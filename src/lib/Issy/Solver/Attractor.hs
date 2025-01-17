-------------------------------------------------------------------------------
module Issy.Solver.Attractor
  ( attractor
  , attractorEx
  , noCheck
  ) where

-------------------------------------------------------------------------------
import Control.Monad (filterM)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, accelerate, generateProgram, setName)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration (accelReach, canAccel)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Statistics (Stats)
import qualified Issy.Statistics as Stats
import Issy.Utils.Logging
import Issy.Utils.OpenList (OpenList)
import qualified Issy.Utils.OpenList as OL

-------------------------------------------------------------------------------
type StopCheck = Maybe (Loc -> SymSt -> IO Bool)

noCheck :: StopCheck
noCheck = Nothing

-------------------------------------------------------------------------------
-- | 'attractor' compute the attractor for a given player, game, and symbolic
-- state
attractor :: Config -> Stats -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, Stats)
attractor cfg stats player arena stopCheck target = do
  cfg <- pure $ setName "Attr" $ cfg {generateProgram = False}
  (res, stats, _) <- attractorFull cfg stats player arena stopCheck target
  pure (res, stats)

-------------------------------------------------------------------------------
-- | 'attractorEx' compute the attractor for a given player, game, and symbolic
-- state and does program extraction if indicated in the 'Config'.
attractorEx :: Config -> Stats -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, Stats, SyBo)
attractorEx cfg stats player arena stopCheck target = do
  cfg <-
    pure
      $ if generateProgram cfg
          then setName "AttrE" cfg
          else setName "Attr " cfg
  attractorFull cfg stats player arena stopCheck target

-------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used
-- for the different type of attractor computations (with/without extraction)
--
attractorFull :: Config -> Stats -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, Stats, SyBo)
attractorFull cfg stats player arena stopCheck target = do
  satLocs <- Set.fromList . map fst <$> filterM (SMT.sat cfg . snd) (SymSt.toList target)
  lg cfg ["Attractor for", show player, "from", strLocs satLocs, "to reach", strStA target]
  let prog = Synt.returnOn target $ Synt.normSyBo cfg arena
  (res, stats, prog) <- attr stats (noVisits arena) (OL.fromSet (predSet arena satLocs)) target prog
  lg cfg ["Result", strStA res]
  return (res, stats, prog)
  where
    attr :: Stats -> VisitCounter -> OpenList Loc -> SymSt -> SyBo -> IO (SymSt, Stats, SyBo)
    attr stats vcnt open reach prog =
      case OL.pop open of
        Nothing -> pure (reach, stats, prog)
        Just (l, open) -> do
          stop <- fromMaybe (\_ _ -> pure False) stopCheck l reach
          if stop
            then pure (reach, stats, prog)
            else attrStep stats vcnt open reach prog l
    --
    attrStep ::
         Stats -> VisitCounter -> OpenList Loc -> SymSt -> SyBo -> Loc -> IO (SymSt, Stats, SyBo)
    attrStep stats vcnt open reach prog l = do
      vcnt <- pure $ visit l vcnt
      let old = reach `get` l
      lgd cfg ["Step in", locName arena l, "with", SMTLib.toString old]
          -- Enforcable predecessor step
      new <- SMT.simplify cfg $ FOL.orf [cpre player arena reach l, old]
      lgd cfg ["Compute new", SMTLib.toString new]
          -- Check if this changed something in this location
      unchanged <- SMT.valid cfg $ new `FOL.impl` old
      lgd cfg ["which has changed?", show (not unchanged)]
      if unchanged
        then attr stats vcnt open reach prog
        else do
          prog <- pure $ Synt.enforceTo l new reach prog
          reach <- pure $ set reach l new
          open <- pure $ preds arena l `OL.push` open
              -- Check if we accelerate
          if accelerate cfg && canAccel arena l && accelNow l old vcnt
                  -- Acceleration
            then do
              lg cfg ["Attempt reachability acceleration"]
              (acc, progSub) <- accelReach cfg (visits l vcnt) player arena l reach
              stats <- pure $ Stats.accel stats
              lg cfg ["Accleration formula", SMTLib.toString acc]
              res <- SMT.simplify cfg $ FOL.orf [new, acc]
              succ <- not <$> SMT.valid cfg (res `FOL.impl` new)
              lg cfg ["Accelerated:", show succ]
              if succ
                      -- Acceleration succeed
                then do
                  stats <- pure $ Stats.accelSucc stats
                  prog <- pure $ Synt.callOn l acc progSub prog
                  attr stats vcnt open (set reach l res) prog
                else attr stats vcnt open reach prog
            else attr stats vcnt open reach prog
    -- Logging helper
    strLocs = strS (locName arena)
    strStA = strSt arena

-------------------------------------------------------------------------------
-- Heuristics
-------------------------------------------------------------------------------
accelNow :: Loc -> Term -> VisitCounter -> Bool
accelNow l f vcnt = (f /= FOL.false) && visits2accel (visits l vcnt)

accelerationDist :: Int
accelerationDist = 4

visits2accel :: Int -> Bool
visits2accel k = (k >= accelerationDist) && (k `mod` accelerationDist == 0)
-------------------------------------------------------------------------------
