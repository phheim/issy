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
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
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
attractor :: Config -> Player -> Arena -> StopCheck -> SymSt -> IO SymSt
attractor cfg player arena stopCheck target = do
  cfg <- pure $ setName "Attr" $ cfg {generateProgram = False}
  fst <$> attractorFull cfg player arena stopCheck target

-------------------------------------------------------------------------------
-- | 'attractorEx' compute the attractor for a given player, game, and symbolic
-- state and does program extraction if indicated in the 'Config'.
attractorEx :: Config -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, CFG)
attractorEx cfg player arena stopCheck target = do
  cfg <-
    pure
      $ if generateProgram cfg
          then setName "AttrE" cfg
          else setName "Attr" cfg
  attractorFull cfg player arena stopCheck target

-------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used
-- for the different type of attractor computations (with/without extraction)
--
attractorFull :: Config -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, CFG)
attractorFull cfg player arena stopCheck target = do
  satLocs <- Set.fromList . map fst <$> filterM (SMT.sat cfg . snd) (SymSt.toList target)
  lg cfg ["Attractor for", show player, "from", strLocs satLocs, "to reach", strStA target]
  (res, prog) <-
    attr (noVisits arena) (OL.fromSet (predSet arena satLocs)) target (CFG.goalCFG target)
  lg cfg ["Result", strStA res]
  return (res, prog)
  where
    attr :: VisitCounter -> OpenList Loc -> SymSt -> CFG -> IO (SymSt, CFG)
    attr vcnt open reach prog =
      case OL.pop open of
        Nothing -> pure (reach, prog)
        Just (l, open) -> do
          stop <- fromMaybe (\_ _ -> pure False) stopCheck l reach
          if stop
            then pure (reach, prog)
            else attrStep vcnt open reach prog l
    --
    attrStep :: VisitCounter -> OpenList Loc -> SymSt -> CFG -> Loc -> IO (SymSt, CFG)
    attrStep vcnt open reach prog l = do
      vcnt <- pure $ visit l vcnt
      let old = reach `get` l
      lg cfg ["Step in", locName arena l, "with", SMTLib.toString old]
          -- Enforcable predecessor step
      new <- SMT.simplifyHeavy cfg $ FOL.orf [cpre player arena reach l, old]
      lg cfg ["Compute new", SMTLib.toString new]
          -- Check if this changed something in this location
      unchanged <- SMT.valid cfg $ new `FOL.impl` old
      lg cfg ["which has changed?", show (not unchanged)]
      if unchanged
        then attr vcnt open reach prog
        else do
          prog <- extr $ CFG.addUpd reach arena l prog
          prog <- simpCFG prog
          reach <- pure $ set reach l new
          open <- pure $ preds arena l `OL.push` open
              -- Check if we accelerate
          if accelerate cfg && canAccel arena l && accelNow l old vcnt
                  -- Acceleration
            then do
              lg cfg ["Attempt reachability acceleration"]
              (acc, progSub) <- accelReach cfg (visits l vcnt) player arena l reach
              lg cfg ["Accleration formula", SMTLib.toString acc]
              res <- SMT.simplify cfg $ FOL.orf [new, acc]
              succ <- not <$> SMT.valid cfg (res `FOL.impl` new)
              lg cfg ["Accelerated:", show succ]
              if succ
                      -- Acceleration succeed
                then do
                  prog <- extr $ CFG.integrate progSub prog
                  prog <- simpCFG prog
                  attr vcnt open (set reach l res) prog
                else attr vcnt open reach prog
            else attr vcnt open reach prog
    -- Logging helper
    strLocs = strS (locName arena)
    strStA = strSt arena
    -- Extraction helpers
    extr prog
      | generateProgram cfg = pure prog
      | otherwise = pure CFG.empty
    simpCFG prog
      | generateProgram cfg = CFG.simplify cfg prog
      | otherwise = pure prog

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
