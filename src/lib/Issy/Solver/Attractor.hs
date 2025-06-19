---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Attractor
-- Description : Implementation of top-level attractor computation
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.Attractor
  ( SolSt(..)
  , attractor
  , attractorEx
  , noCheck
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad (filterM)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, accelerate, enforcementSummaries, generateProgram, setName)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration (accelReach, canAccel)
import Issy.Solver.EnforcementSummaries (EnfSt, trySummary)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Statistics (Stats)
import qualified Issy.Statistics as Stats
import Issy.Utils.Logging
import Issy.Utils.OpenList (OpenList)
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- Solver State
--  TODO: maybe move somewhere else, e.g. own module?
---------------------------------------------------------------------------------------------------
data SolSt = SolSt
  { stats :: Stats
  , enfst :: EnfSt
  }

---------------------------------------------------------------------------------------------------
type StopCheck = Maybe (Loc -> SymSt -> IO Bool)

noCheck :: StopCheck
noCheck = Nothing

---------------------------------------------------------------------------------------------------
-- | 'attractor' compute the attractor for a given player, game, and symbolic state
attractor :: Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt)
attractor cfg solst player arena stopCheck target = do
  cfg <- pure $ setName "Attr" $ cfg {generateProgram = False}
  (res, solst, _) <- attractorFull cfg solst player arena stopCheck target
  pure (res, solst)

---------------------------------------------------------------------------------------------------
-- | 'attractorEx' compute the attractor for a given player, game, and symbolic state and does 
-- program extraction if indicated in the 'Config'.
attractorEx :: Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt, SyBo)
attractorEx cfg solst player arena stopCheck target = do
  cfg <-
    pure
      $ if generateProgram cfg
          then setName "AttrE" cfg
          else setName "Attr " cfg
  attractorFull cfg solst player arena stopCheck target

---------------------------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used for the different
-- type of attractor computations (with/without extraction)
attractorFull :: Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt, SyBo)
attractorFull cfg solst player arena stopCheck target = do
  satLocs <- Set.fromList . map fst <$> filterM (SMT.sat cfg . snd) (SymSt.toList target)
  lg cfg ["Attractor for", show player, "from", strLocs satLocs, "to reach", strStA target]
  let prog = Synt.returnOn target $ Synt.normSyBo cfg arena
  (res, solst, prog) <- attr solst (noVisits arena) (OL.fromSet (predSet arena satLocs)) target prog
  lg cfg ["Result", strStA res]
  return (res, solst, prog)
  where
    attr :: SolSt -> VisitCounter -> OpenList Loc -> SymSt -> SyBo -> IO (SymSt, SolSt, SyBo)
    attr solst vcnt open reach prog =
      case OL.pop open of
        Nothing -> pure (reach, solst, prog)
        Just (l, open) -> do
          stop <- fromMaybe (\_ _ -> pure False) stopCheck l reach
          if stop
            then pure (reach, solst, prog)
            else attrStep solst vcnt open reach prog l
    --
    attrStep ::
         SolSt -> VisitCounter -> OpenList Loc -> SymSt -> SyBo -> Loc -> IO (SymSt, SolSt, SyBo)
    attrStep solst vcnt open reach prog l = do
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
        then attr solst vcnt open reach prog
        else do
          prog <- pure $ Synt.enforceTo l new reach prog
          reach <- pure $ set reach l new
          open <- pure $ preds arena l `OL.push` open
              -- Check if we accelerate
          if accelerate cfg && canAccel arena l && accelNow l old vcnt
                  -- Acceleration
            then accelSum solst vcnt open reach prog l
            else attr solst vcnt open reach prog
    -- Acceleration or summary application
    accelSum ::
         SolSt -> VisitCounter -> OpenList Loc -> SymSt -> SyBo -> Loc -> IO (SymSt, SolSt, SyBo)
    accelSum solst vcnt open reach prog l
      | enforcementSummaries cfg = do
        (enfst', msum) <- trySummary cfg player arena l (enfst solst) reach
        solst <- pure $ solst {enfst = enfst'}
        case msum of
                -- Summary was not found and could not be computed either
          Nothing -> accel solst vcnt open reach prog l
          Just (sum, subProg) -> do
                        -- TODO: use programm
                        -- TODO: add QELIM stepp
                        -- If the summary does not add new stuff we do not accelerate
            extended <- SMT.sat cfg $ FOL.andf [sum, FOL.neg (get reach l)]
            if extended
              then do
                new <- SMT.simplify cfg $ FOL.orf [get reach l, sum]
                attr solst vcnt open (set reach l new) prog
              else accel solst vcnt open reach prog l
      | otherwise = accel solst vcnt open reach prog l
    -- Acceleration
    accel ::
         SolSt -> VisitCounter -> OpenList Loc -> SymSt -> SyBo -> Loc -> IO (SymSt, SolSt, SyBo)
    accel solst vcnt open reach prog l = do
      lg cfg ["Attempt reachability acceleration"]
      (acc, progSub) <- accelReach cfg (visits l vcnt) player arena l reach
      solst <- pure $ solst {stats = Stats.accel (stats solst)}
      lg cfg ["Accleration formula", SMTLib.toString acc]
      res <- SMT.simplify cfg $ FOL.orf [get reach l, acc]
      succ <- not <$> SMT.valid cfg (res `FOL.impl` get reach l)
      lg cfg ["Accelerated:", show succ]
      if succ
                      -- Acceleration succeed
        then do
          solst <- pure $ solst {stats = Stats.accelSucc (stats solst)}
          prog <- pure $ Synt.callOn l acc progSub prog
          attr solst vcnt open (set reach l res) prog
        else attr solst vcnt open reach prog
    -- Logging helper
    strLocs = strS (locName arena)
    strStA = strSt arena

---------------------------------------------------------------------------------------------------
-- Heuristics
---------------------------------------------------------------------------------------------------
accelNow :: Loc -> Term -> VisitCounter -> Bool
accelNow l f vcnt = (f /= FOL.false) && visits2accel (visits l vcnt)

accelerationDist :: Int
accelerationDist = 4

visits2accel :: Int -> Bool
visits2accel k = (k >= accelerationDist) && (k `mod` accelerationDist == 0)
---------------------------------------------------------------------------------------------------
