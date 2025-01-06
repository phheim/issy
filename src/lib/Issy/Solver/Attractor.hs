-------------------------------------------------------------------------------
module Issy.Solver.Attractor
  ( attractor
  , attractorEx
  ) where

-------------------------------------------------------------------------------
import Control.Monad (filterM)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, accelerate, generateProgram, setName)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.SMT (sat, simplify, valid)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Acceleration (accelReach)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Solver.Heuristics (visits2accel)
import Issy.Utils.Logging
import Issy.Utils.OpenList (OpenList, pop, push)
import qualified Issy.Utils.OpenList as OL (fromSet)

-------------------------------------------------------------------------------
-- | 'attractor' compute the attractor for a given player, game, and symbolic
-- state
attractor :: Config -> Ply -> Game -> SymSt -> IO SymSt
attractor ctx p g target = do
  ctx <- pure $ setName "Attr" $ ctx {generateProgram = False}
  fst <$> attractorFull ctx p g target

-------------------------------------------------------------------------------
-- | 'attractorEx' compute the attractor for a given player, game, and symbolic
-- state and does program extraction if indicated in the 'Config'.
attractorEx :: Config -> Ply -> Game -> SymSt -> IO (SymSt, CFG)
attractorEx ctx p g target = do
  ctx <-
    pure
      $ if generateProgram ctx
          then setName "AttrE" ctx
          else setName "Attr" ctx
  attractorFull ctx p g target

-------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used
-- for the different type of attractor computations (with/without extraction)
--
attractorFull :: Config -> Ply -> Game -> SymSt -> IO (SymSt, CFG)
attractorFull ctx p g target = do
  satLocs <- Set.fromList . map fst <$> filterM (sat ctx . snd) (SymSt.toList target)
  lg ctx ["Attractor for", show p, "from", strS (locName g) satLocs, "to reach", strSt g target]
  (res, cfg) <- attr (noVisits g) (OL.fromSet (predSet g satLocs)) target (CFG.goalCFG target)
  lg ctx ["Result", strSt g res]
  return (res, cfg)
  where
    attr :: VisitCounter -> OpenList Loc -> SymSt -> CFG -> IO (SymSt, CFG)
    attr vcnt open reach cfg =
      case pop open of
        Nothing -> return (reach, cfg)
        Just (l, open) -> do
          vcnt <- pure $ visit l vcnt
          let old = reach `get` l
          lg ctx ["Step in", locName g l, "with", smtLib2 old]
          -- Enforcable predecessor step
          new <- simplify ctx $ FOL.orf [cpre p g reach l, old]
          lg ctx ["Compute new", smtLib2 new]
          -- Check if this changed something in this location
          unchanged <- valid ctx $ new `FOL.impl` old
          lg ctx ["which has changed?", show (not unchanged)]
          if unchanged
            then attr vcnt open reach cfg
            else do
              cfg <- extr $ CFG.addUpd reach g l cfg
              cfg <- simpCFG cfg
              reach <- pure $ set reach l new
              open <- pure $ preds g l `push` open
              -- Check if we accelerate
              if accelerate ctx && canAccel g l && accelNow l old vcnt
                  -- Acceleration
                then do
                  lg ctx ["Attempt reachability acceleration"]
                  (acc, cfgSub) <- accelReach ctx (visits l vcnt) p g l reach
                  lg ctx ["Accleration formula", smtLib2 acc]
                  res <- simplify ctx $ FOL.orf [new, acc]
                  succ <- not <$> valid ctx (res `FOL.impl` new)
                  lg ctx ["Accelerated:", show succ]
                  if succ
                      -- Acceleration succeed
                    then do
                      cfg <- extr $ CFG.integrate cfgSub cfg
                      cfg <- simpCFG cfg
                      attr vcnt open (set reach l res) cfg
                    else attr vcnt open reach cfg
                else attr vcnt open reach cfg
      where
        extr cfg
          | generateProgram ctx = pure cfg
          | otherwise = pure CFG.empty
        simpCFG cfg
          | generateProgram ctx = CFG.simplify ctx cfg
          | otherwise = pure cfg

canAccel :: Game -> Loc -> Bool
canAccel g l =
  any (\v -> FOL.isNumber (sortOf g v) && not (boundedVar g v)) (stateVars g) && (g `cyclicIn` l)

-------------------------------------------------------------------------------
-- Heuristics
-------------------------------------------------------------------------------
accelNow :: Loc -> Term -> VisitCounter -> Bool
accelNow l f vcnt = (f /= FOL.false) && visits2accel (visits l vcnt)
-------------------------------------------------------------------------------
