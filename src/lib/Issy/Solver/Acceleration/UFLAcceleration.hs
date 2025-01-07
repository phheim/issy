{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration.UFLAcceleration
  ( accelReach
  ) where

import Control.Monad (unless)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, nestAcceleration, setName)
import Issy.Logic.FOL (Function, Symbol, Term(Func, Lambda, Quant, Var))
import qualified Issy.Logic.FOL as FOL
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Acceleration.Heuristics
import Issy.Solver.Acceleration.LemmaFinding (Constraint, LemSyms(..), replaceLemma, resolve)
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

-------------------------------------------------------------------------------
accelReach :: Config -> Int -> Player -> Game -> Loc -> SymSt -> IO (Term, CFG)
accelReach ctx limit p g l st = do
  ctx <- pure $ setName "AccReach" ctx
  lg ctx ["Accelerate in", locName g l, "on", strSt g st]
  lg ctx ["Depth bound", show (limit2depth limit)]
  lg ctx ["Size bound", show (limit2size limit)]
  let acst = accState ctx limit p g
  (cons, f, cfg, acst) <- accReach acst g l st
  cons <- pure $ cons ++ [Vars.existsX (vars g) (FOL.andf [f, FOL.neg (st `get` l)])]
  unless (all (null . FOL.frees) cons)
    $ error
    $ "assert: constraint with free variables " ++ strL (strS show . FOL.frees) cons
  (res, col) <- resolve ctx limit (vars g) cons f (lemmaSyms acst)
  cfg <- pure $ foldl (flip (\(l, li) -> CFG.mapCFG (replaceLemma (vars g) li l))) cfg col
  cfg <- pure $ CFG.setLemmas (Vars.stateVarL (vars g)) col cfg
  lg ctx ["Acceleration resulted in", smtLib2 res]
  return (res, cfg)

-------------------------------------------------------------------------------
-- IterA and accReach
-------------------------------------------------------------------------------
data AccState = AccState
  { player :: Player
  , limit :: Int
  , depth :: Int
  , config :: Config
  , usedSyms :: Set Symbol
  , lemmaSyms :: [LemSyms]
  , visitCounters :: [VisitCounter]
  }

accState :: Config -> Int -> Player -> Game -> AccState
accState cfg limit ply arena =
  AccState
    { config = cfg
    , player = ply
    , limit = limit
    , depth = 0
    , usedSyms = usedSymbols arena
    , lemmaSyms = []
    , visitCounters = []
    }

sizeLimit :: AccState -> Maybe Int
sizeLimit = Just . limit2size . limit

unnest :: AccState -> Loc -> AccState
unnest acst = doVisit $ acst {visitCounters = tail (visitCounters acst), depth = depth acst - 1}

nest :: Loc -> AccState -> Bool
nest l acst =
  nestAcceleration (config acst)
    && (depth acst - 1 > limit2depth (limit acst))
    && (visitingThreshold == visits l (head (visitCounters acst)))

visiting :: Loc -> AccState -> Bool
visiting l = (< visitingThreshold) . visits l . head . visitCounters

doVisit :: AccState -> Loc -> AccState
doVisit acst l =
  acst {visitCounters = visit l (head (visitCounters acst)) : tail (visitCounters acst)}

doIterA :: AccState -> Game -> AccState
doIterA acst arena =
  acst {visitCounters = noVisits arena : visitCounters acst, depth = depth acst + 1}

accReach :: AccState -> Game -> Loc -> SymSt -> IO (Constraint, Term, CFG, AccState)
accReach acst g loc st = do
  let targetInv = g `inv` loc
  -- Compute loop scenario
  (gl, loc, loc', st, fixedInv) <- loopScenario (config acst) (sizeLimit acst) g loc st
  -- Compute new lemma symbols
  (base, step, conc, lsym, stepSym, acst) <- pure $ lemmaSymbols (vars g) acst
  -- Initialize loop-program
  cfg <- pure $ CFG.loopCFG (loc, loc') st lsym step
  -- Finialize loop game target with step relation and compute loop attractor
  let st' = set st loc' $ FOL.orf [st `get` loc, step]
  (cons, stAcc, cfg, acst) <- iterA acst gl st' loc' cfg
  -- Derive constraints
  let quantSub f = Vars.forallX (vars g) $ FOL.andf [targetInv, conc] `FOL.impl` f
  cons <- pure $ map (expandStep (vars g) stepSym) cons
  stAcc <- pure $ SymSt.map (expandStep (vars g) stepSym) stAcc
  cons <-
    pure
      [ Vars.forallX (vars g) $ FOL.andf [targetInv, base] `FOL.impl` (st `get` loc)
      , quantSub (stAcc `get` loc)
      , quantSub (FOL.andf cons)
      ]
  pure (cons, FOL.andf [conc, fixedInv], cfg, acst)

iterA :: AccState -> Game -> SymSt -> Loc -> CFG -> IO (Constraint, SymSt, CFG, AccState)
iterA acst g attr shadow = go (doIterA acst g) (OL.fromSet (preds g shadow)) [] attr
  where
    go acst open cons attr cfgl =
      case OL.pop open of
        Nothing -> pure (cons, attr, cfgl, acst)
        Just (l, open)
          -- Normal IterA update
          | visiting l acst -> do
            open <- pure $ preds g l `OL.push` open
            cfgl <- pure $ CFG.addUpd attr g l cfgl
            attr <- pure $ SymSt.disj attr l $ cpre (player acst) g attr l
            go (doVisit acst l) open cons attr cfgl
          -- Nested IterA update
          | nest l acst -> do
            (consA, fA, cfgSub, acst) <- accReach acst g l attr
            open <- pure $ preds g l `OL.push` open
            cons <- pure $ cons ++ consA
            attr <- pure $ set attr l $ FOL.orf [fA, attr `get` l]
            cfgl <- pure $ CFG.integrate cfgSub cfgl
            go (unnest acst l) open cons attr cfgl
          -- Do nothing
          | otherwise -> go acst open cons attr cfgl

-------------------------------------------------------------------------------
-- Symbol Management
-------------------------------------------------------------------------------
lemmaSymbols :: Variables -> AccState -> (Term, Term, Term, LemSyms, Function, AccState)
lemmaSymbols vars acst =
  let base = FOL.uniqueName "b" $ usedSyms acst
      step = FOL.uniqueName "s" $ usedSyms acst
      conc = FOL.uniqueName "c" $ usedSyms acst
      lsym = LemSyms base step conc
   in ( Vars.unintPredTerm vars base
      , Vars.unintPredTerm vars step
      , Vars.unintPredTerm vars conc
      , lsym
      , Vars.unintPred vars step
      , acst
          { usedSyms = usedSyms acst `Set.union` Set.fromList [base, step, conc]
          , lemmaSyms = lsym : lemmaSyms acst
          })

--
-- Step relation [EX ++ CELLS]
-- Other relations [CELLS]
-- 
expandStep :: Variables -> Function -> Term -> Term
expandStep vars func = go
  where
    go =
      \case
        Quant q s t -> Quant q s $ go t
        Lambda s t -> Lambda s $ go t
        Func f args
          | f == func -> Func f $ [Var v (Vars.sortOf vars v) | v <- Vars.stateVarL vars] ++ args
          | otherwise -> Func f $ map go args
        atom -> atom
-------------------------------------------------------------------------------
