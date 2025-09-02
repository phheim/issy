{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration.UFLAcceleration
  ( accelReach
  ) where

import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (extendAcceleration)
import Issy.Logic.FOL (Term(Func, Lambda, Quant, Var))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.Acceleration.LemmaFinding (Constraint, LemSyms(..), Lemma(..), resolve)
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

-------------------------------------------------------------------------------
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "UinAc" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  lg conf ["Depth bound", show (H.nestingDepth heur)]
  let acst = accState conf heur player arena
  (cons, f, prog, acst) <- accReach acst arena loc reach
  cons <- pure $ cons ++ [Vars.existsX (vars arena) (FOL.andf [f, FOL.neg (reach `get` loc)])]
  unless (all (null . FOL.frees) cons)
    $ error
    $ "assert: constraint with free variables " ++ strL (strS show . FOL.frees) cons
  (res, lemmaAssign) <- resolve conf heur (vars arena) cons f (lemmaSyms acst)
  prog <- pure $ foldl (replaceLemma (vars arena)) prog lemmaAssign
  lg conf ["Acceleration resulted in", SMTLib.toString res]
  return (res, prog)

-------------------------------------------------------------------------------
-- IterA and accReach
-------------------------------------------------------------------------------
data AccState = AccState
  { player :: Player
  , depth :: Int
  , config :: Config
  , heur :: Heur
  , usedSyms :: Set Symbol
  , lemmaSyms :: [LemSyms]
  , visitCounters :: [VisitCounter]
  }

accState :: Config -> Heur -> Player -> Arena -> AccState
accState cfg heur ply arena =
  AccState
    { config = cfg
    , player = ply
    , heur = heur
    , depth = 0
    , usedSyms = usedSymbols arena
    , lemmaSyms = []
    , visitCounters = []
    }

unnest :: AccState -> Loc -> AccState
unnest acst = doVisit $ acst {visitCounters = tail (visitCounters acst), depth = depth acst - 1}

nest :: Loc -> AccState -> Bool
nest l acst =
  extendAcceleration (config acst)
    && (depth acst - 1 > H.nestingDepth (heur acst))
    && (H.iterAMaxCPres (heur acst) == visits l (head (visitCounters acst)))

visiting :: Loc -> AccState -> Bool
visiting l acst = H.iterAMaxCPres (heur acst) > visits l (head (visitCounters acst))

doVisit :: AccState -> Loc -> AccState
doVisit acst l =
  acst {visitCounters = visit l (head (visitCounters acst)) : tail (visitCounters acst)}

doIterA :: AccState -> Arena -> AccState
doIterA acst arena =
  acst {visitCounters = noVisits arena : visitCounters acst, depth = depth acst + 1}

accReach :: AccState -> Arena -> Loc -> SymSt -> IO (Constraint, Term, SyBo, AccState)
accReach acst g loc st = do
  let targetInv = dom g loc
  -- Compute new lemma symbols
  (base, step, conc, stepSym, prime, acst) <- pure $ lemmaSymbols (vars g) acst
  -- Compute loop scenario
  (gl, loc, loc', st, fixedInv, prog) <- loopScenario (config acst) (heur acst) g loc st prime
  -- Finialize loop game target with step relation and compute loop attractor
  let st' = set st loc' $ FOL.orf [st `get` loc, step]
  (cons, stAcc, prog, acst) <- iterA acst gl st' loc' prog
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
  pure (cons, FOL.andf [conc, fixedInv], prog, acst)

iterA :: AccState -> Arena -> SymSt -> Loc -> SyBo -> IO (Constraint, SymSt, SyBo, AccState)
iterA acst g attr shadow = go (doIterA acst g) (OL.fromSet (preds g shadow)) [] attr
  where
    go acst open cons attr prog =
      case OL.pop open of
        Nothing -> pure (cons, attr, prog, acst)
        Just (l, open)
          -- Normal IterA update
          | visiting l acst -> do
            open <- pure $ preds g l `OL.push` open
            let new = cpre (player acst) g attr l
            prog <- pure $ Synt.enforceTo l new attr prog
            attr <- pure $ SymSt.disj attr l new
            go (doVisit acst l) open cons attr prog
          -- Nested IterA update
          | nest l acst -> do
            (consA, fA, subProg, acst) <- accReach acst g l attr
            open <- pure $ preds g l `OL.push` open
            cons <- pure $ cons ++ consA
            attr <- pure $ set attr l $ FOL.orf [fA, attr `get` l]
            prog <- pure $ Synt.callOn l fA subProg prog
            go (unnest acst l) open cons attr prog
          -- Do nothing
          | otherwise -> go acst open cons attr prog

-------------------------------------------------------------------------------
-- Symbol Management
-------------------------------------------------------------------------------
lemmaSymbols :: Variables -> AccState -> (Term, Term, Term, Function, Symbol, AccState)
lemmaSymbols vars acst =
  let base = FOL.uniqueName "b" $ usedSyms acst
      step = FOL.uniqueName "s" $ usedSyms acst
      conc = FOL.uniqueName "c" $ usedSyms acst
      prime = FOL.uniquePrefix "prime_" $ usedSyms acst
      lsym = LemSyms base step conc prime
   in ( Vars.unintPredTerm vars base
      , Vars.unintPredTerm vars step
      , Vars.unintPredTerm vars conc
      , Vars.unintPred vars step
      , prime
      , acst
          { usedSyms = usedSyms acst `Set.union` Set.fromList [base, step, conc, prime]
          , lemmaSyms = lsym : lemmaSyms acst
          })

replaceLemma :: Variables -> SyBo -> (LemSyms, Lemma) -> SyBo
replaceLemma vars sybo (LemSyms bs ss cs prime, Lemma b s c) =
  let vs = Vars.stateVarL vars
   in Synt.replaceUF ss (vs ++ map (prime ++) vs) s
        $ Synt.replaceUF cs vs c
        $ Synt.replaceUF bs vs b sybo

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
