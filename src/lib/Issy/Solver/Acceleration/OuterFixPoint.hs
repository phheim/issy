---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Acceleration.OuterFixPoint
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration.OuterFixPoint
  ( accelCoBuechi
  ) where

import qualified Data.Map.Strict as Map
import Issy.Prelude

import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import Issy.Printers.SMTLib as SMTLib
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.Acceleration.LemmaFinding (LemSyms(..), Lemma(..), resolve)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt

accelCoBuechi :: Config -> Player -> Arena -> Loc -> SymSt -> SymSt -> IO (Term, SyBo)
accelCoBuechi conf player arena loc fset wopp = do
  conf <- pure $ setName "BueAc" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena fset]
  let (base, step, conc, stepFun, prime, lsym) = lemmaSymbols arena
  (arena, loc') <- pure $ loopArena arena loc
  fset <- pure $ SymSt.set (extendSt fset Just arena) loc' $ FOL.neg step
  wopp <- pure $ extendSt wopp Just arena
  let idMap = Map.fromSet id (locations arena)
  let stratO = Synt.returnOn wopp $ Synt.loopSyBo conf arena loc loc' prime idMap
  (constrRec, rec, stratO) <- pure $ iterB conf arena player fset wopp stratO
  constrRec <- pure $ expandStep (vars arena) stepFun constrRec
  rec <- pure $ SymSt.map (expandStep (vars arena) stepFun) rec
  -- Base condition
  let baseCond =
        Vars.forallX (vars arena) $ FOL.impl (FOL.andf [dom arena loc, base]) $ get wopp loc
  let stepCond =
        Vars.forallX (vars arena)
          $ FOL.impl (FOL.andf [dom arena loc, base, get fset loc])
          $ FOL.andf [constrRec, get rec loc]
  let progress = Vars.existsX (vars arena) $ FOL.andf [conc, FOL.neg (get wopp loc)]
  let constr = [baseCond, stepCond, progress]
  unless (all (null . FOL.frees) constr) $ error "assert: constraint with free variables"
  (conc, lemmaAssign) <- resolve conf (H.simple conf arena) (vars arena) constr conc [lsym]
  lg conf ["Accelerated with", SMTLib.toString conc]
  stratO <- pure $ foldl (replaceLemma (vars arena)) stratO lemmaAssign
  pure (conc, stratO)

-- Add stuff to co-Buechi player
iterB :: Config -> Arena -> Player -> SymSt -> SymSt -> SyBo -> (Term, SymSt, SyBo)
iterB conf arena player fset wopp = go 0 FOL.true wopp
  where
    go cnt constr wopp stratO
      | cnt >= outerFPIterBBound = (constr, wopp, stratO)
      | otherwise =
        let (d, _) = iterA conf player arena (SymSt.disjS fset wopp)
            constr' = FOL.andf [constr, precise player arena d]
            cannotEnforceD = SymSt.map FOL.neg $ cpreS player arena d
            (wopp', stratOSub) = iterA conf (opponent player) arena cannotEnforceD
            stratO' = Synt.callOnSt wopp' stratOSub $ Synt.enforceFromTo cannotEnforceD wopp stratO
         in go (cnt + 1) constr' wopp' stratO'

precise :: Player -> Arena -> SymSt -> Term
precise player arena d =
  FOL.andfL (locationL arena) $ \l -> FOL.impl (cpre player arena d l) $ get d l

iterA :: Config -> Player -> Arena -> SymSt -> (SymSt, SyBo)
iterA conf player arena attr = go 0 attr $ Synt.returnOn attr $ Synt.normSyBo conf arena
  where
    go cnt attr sybo
      | cnt >= outerFPIterABound = (attr, sybo)
      | otherwise =
        let attr' = cpreS player arena attr
            sybo' = Synt.enforceFromTo attr attr' sybo
         in go (cnt + 1) attr' sybo'

--
-- Symbol Management
--
lemmaSymbols :: Arena -> (Term, Term, Term, Function, Symbol, LemSyms)
lemmaSymbols arena =
  let syms = usedSymbols arena
      base = FOL.uniquePrefix "base" syms
      step = FOL.uniqueName "step" syms
      conc = FOL.uniqueName "conc" syms
      prime = FOL.uniquePrefix "prime_" syms
   in ( Vars.unintPredTerm (vars arena) base
      , Vars.unintPredTerm (vars arena) step
      , Vars.unintPredTerm (vars arena) conc
      , Vars.unintPred (vars arena) step
      , prime
      , LemSyms base step conc prime)

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
        FOL.Quant q s t -> FOL.Quant q s $ go t
        FOL.Lambda s t -> FOL.Lambda s $ go t
        FOL.Func f args
          | f == func -> FOL.Func f $ [Vars.mk vars v | v <- Vars.stateVarL vars] ++ args
          | otherwise -> FOL.Func f $ map go args
        atom -> atom

--
-- "Heuristics"
--
outerFPIterABound :: Int
outerFPIterABound = 2

outerFPIterBBound :: Int
outerFPIterBBound = 2
---------------------------------------------------------------------------------------------------
