---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Logic.Reasoning
-- Description : More complex algorithms for logic reasoning
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
-- This module contains more complex algorithms to reason on logic which go
-- beyond simple normalisation operations but are not part of any other modules 
-- like reasoning on polyhedra or intervals.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Reasoning
  ( skolemize
  , equalitiesFor
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Config (Config, setName)
import Issy.Logic.FOL (Function(..), Sort, Symbol, Term(..))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Utils.Extra (justOn)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- | 'skolemize' computes for a set of variables V and 'Term's t and pre 
-- skolem functions for F_v for all v in V, such that the folllowing holds:
--
--  forall (FreeVars(t) \ V). pre(FreeVars(t) \ V) -> t[v -> F_v]
--
-- The usual scenario is that pre := exists V. t.
-- Both 'Term's should be free of uninterpreted functions.
skolemize :: Config -> [(Symbol, Sort)] -> Term -> Term -> IO (Map Symbol Term)
skolemize conf vars pre term
  | any isSkolem (FOL.frees pre) = error "assert: precondition should not have skolem variables"
  | not (any isSkolem (FOL.frees term)) = pure Map.empty
  | otherwise = do
    conf <- pure $ setName "Skolemize" conf
    lgd conf ["Skolem vars", strL fst vars]
    lgd conf ["Precondition", SMTLib.toString pre]
    lgd conf ["Term", SMTLib.toString term]
    pre <- SMT.simplify conf pre
    term <- SMT.simplify conf term
    (term, skolemEqs) <- eqElim conf vars pre term
    skolemDirs <- skolemDirect conf vars pre term
    pure $ Map.fromList $ skolemEqs ++ skolemDirs
  where
    isSkolem v = any ((v ==) . fst) vars

skolemDirect :: Config -> [(Symbol, Sort)] -> Term -> Term -> IO [(Symbol, Term)]
skolemDirect conf vars pre term
  | null freeSkolems = pure []
  | otherwise = do
    lgd conf ["Skolemize with SMT on", strL fst freeSkolems]
    let termSkolem = FOL.mapTerm (\v s -> justOn (isSkolem v) (skolem v s)) term
    let f = FOL.impl pre termSkolem
    let query = FOL.pushdownQE $ FOL.forAll (Set.toList (FOL.frees f)) f
    model <- SMT.satModel conf query
    case model of
      Nothing -> error "assert: precondition was not proper"
      Just model -> do
        model <- pure $ FOL.modelToMap model
        lgd conf ["Skolem model", strM id SMTLib.toString model]
        pure $ Map.toList model
  where
    prefix =
      FOL.uniquePrefix "skolem_func_"
        $ FOL.symbols pre `Set.union` FOL.symbols term `Set.union` Set.fromList (map fst vars)
    isSkolem v = any ((v ==) . fst) vars
        --
    freeSkolems = filter ((`elem` FOL.frees term) . fst) vars
        --
    otherVars = filter (not . isSkolem . fst) $ Map.toList $ FOL.bindings $ FOL.impl pre term
    skolem v s = FOL.unintFunc (prefix ++ v) s otherVars

eqElim :: Config -> [(Symbol, Sort)] -> Term -> Term -> IO (Term, [(Symbol, Term)])
eqElim conf vars pre term = go term [] vars
  where
    go term skolems [] = pure (term, skolems)
    go term skolems ((var, sort):vr)
      | var `notElem` FOL.frees term = go term ((var, FOL.var var sort) : skolems) vr
      | otherwise = do
        sk <- tryEqElim conf vars pre term var
        case sk of
          Nothing -> go term skolems vr
          Just sk -> do
            term <- SMT.simplify conf $ FOL.mapTermFor var sk term
            go term ((var, sk) : skolems) vr

-- | try to eliminate skolem  functions based on equalities found in the 
-- condition
tryEqElim :: Config -> [(Symbol, Sort)] -> Term -> Term -> Symbol -> IO (Maybe Term)
tryEqElim conf vars pre term var = do
  let equals = filter (not . any isSkolem . FOL.frees) $ Set.toList $ equalitiesFor var term
  lgd conf ["For", var, "use equalties", strL SMTLib.toString equals]
  res <- go pre equals
  case res of
    Nothing -> lgd conf ["Failed to derive skolem function"]
    Just res -> lgd conf ["Derive skolem function", var, ":=", SMTLib.toString res]
  pure res
  where
    isSkolem v = any ((v ==) . fst) vars
    --
    go pre =
      \case
        [] -> pure Nothing
        eq:eqr -> do
          let condSet = FOL.exists (map fst vars) $ FOL.mapTermFor var eq term
          condSet <- SMT.simplify conf condSet
          satT <- SMT.sat conf condSet
          if satT
            then do
              pre <- SMT.simplify conf $ FOL.andf [pre, FOL.neg condSet]
              satE <- SMT.sat conf pre
              if satE
                then fmap (FOL.ite condSet eq) <$> go pre eqr
                else pure $ Just eq
            else go pre eqr

equalitiesFor :: Symbol -> Term -> Set Term
equalitiesFor var = go
  where
    go =
      \case
        Func FEq [st1, st2]
          | var `elem` FOL.frees st1 && var `elem` FOL.frees st2 -> go st1 `Set.union` go st2 -- While there might be casese like 2x = x + 1 that could also be handled, this should be taken care of by simplification operations
          | var `elem` FOL.frees st2 -> go $ Func FEq [st2, st1]
          | var `elem` FOL.frees st1 ->
            case st1 of
              Var v _
                | v == var -> Set.singleton st2
                | otherwise -> error "assert: this should not be reachable"
              Func FMul [Const c, Var v _]
                | v == var -> Set.singleton $ FOL.multT [Const (FOL.invertC c), st2]
                | otherwise -> error "assert: this should not be reachable"
              Func FAdd [] -> error "assert: this should not be reachable"
              Func FAdd (t:ts)
                | var `elem` FOL.frees t -> go $ Func FEq [t, FOL.minusT [st2, Func FAdd ts]]
                | otherwise -> go $ Func FEq [Func FAdd ts, FOL.minusT [st2, t]]
              _ -> Set.empty
          | otherwise -> Set.empty
        Func _ args -> Set.unions $ map go args
        Quant _ _ f -> go f
        Lambda _ f -> go f
        _ -> Set.empty
---------------------------------------------------------------------------------------------------
