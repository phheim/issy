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

import qualified Data.Map as Map
---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Config (Config)
import Issy.Logic.FOL (Function(..), Sort, Symbol, Term(..))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT

---------------------------------------------------------------------------------------------------
-- | 'skolemize' computes for a set of variables V and 'Term's t and pre 
-- skolem functions for F_v for all v in V, such that the folllowing holds:
--
--  forall (FreeVars(t) \ V). pre(FreeVars(t) \ V) -> t[v -> F_v]
--
-- The usual scenario is that pre := exists V. t.
-- Both 'Term's should be free of uninterpreted functions.
skolemize :: Config -> [(Symbol, Sort)] -> Term -> Term -> IO (Map Symbol Term)
skolemize conf vars pre term = do
  pre <- SMT.simplify conf pre
  term <- SMT.simplify conf term
  error "TODO IMPLEMENT"

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
