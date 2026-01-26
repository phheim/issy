---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Monitor.Propagation
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

module Issy.Monitor.Propagation
  ( generatePredicatesTSL
  , generatePredicatesRPLTL
  , propagatedPredicatesTSL
  , propagatedPredicatesRPLTL
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (propagationLevel)
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT

generatePredicatesTSL :: Config -> Variables -> Set Term -> Set (Symbol, Term) -> IO (Set Term)
generatePredicatesTSL cfg vars preds updates = do
  preds <- pure $ Set.filter (all (Vars.isStateVar vars) . FOL.frees) preds
  let constUpdPreds = Set.unions $ Set.map constUpdateTerm updates
  let boolPreds =
        Set.map FOL.bvarT $ Set.filter ((== FOL.SBool) . Vars.sortOf vars) $ Vars.stateVars vars
  preds <- pure $ Set.union preds $ guardLevel 2 constUpdPreds
  preds <- pure $ Set.union preds $ guardLevel 2 boolPreds
  preds <- pure $ Set.union preds $ guardLevel 3 $ Set.unions $ Set.map mutate preds
  preds <- pure $ Set.union preds $ guardLevel 4 $ applyUpds preds
  preds <- pure $ Set.union preds $ guardLevel 1 $ Set.map FOL.neg preds
  Set.fromList <$> mapM (SMT.simplify cfg) (Set.toList preds)
  where
    guardLevel k
      | propagationLevel cfg >= k = id
      | otherwise = const Set.empty
    --
    mutate term =
      case term of
        FOL.Func FOL.FNot [arg] -> mutate arg
        FOL.Func f args
          | f `elem` FOL.comparisionFunctions ->
            Set.fromList [FOL.func FOL.FEq args, FOL.func FOL.FLt args, FOL.func FOL.FLte args]
          | otherwise -> Set.empty
        _ -> Set.empty
    --
    applyUpd (var, upd) =
      FOL.mapTerm $ \v _ ->
        if var == v
          then Just upd
          else Nothing
    applyUpds = Set.map (uncurry applyUpd) . Set.cartesianProduct updates
    --
    constUpdateTerm (var, upd)
      | null (FOL.frees upd) && (Vars.sortOf vars var /= FOL.SBool) =
        Set.singleton (Vars.mk vars var `FOL.equal` upd)
      | otherwise = Set.empty

generatePredicatesRPLTL :: Config -> Variables -> Set Term -> IO (Set Term)
generatePredicatesRPLTL cfg vars preds = do
  preds <- pure $ Set.filter (all (Vars.isStateVar vars) . FOL.frees) preds
  let boolPreds =
        Set.map FOL.bvarT $ Set.filter ((== FOL.SBool) . Vars.sortOf vars) $ Vars.stateVars vars
  preds <- pure $ Set.union preds $ guardLevel 2 boolPreds
  preds <- pure $ Set.union preds $ guardLevel 3 $ Set.unions $ Set.map mutate preds
  preds <- pure $ Set.union preds $ guardLevel 1 $ Set.map FOL.neg preds
  Set.fromList <$> mapM (SMT.simplify cfg) (Set.toList preds)
  where
    guardLevel k
      | propagationLevel cfg >= k = id
      | otherwise = const Set.empty
    --
    mutate term =
      case term of
        FOL.Func FOL.FNot [arg] -> mutate arg
        FOL.Func f args
          | f `elem` FOL.comparisionFunctions ->
            Set.fromList [FOL.func FOL.FEq args, FOL.func FOL.FLt args, FOL.func FOL.FLte args]
          | otherwise -> Set.empty
        _ -> Set.empty

propagatedPredicatesRPLTL :: Config -> Variables -> Term -> Set Term -> IO [Term]
propagatedPredicatesRPLTL cfg vars constr =
  filterM (SMT.valid cfg . FOL.impl constr . Vars.primeT vars) . Set.toList

propagatedPredicatesTSL :: Config -> Term -> [(Symbol, Term)] -> Set Term -> IO [Term]
propagatedPredicatesTSL cfg constr upds = filterM propagate . Set.toList
  where
    mapping = Map.fromList upds
    --    
    propagate :: Term -> IO Bool
    propagate term
      | all (`Map.member` mapping) (FOL.frees term) =
        SMT.valid cfg $ FOL.impl constr $ FOL.mapTermM mapping term
      | otherwise = pure False
---------------------------------------------------------------------------------------------------
