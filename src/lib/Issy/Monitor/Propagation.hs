module Issy.Monitor.Propagation
  ( generatePredicates
  , propagatedPredicates
  ) where

import Control.Monad (filterM)
import qualified Data.Map.Strict as Map
import Data.Set (Set, cartesianProduct)
import qualified Data.Set as Set

import Issy.Base.Variables
import Issy.Config (Config, propagationLevel)
import Issy.Logic.FOL
import Issy.Logic.SMT

generatePredicates :: Config -> Variables -> Set Term -> Set (Symbol, Term) -> IO (Set Term)
generatePredicates cfg vars preds updates = do
  preds <- pure $ Set.filter (all (isStateVar vars) . frees) preds
  let constUpdPreds = Set.unions $ Set.map constUpdateTerm updates
  let boolPreds = Set.map bvarT $ Set.filter ((== SBool) . sortOf vars) $ stateVars vars
  preds <- pure $ preds `Set.union` guardLevel 2 constUpdPreds
  preds <- pure $ preds `Set.union` guardLevel 2 boolPreds
  preds <- pure $ preds `Set.union` guardLevel 3 (Set.unions (Set.map mutate preds))
  preds <- pure $ preds `Set.union` guardLevel 4 (applyUpds preds)
  preds <- pure $ preds `Set.union` guardLevel 1 (Set.map neg preds)
  Set.fromList <$> mapM (simplify cfg) (Set.toList preds)
  where
    guardLevel k
      | propagationLevel cfg >= k = id
      | otherwise = const Set.empty
    --
    mutate term =
      case term of
        Func (PredefF "not") [arg] -> mutate arg
        Func (PredefF name) args
          | name `elem` ["=", "<", ">", "<=", ">="] ->
            Set.fromList [func "=" args, func "<" args, func "<=" args]
          | otherwise -> Set.empty
        _ -> Set.empty
    --
    applyUpd (var, upd) =
      mapTerm $ \v _ ->
        if var == v
          then Just upd
          else Nothing
    applyUpds = Set.map (uncurry applyUpd) . cartesianProduct updates
    --
    constUpdateTerm (var, upd)
      | null (frees upd) && (sortOf vars var /= SBool) =
        Set.singleton (Var var (sortOf vars var) `equal` upd)
      | otherwise = Set.empty

generatePredicatesRPLT :: Config -> Variables -> Set Term -> IO (Set Term)
generatePredicatesRPLT cfg vars preds = do
  preds <- pure $ Set.filter (all (isStateVar vars) . frees) preds
  let boolPreds = Set.map bvarT $ Set.filter ((== SBool) . sortOf vars) $ stateVars vars
  preds <- pure $ preds `Set.union` guardLevel 2 boolPreds
  preds <- pure $ preds `Set.union` guardLevel 3 (Set.unions (Set.map mutate preds))
  preds <- pure $ preds `Set.union` guardLevel 1 (Set.map neg preds)
  Set.fromList <$> mapM (simplify cfg) (Set.toList preds)
  where
    guardLevel k
      | propagationLevel cfg >= k = id
      | otherwise = const Set.empty
    --
    mutate term =
      case term of
        Func (PredefF "not") [arg] -> mutate arg
        Func (PredefF name) args
          | name `elem` ["=", "<", ">", "<=", ">="] ->
            Set.fromList [func "=" args, func "<" args, func "<=" args]
          | otherwise -> Set.empty
        _ -> Set.empty

propagatedPredicates :: Config -> Term -> [(Symbol, Term)] -> Set Term -> IO [Term]
propagatedPredicates cfg constr upds = filterM propagate . Set.toList
  where
    mapping = Map.fromList upds
    --    
    propagate :: Term -> IO Bool
    propagate term
      | all (`Map.member` mapping) (frees term) = valid cfg $ constr `impl` mapTermM mapping term
      | otherwise = pure False
