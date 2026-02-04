---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Games.Variables
-- Description : State and input variable handling
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the handling of state and input variables that appear in symbolic
-- arenas as well as reactive program arenas. It also implements a lot of useful helper
-- functions to work with those.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Games.Variables
  ( -- Data structures
    Variables
  , Type(..)
  , -- Priming
    prime
  , unprime
  , isPrimed
  , -- Access
    inputs
  , stateVars
  , stateVars'
  , inputL
  , stateVarL
  , stateVarL'
  , sortOf
  , typeOf
  , isInput
  , isStateVar
  , isBounded
  , allSymbols
  , -- Creation
    empty
  , addInput
  , addStateVar
  , addVariable
  , setBounded
  , -- Short hands on terms
    mk
  , primeT
  , forallI
  , forallX
  , forallX'
  , existsI
  , existsX
  , existsX'
  , unintPred
  , unintPredTerm
  ) where

---------------------------------------------------------------------------------------------------
import Data.List (isSuffixOf)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Function, Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- Data structures
---------------------------------------------------------------------------------------------------
-- Next-state variables or also primed variables are represent by adding the following suffix
-- to the variable. This should all be handled internally by the module in the sense that an
-- user should not do thing with this suffix manually. It should not be exported!
primeSuffix :: String
primeSuffix = "~"

-- | This data structure represents a context of input, state, and potentially next-state
-- variables. The sort of the variable (its type in SMT language) is part of this context.
-- Usually such a context is associated to one specification and will seldom change.
data Variables = Variables
  { inputs :: Set Symbol
    -- ^ The input variables in a variable context.
  , stateVars :: Set Symbol
    -- ^ The state variables in a variables context
  , ioTypes :: Map Symbol Sort
  , bounded :: Set Symbol
  } deriving (Eq, Ord, Show)

-- | Representation of the type of a variable which consists of its state as input
-- or state, and its sort.
data Type
  = TInput Sort
  -- ^ representation of an input type
  | TState Sort
  -- ^ representation of an state type
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Priming
---------------------------------------------------------------------------------------------------
-- | Transform the symbol of a state variable in the symbol of a next-state variable.
-- This function works directly on the symbol and should be avoided if possible. Try to use
-- functions like 'primeT' instead.
prime :: Symbol -> Symbol
prime = (++ primeSuffix)

-- | Transform the symbol of next-state variable to one of a state variable (if possible).
-- Try to avoid it similar to 'prime'.
unprime :: Symbol -> Symbol
unprime s
  | isPrimed s = take (length s - length primeSuffix) s
  | otherwise = s

-- | Check if a symbol is primed like a next-state variable. For non variable symbols
-- this function does not have any meaning.
isPrimed :: Symbol -> Bool
isPrimed = isSuffixOf primeSuffix

---------------------------------------------------------------------------------------------------
-- Access
---------------------------------------------------------------------------------------------------
-- | The next-state variables in a variables context
stateVars' :: Variables -> Set Symbol
stateVars' = Set.map (++ primeSuffix) . stateVars

-- | 'inputs' as a list.
inputL :: Variables -> [Symbol]
inputL = Set.toList . inputs

-- | 'stateVars' as a list.
stateVarL :: Variables -> [Symbol]
stateVarL = Set.toList . stateVars

-- | 'stateVars'' as a list.
stateVarL' :: Variables -> [Symbol]
stateVarL' = Set.toList . stateVars'

-- | The sort of a variable. If the variable is not in the context, this method is undefined.
sortOf :: Variables -> Symbol -> Sort
sortOf vars var =
  case ioTypes vars !? unprime var of
    Just sort -> sort
    Nothing -> error $ "tried to access not exiting variable " ++ var

-- | The general type of a variable. If the variable is not in the context, this method is undefined.
typeOf :: Variables -> Symbol -> Type
typeOf vars var
  | var `elem` inputs vars = TInput (sortOf vars var)
  | otherwise = TState (sortOf vars var)

-- | Check if a variable is an input.
isInput :: Variables -> Symbol -> Bool
isInput vars var = var `elem` inputs vars

-- | Check if a variable is a state variable.
isStateVar :: Variables -> Symbol -> Bool
isStateVar vars var = var `elem` stateVars vars

-- | Check if a variable is marked as bounded. Note that the bounded mechanism
-- is not faithful and should be used for heuristics only.
isBounded :: Variables -> Symbol -> Bool
isBounded vars = (`elem` bounded vars)

-- | All symbols that appear in a variable context.
allSymbols :: Variables -> Set Symbol
allSymbols vars =
  inputs vars `Set.union` stateVars vars `Set.union` Set.map (++ primeSuffix) (stateVars vars)

allVars :: Variables -> Set Symbol
allVars vars = inputs vars `Set.union` stateVars vars

---------------------------------------------------------------------------------------------------
-- Creation
---------------------------------------------------------------------------------------------------
-- | The empty context without any variables.
empty :: Variables
empty =
  Variables {inputs = Set.empty, stateVars = Set.empty, ioTypes = Map.empty, bounded = Set.empty}

-- | Add an input variable to a variable context. If the variable name is already in use or
-- the variable name is already primed, this function is undefined.
addInput :: Variables -> Symbol -> Sort -> Variables
addInput vars var sort
  | var `elem` allVars vars = error $ "assert: " ++ var ++ " alread exists"
  | primeSuffix `isSuffixOf` var = error $ "assert: " ++ var ++ " has prime suffix"
  | otherwise =
    vars {inputs = Set.insert var (inputs vars), ioTypes = Map.insert var sort (ioTypes vars)}

-- | Add an state variable to a variable context. This also includes the primed state to the
-- context. If the variable name is already in use or the variable name is already primed, this
-- function is undefined.
addStateVar :: Variables -> Symbol -> Sort -> Variables
addStateVar vars var sort
  | var `elem` allVars vars = error $ "assert: " ++ var ++ " alread exists"
  | primeSuffix `isSuffixOf` var = error $ "assert: " ++ var ++ " has prime suffix"
  | otherwise =
    vars {stateVars = Set.insert var (stateVars vars), ioTypes = Map.insert var sort (ioTypes vars)}

-- | Add a variable based on its generic type. The same condition as for 'addInput' and
-- 'addStateVar' apply
addVariable :: Variables -> Symbol -> Type -> Variables
addVariable vars var =
  \case
    TInput sort -> addInput vars var sort
    TState sort -> addStateVar vars var sort

-- | Mark a variable to be of bounded domain. This mechanism can be used for heuristics
-- but cannot be relied on for correctness.
setBounded :: Variables -> Symbol -> Variables
setBounded vars var
  | isStateVar vars var = vars {bounded = Set.insert var (bounded vars)}
  | otherwise = vars

---------------------------------------------------------------------------------------------------
-- Short hands
---------------------------------------------------------------------------------------------------
-- | Create a term that consists of a simple variable. This method is undefined if the given
-- variable name is not in the context.
mk :: Variables -> Symbol -> Term
mk vars name
  | name `notElem` allSymbols vars = error $ "assert: " ++ name ++ " not found"
  | otherwise = FOL.var name (sortOf vars name)

-- | Replace all state variables in a term by their primed/next-state versions.
primeT :: Variables -> Term -> Term
primeT vars =
  FOL.mapSymbol $ \v ->
    if v `elem` stateVars vars
      then prime v
      else v

-- | Universally quantify over all inputs.
forallI :: Variables -> Term -> Term
forallI vars = FOL.forAll (inputL vars)

-- | Existentially quantify over all inputs.
existsI :: Variables -> Term -> Term
existsI vars = FOL.exists (inputL vars)

-- | Universally quantify over all current state variables.
forallX :: Variables -> Term -> Term
forallX vars = FOL.forAll (stateVarL vars)

-- | Existentially quantify over all current state variables.
existsX :: Variables -> Term -> Term
existsX vars = FOL.exists (stateVarL vars)

-- | Universally quantify over all next-state variables.
forallX' :: Variables -> Term -> Term
forallX' vars = FOL.forAll (stateVarL' vars)

-- | Existentially quantify over all next-state variables.
existsX' :: Variables -> Term -> Term
existsX' vars = FOL.exists (stateVarL' vars)

-- | Create an uninterpreted function, that has as argument sorts the sorts of
-- the state variables in the order of 'stateVarL'.
unintPred :: Variables -> String -> Function
unintPred vars name = FOL.CustomF name (map (sortOf vars) (stateVarL vars)) FOL.SBool

-- | Create an uninterpreted function term, that has as argument the simple variable terms
-- of the state variables in the order of 'stateVarL'.
unintPredTerm :: Variables -> String -> Term
unintPredTerm vars name = FOL.Func (unintPred vars name) $ map (mk vars) (stateVarL vars)
---------------------------------------------------------------------------------------------------
