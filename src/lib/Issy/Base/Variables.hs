{-# LANGUAGE LambdaCase #-}

-- TODO: add 'bounded' variable handeling
module Issy.Base.Variables
  ( Type(..)
  , Variables
  , inputs
  , inputL
  , stateVars
  , stateVarL
  , stateVars'
  , stateVarL'
  , empty
  , addInput
  , addStateVar
  , addVariable
  , forallI
  , forallX
  , forallX'
  , existsI
  , existsX
  , existsX'
  , prime
  , typeOf
  , sortOf
  , isInput
  , isStateVar
  , allSymbols
  , primeT
  , unprime
  , isPrimed
  ) where

import Data.List (isSuffixOf)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Sort, Symbol, Term, exists, forAll, mapSymbol)

primeSuffix :: String
primeSuffix = "'"

data Variables = Variables
  { inputs :: Set Symbol
  , stateVars :: Set Symbol
  , ioTypes :: Map Symbol Sort
  } deriving (Eq, Ord, Show)

data Type
  = TInput Sort
  | TOutput Sort
  deriving (Eq, Ord, Show)

allVars :: Variables -> Set Symbol
allVars vars = inputs vars `Set.union` stateVars vars

empty :: Variables
empty = Variables {inputs = Set.empty, stateVars = Set.empty, ioTypes = Map.empty}

sortOf :: Variables -> Symbol -> Sort
sortOf vars var =
  case ioTypes vars !? unprime var of
    Just sort -> sort
    Nothing -> error $ "tried to access not exiting variable " ++ var

typeOf :: Variables -> Symbol -> Type
typeOf vars var
  | var `elem` inputs vars = TInput (sortOf vars var)
  | otherwise = TOutput (sortOf vars var)

isInput :: Variables -> Symbol -> Bool
isInput vars var = var `elem` inputs vars

isStateVar :: Variables -> Symbol -> Bool
isStateVar vars var = var `elem` stateVars vars

inputL :: Variables -> [Symbol]
inputL = Set.toList . inputs

stateVarL :: Variables -> [Symbol]
stateVarL = Set.toList . stateVars

stateVars' :: Variables -> Set Symbol
stateVars' = Set.map (++ primeSuffix) . stateVars

stateVarL' :: Variables -> [Symbol]
stateVarL' = Set.toList . stateVars'

allSymbols :: Variables -> Set Symbol
allSymbols vars =
  inputs vars `Set.union` stateVars vars `Set.union` Set.map (++ primeSuffix) (stateVars vars)

addInput :: Variables -> Symbol -> Sort -> Variables
addInput vars var sort
  | var `elem` allVars vars = error $ "assert: " ++ var ++ " alread exists"
  | primeSuffix `isSuffixOf` var = error $ "assert: " ++ var ++ " has prime suffix"
  | otherwise =
    vars {inputs = Set.insert var (inputs vars), ioTypes = Map.insert var sort (ioTypes vars)}

addStateVar :: Variables -> Symbol -> Sort -> Variables
addStateVar vars var sort
  | var `elem` allVars vars = error $ "assert: " ++ var ++ " alread exists"
  | primeSuffix `isSuffixOf` var = error $ "assert: " ++ var ++ " has prime suffix"
  | otherwise =
    vars {stateVars = Set.insert var (stateVars vars), ioTypes = Map.insert var sort (ioTypes vars)}

addVariable :: Variables -> Symbol -> Type -> Variables
addVariable vars var =
  \case
    TInput sort -> addInput vars var sort
    TOutput sort -> addStateVar vars var sort

forallI :: Variables -> Term -> Term
forallI vars = forAll (inputL vars)

existsI :: Variables -> Term -> Term
existsI vars = exists (inputL vars)

forallX :: Variables -> Term -> Term
forallX vars = forAll (stateVarL vars)

existsX :: Variables -> Term -> Term
existsX vars = exists (stateVarL vars)

existsX' :: Variables -> Term -> Term
existsX' vars = exists (stateVarL' vars)

forallX' :: Variables -> Term -> Term
forallX' vars = forAll (stateVarL' vars)

isPrimed :: Symbol -> Bool
isPrimed = isSuffixOf primeSuffix

prime :: Symbol -> Symbol
prime = (++ primeSuffix)

unprime :: Symbol -> Symbol
unprime s
  | isPrimed s = take (length s - length primeSuffix) s
  | otherwise = s

primeT :: Variables -> Term -> Term
primeT vars =
  mapSymbol $ \v ->
    if v `elem` stateVars vars
      then prime v
      else v
