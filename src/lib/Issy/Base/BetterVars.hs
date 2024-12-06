{-# LANGUAGE LambdaCase #-}

-- TODO: add 'bounded' variable handeling
-- TODO: maybe ecnapulate variables in a speparate newtype Var type instead of symbol
--       This might than also include the sort!!!
--
module Issy.Base.Variables
  ( Type(..)
  , Variables
  , Var
  , toTerm
  , toSymbol
  , inputs
  , inputL
  , stateVars
  , stateVarL
  , stateVars'
  , stateVarL'
  , empty
  , get
  , addInput
  , addStateVar
  , addVariable
  , forallV
  , existsV
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
import qualified Issy.Logic.FOL as FOL

primeSuffix :: String
primeSuffix = "'"

--
-- TODO: maybe intergrate this into overall structure for better type safety!
--
data Var = Var
  { name :: Symbol
  , varType :: Type
  } deriving (Eq, Ord, Show)

toSymbol :: Var -> Symbol
toSymbol = name

toTerm :: Var -> Term
toTerm v =
  case varType v of
    TInput sort -> FOL.Var (name v) sort
    TOutput sort -> FOL.Var (name v) sort

forallV :: [Var] -> Term -> Term
forallV vars = forAll (map toSymbol vars)

existsV :: [Var] -> Term -> Term
existsV vars = exists (map toSymbol vars)

-- TODO: the data structure can be optimized, e.g. by having a map or so!
newtype Variables =
  Variables (Set Var)
  deriving (Eq, Ord, Show)

-- TODO: This can be optimized and have a better error message
get :: Variables -> Symbol -> Var
get (Variables vars) varname = Set.findMin (Set.filter ((== varname) . name) vars)

data Type
  = TInput Sort
  | TOutput Sort
  -- ^ TODO: rename to stateVar
  deriving (Eq, Ord, Show)

empty :: Variables
empty = Variables Set.empty

sortOf :: Var -> Sort
sortOf var =
  case varType var of
    TInput sort -> sort
    TOutput sort -> sort

typeOf :: Var -> Type
typeOf = varType

isInput :: Var -> Bool
isInput var =
  case varType var of
    TInput _ -> True
    TOutput _ -> False

isStateVar :: Var -> Bool
isStateVar = not . isInput

inputs :: Variables -> Set Var
inputs (Variables vars) = Set.filter isInput vars

stateVars :: Variables -> Set Var
stateVars (Variables vars) = Set.filter isStateVar vars

inputL :: Variables -> [Var]
inputL = Set.toList . inputs

stateVarL :: Variables -> [Var]
stateVarL = Set.toList . stateVars

stateVars' :: Variables -> Set Var
stateVars' = Set.map prime . stateVars

stateVarL' :: Variables -> [Var]
stateVarL' = Set.toList . stateVars'

allSymbols :: Variables -> Set Symbol
allSymbols vars =
  Set.map toSymbol
    $ inputs vars `Set.union` stateVars vars `Set.union` Set.map prime (stateVars vars)

-- TODO: adding can be collapsed!
addInput :: Variables -> Symbol -> Sort -> Variables
addInput (Variables vars) var sort
  | var `elem` allSymbols (Variables vars) = error $ "assert: " ++ var ++ " alread exists"
  | primeSuffix `isSuffixOf` var = error $ "assert: " ++ var ++ " has prime suffix"
  | otherwise = Variables (Set.insert (Var {name = var, varType = TInput sort}) vars)

addStateVar :: Variables -> Symbol -> Sort -> Variables
addStateVar (Variables vars) var sort
  | var `elem` allSymbols (Variables vars) = error $ "assert: " ++ var ++ " alread exists"
  | primeSuffix `isSuffixOf` var = error $ "assert: " ++ var ++ " has prime suffix"
  | otherwise = Variables (Set.insert (Var {name = var, varType = TOutput sort}) vars)

addVariable :: Variables -> Symbol -> Type -> Variables
addVariable vars var =
  \case
    TInput sort -> addInput vars var sort
    TOutput sort -> addStateVar vars var sort

forallI :: Variables -> Term -> Term
forallI vars = forallV (inputL vars)

existsI :: Variables -> Term -> Term
existsI vars = existsV (inputL vars)

forallX :: Variables -> Term -> Term
forallX vars = forallV (stateVarL vars)

existsX :: Variables -> Term -> Term
existsX vars = existsV (stateVarL vars)

existsX' :: Variables -> Term -> Term
existsX' vars = existsV (stateVarL' vars)

forallX' :: Variables -> Term -> Term
forallX' vars = forallV (stateVarL' vars)

isPrimed :: Var -> Bool
isPrimed = isSuffixOf primeSuffix . name

prime :: Var -> Var
prime var = var {name = name var ++ primeSuffix}

unprime :: Var -> Var
unprime v
  | isPrimed v =
    let n = name v
     in v {name = take (length n - length primeSuffix) n}
  | otherwise = v

primeT :: Variables -> Term -> Term
primeT vars =
  mapSymbol $ \v ->
    if v `elem` map toSymbol (stateVarL' vars)
      then v ++ primeSuffix
      else v
