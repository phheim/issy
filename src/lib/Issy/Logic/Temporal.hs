{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Logic.Temporal
  ( BOp(..)
  , UOp(..)
  , Formula(..)
  , Spec(..)
  , next
  , globally
  , eventually
  , atoms
  , isSafety
  , toFormula
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)

data BOp
  = Until
  | WeakUntil
  | Release
  deriving (Eq, Ord, Show)

data UOp
  = Next
  | Globally
  | Eventually
  deriving (Eq, Ord, Show)

data Formula a
  = Atom a
  | And [Formula a]
  | Or [Formula a]
  | Not (Formula a)
  -- Temporal operators
  | UExp UOp (Formula a)
  | BExp BOp (Formula a) (Formula a)
  deriving (Eq, Ord, Show)

data Spec a = Spec
  { variables :: Variables
  , assumptions :: [Formula a]
  , guarantees :: [Formula a]
  } deriving (Eq, Ord, Show)

toFormula :: Spec a -> Formula a
toFormula spec = Or [Not (And (assumptions spec)), And (guarantees spec)]

isSafety :: Spec a -> Bool
isSafety spec = all isTemporalBounded (assumptions spec) && all formulaIsSafety (guarantees spec)

next :: Formula a -> Formula a
next = UExp Next

globally :: Formula a -> Formula a
globally = UExp Globally

eventually :: Formula a -> Formula a
eventually = UExp Eventually

isTemporalBounded :: Formula a -> Bool
isTemporalBounded =
  \case
    Atom _ -> True
    And fs -> all isTemporalBounded fs
    Or fs -> all isTemporalBounded fs
    Not f -> isTemporalBounded f
    UExp Next f -> isTemporalBounded f
    UExp _ _ -> False
    BExp {} -> False

formulaIsSafety :: Formula a -> Bool
formulaIsSafety = go
  where
    go =
      \case
        And fs -> all go fs
        Or fs -> all go fs
        UExp Globally f -> go f
        UExp Next f -> go f
        BExp WeakUntil f g -> go f && go g
        BExp Release f g -> go f && go g
        f -> isTemporalBounded f

atoms :: Ord a => Formula a -> Set a
atoms =
  \case
    Atom atom -> Set.singleton atom
    And fs -> Set.unions $ map atoms fs
    Or fs -> Set.unions $ map atoms fs
    Not f -> atoms f
    UExp _ f -> atoms f
    BExp _ f g -> atoms f `Set.union` atoms g
