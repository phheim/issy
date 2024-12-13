{-# LANGUAGE LambdaCase #-}

module Issy.Logic.Temporal
  ( BOp(..)
  , UOp(..)
  , Formula(..)
  , next
  , globally
  , eventually
  , atoms
  , isSafety
  , isTemporalBounded
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

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

isSafety :: Formula a -> Bool
isSafety =
  \case
    And fs -> all isSafety fs
    Or fs -> all isSafety fs
    UExp Globally f -> isSafety f
    UExp Next f -> isSafety f
    BExp WeakUntil f g -> isSafety f && isSafety g
    BExp Release f g -> isSafety f && isSafety g
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
