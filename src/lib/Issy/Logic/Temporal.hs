---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.Temporal
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Logic.Temporal
  ( BOp(..)
  , UOp(..)
  , Formula(..)
  , Spec(..)
  , mapF
  , next
  , globally
  , eventually
  , atoms
  , isSafety
  , toFormula
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Games.Variables (Variables)

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

instance Functor Formula where
  fmap m (Atom a) = Atom (m a)
  fmap m (And fs) = And $ map (fmap m) fs
  fmap m (Or fs) = Or $ map (fmap m) fs
  fmap m (Not f) = Not $ fmap m f
  fmap m (UExp op f) = UExp op $ fmap m f
  fmap m (BExp op f g) = BExp op (fmap m f) (fmap m g)

data Spec a = Spec
  { variables :: Variables
  , assumptions :: [Formula a]
  , guarantees :: [Formula a]
  } deriving (Eq, Ord, Show)

mapF :: (Formula a -> Formula b) -> Spec a -> Spec b
mapF m spec =
  Spec
    { variables = variables spec
    , assumptions = map m (assumptions spec)
    , guarantees = map m (guarantees spec)
    }

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
---------------------------------------------------------------------------------------------------
