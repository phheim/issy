---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.Temporal
-- Description : Temporal logic representation
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module provides an polymorphic interface for temporal logic formulas and specifications
-- (with linear time) that can be use for logics like RPLTL, TSL or LTL. As for now
-- this module does not support past temporal operators, finite traces or branching time.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Temporal
  ( Formula(..)
  , UOp(..)
  , BOp(..)
  , next
  , globally
  , eventually
  , atoms
  , --
    Spec(..)
  , toFormula
  , mapF
  , isSafety
  ) where

---------------------------------------------------------------------------------------------------
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Games.Variables (Variables)

---------------------------------------------------------------------------------------------------
-- Plain Formulas
---------------------------------------------------------------------------------------------------
-- | Polymorphic representation of linear-time temporal logic formulas
data Formula a
  = Atom a
  -- ^ polymorhic atomic terms/propositions
  | And [Formula a]
  -- ^ boolean conjunction
  | Or [Formula a]
  -- ^ boolean disjunction
  | Not (Formula a)
  -- ^ boolean negation
  | UExp UOp (Formula a)
  -- ^ unary temporal operator
  | BExp BOp (Formula a) (Formula a)
  -- ^ binary temporal operator
  deriving (Eq, Ord, Show)

-- | Enum for unary temporal logic operators
data UOp
  = Next
  -- ^ next temporal operator, indicates that the sub-formula
  -- has to hold in the next time step
  | Globally
  -- ^ globally temporal operator, indicates that the sub-formula
  -- has to hold in the current step, and all future time-steps
  | Eventually
  -- ^ eventually temporal operator, indicates that the sub-formula
  -- has to hold now or in one future time-step
  deriving (Eq, Ord, Show)

-- | Enum for binary temporal logic operators
data BOp
  = Until
  -- ^ until temporal operator, indicates that the first sub-formula has to
  -- hold as long as the second formula does not hold, and the later must happen
  | WeakUntil
  -- ^ weak until temporal operator, indicates that the first sub-formula has to
  -- hold as long as the second formula does not hold, and the later can happen
  | Release
  -- ^ release temporal operator, indicates that the second sub-formula has to
  -- hold till a time step, where the first one also holds
  deriving (Eq, Ord, Show)

instance Functor Formula where
  fmap m (Atom a) = Atom (m a)
  fmap m (And fs) = And $ map (fmap m) fs
  fmap m (Or fs) = Or $ map (fmap m) fs
  fmap m (Not f) = Not $ fmap m f
  fmap m (UExp op f) = UExp op $ fmap m f
  fmap m (BExp op f g) = BExp op (fmap m f) (fmap m g)

-- | Add the next operator on top of a formula.
next :: Formula a -> Formula a
next = UExp Next

-- | Add the globally operator on top of a formula.
globally :: Formula a -> Formula a
globally = UExp Globally

-- | Add the eventually operator on top of a formula.
eventually :: Formula a -> Formula a
eventually = UExp Eventually

-- | Check if a temporal logic formula is bounded, i.e. there is
-- a limit on how many time-steps in the future it can impose conditions on.
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

-- | Check if a formula is syntactically a safety formula.
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

-- | All atoms that appear in the temporal formula.
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
-- Specifications
---------------------------------------------------------------------------------------------------
-- | Representation of an assume-guarantee specification with additional 'Variables'. The
-- semantic of such a specification is formula which results from the
-- conjunction of the assumptions implying the conjunction of guarantees.
data Spec a = Spec
  { variables :: Variables
  -- ^ store of typed variables
  , assumptions :: [Formula a]
  -- ^ assumptions of the temporal logic specification
  , guarantees :: [Formula a]
  -- ^ guarantees of the temporal logic specification
  } deriving (Eq, Ord, Show)

-- | Translate the specification into its semantically equivalent single
-- temporal logic formula
toFormula :: Spec a -> Formula a
toFormula spec = Or [Not (And (assumptions spec)), And (guarantees spec)]

-- | Map all assumption and guarantees in the specification
mapF :: (Formula a -> Formula b) -> Spec a -> Spec b
mapF m spec =
  Spec
    { variables = variables spec
    , assumptions = map m (assumptions spec)
    , guarantees = map m (guarantees spec)
    }

-- | Approximate syntactically if a specification is a safety specification.
-- By the nature of an approximation, this check is not complete.
isSafety :: Spec a -> Bool
isSafety spec = all isTemporalBounded (assumptions spec) && all formulaIsSafety (guarantees spec)
---------------------------------------------------------------------------------------------------
