---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.TSLMT
-- Description : Representation of TSLMT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the basic functionalities for representing TSLMT.
-- It builds upon the general temporal logic representation 'Formula'.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.TSLMT
  ( Atom(..)
  , preds
  , updates
  , pullBool
  , pullBoolF
  , pushBool
  , pushBoolF
  ) where

---------------------------------------------------------------------------------------------------
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Function(FAnd, FImply, FNot, FOr), Symbol, Term(Func))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Temporal as TL
import Issy.Logic.Temporal (Formula(..))

---------------------------------------------------------------------------------------------------
-- Basics
---------------------------------------------------------------------------------------------------
-- | TSLMT is represented with temporal logic formulas 'Formula' where the atomic terms
-- are predicates and updates.
data Atom
  = Predicate Term
  -- ^ predicates in TSLMT are simple first-order logic predicates without quantifiers
  | Update Symbol Term
  -- ^ updates of an variable by a term, i.e. the variable
  -- should be assigned (for the next time-step)
  -- the current value of the update term
  deriving (Eq, Ord, Show)

-- | All predicates that are present in the formula.
preds :: TL.Spec Atom -> Set Term
preds =
  Set.unions
    . Set.map
        (\case
           Predicate pred -> Set.singleton pred
           _ -> Set.empty)
    . TL.atoms
    . TL.toFormula

-- | All updates that are present in the formula.
updates :: TL.Spec Atom -> Set (Symbol, Term)
updates =
  Set.unions
    . Set.map
        (\case
           Update var upd -> Set.singleton (var, upd)
           _ -> Set.empty)
    . TL.atoms
    . TL.toFormula

---------------------------------------------------------------------------------------------------
-- Transformations
---------------------------------------------------------------------------------------------------
-- | Apply 'pullBoolF' to a whole specification.
pullBool :: TL.Spec Atom -> TL.Spec Atom
pullBool = TL.mapF pullBoolF

-- | Apply 'pushBoolF' to a whole specification.
pushBool :: TL.Spec Atom -> TL.Spec Atom
pushBool = TL.mapF pushBoolF

-- | The TSLMT representation allows to have boolean combination of predicates
-- which themself might be boolean combinations. 'pullBoolF' moves the boolean
-- combinations to the 'Term' level and pulls up the predicates in the
-- overall term tree.
pullBoolF :: Formula Atom -> Formula Atom
pullBoolF = go
  where
    go =
      \case
        Atom f -> Atom f
        UExp op f -> UExp op (go f)
        BExp op f g -> BExp op (go f) (go g)
        Not f ->
          case go f of
            Atom (Predicate f) -> patom $ FOL.neg f
            f -> Not f
        And [] -> patom FOL.true
        And [f] -> go f
        And fs ->
          let gs = map go fs
           in case allAtoms gs of
                Just gs -> patom $ FOL.andf gs
                Nothing -> And gs
        Or [] -> patom FOL.false
        Or [f] -> go f
        Or fs ->
          let gs = map go fs
           in case allAtoms gs of
                Just gs -> patom $ FOL.orf gs
                Nothing -> Or gs
    allAtoms =
      \case
        [] -> Just []
        Atom (Predicate f):xr -> (f :) <$> allAtoms xr
        _ -> Nothing

-- | 'pushBoolF' does the opposite of 'pullBoolF' and moves the boolean
-- combinations to the 'Formula' level and moves down the predicates in the
-- overall term tree.
pushBoolF :: Formula Atom -> Formula Atom
pushBoolF = go
  where
    go =
      \case
        Atom (Predicate (Func FAnd fs)) -> And $ map (go . patom) fs
        Atom (Predicate (Func FOr fs)) -> Or $ map (go . patom) fs
        Atom (Predicate (Func FNot [f])) -> Not $ go $ patom f
        Atom (Predicate (Func FImply [f, g])) -> Or [Not (go (patom f)), go (patom g)]
        Atom (Predicate f)
          | f == FOL.true -> And []
          | f == FOL.false -> Or []
          | otherwise -> patom f
        Atom (Update x u) -> Atom (Update x u)
        And fs -> And $ map go fs
        Or fs -> Or $ map go fs
        Not f -> Not $ go f
        UExp op f -> UExp op (go f)
        BExp op f g -> BExp op (go f) (go g)

patom :: Term -> Formula Atom
patom = Atom . Predicate
---------------------------------------------------------------------------------------------------
