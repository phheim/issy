---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.RPLTL
-- Description : Representation of RPLTL
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the basic functionalities for representing RPLTL.
-- It builds upon the general temporal logic representation 'Formula'.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.RPLTL
  ( Atom
  , preds
  , pullBool
  , pullBoolF
  , pushBool
  , pushBoolF
  ) where

---------------------------------------------------------------------------------------------------
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Function(FAnd, FImply, FNot, FOr), Term(Func))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Temporal as TL
import Issy.Logic.Temporal (Formula(..), Spec(..))

---------------------------------------------------------------------------------------------------
-- | RPLTL formulas are represented as temporal formulas 'Formula' where the atomic
-- terms are first-order logic predicates (without quantifiers). Those predicates should
-- range over input, state, and next state variables.
type Atom = Term

-- | All atomic terms / predicates that are present in the formula.
preds :: Spec Atom -> Set Atom
preds spec = Set.unions $ map TL.atoms $ assumptions spec ++ guarantees spec

---------------------------------------------------------------------------------------------------
-- | Apply 'pullBoolF' to a whole specification.
pullBool :: Spec Atom -> Spec Atom
pullBool = TL.mapF pullBoolF

-- | Apply 'pushBoolF' to a whole specification.
pushBool :: Spec Atom -> Spec Atom
pushBool = TL.mapF pushBoolF

-- | The RPLTL representation allows to have boolean combination of atomic terms
-- which themself might be boolean combinations. 'pullBoolF' moves the boolean
-- combinations to the 'Term' level and pulls up the atomic terms in the
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
            Atom f -> Atom $ FOL.neg f
            f -> Not f
        And [] -> Atom FOL.true
        And [f] -> go f
        And fs ->
          let gs = map go fs
           in case allAtoms gs of
                Just gs -> Atom $ FOL.andf gs
                Nothing -> And gs
        Or [] -> Atom FOL.false
        Or [f] -> go f
        Or fs ->
          let gs = map go fs
           in case allAtoms gs of
                Just gs -> Atom $ FOL.orf gs
                Nothing -> Or gs
    allAtoms =
      \case
        [] -> Just []
        Atom f:xr -> (f :) <$> allAtoms xr
        _ -> Nothing

-- | 'pushBoolF' does the opposite of 'pullBoolF' and moves the boolean
-- combinations to the 'Formula' level and moves down the atomic terms in the
-- overall term tree.
pushBoolF :: Formula Atom -> Formula Atom
pushBoolF = go
  where
    go =
      \case
        Atom (Func FAnd fs) -> And $ map (go . Atom) fs
        Atom (Func FOr fs) -> Or $ map (go . Atom) fs
        Atom (Func FNot [f]) -> Not $ go $ Atom f
        Atom (Func FImply [f, g]) -> Or [Not (go (Atom f)), go (Atom g)]
        Atom f
          | f == FOL.true -> And []
          | f == FOL.false -> Or []
          | otherwise -> Atom f
        And fs -> And $ map go fs
        Or fs -> Or $ map go fs
        Not f -> Not $ go f
        UExp op f -> UExp op (go f)
        BExp op f g -> BExp op (go f) (go g)
---------------------------------------------------------------------------------------------------
