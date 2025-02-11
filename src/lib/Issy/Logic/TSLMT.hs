{-# LANGUAGE LambdaCase #-}

module Issy.Logic.TSLMT
  ( Atom(..)
  , preds
  , updates
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.Temporal as TL

data Atom
  = Update Symbol Term
  | Predicate Term
  deriving (Eq, Ord, Show)

preds :: TL.Spec Atom -> Set Term
preds =
  Set.unions
    . Set.map
        (\case
           Predicate pred -> Set.singleton pred
           _ -> Set.empty)
    . TL.atoms
    . TL.toFormula

updates :: TL.Spec Atom -> Set (Symbol, Term)
updates =
  Set.unions
    . Set.map
        (\case
           Update var upd -> Set.singleton (var, upd)
           _ -> Set.empty)
    . TL.atoms
    . TL.toFormula
