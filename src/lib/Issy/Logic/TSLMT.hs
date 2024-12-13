{-# LANGUAGE LambdaCase #-}

module Issy.Logic.TSLMT
  ( Atom(..)
  , Formula
  , Spec(..)
  , preds
  , updates
  , toFormula
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.Temporal as TL

data Atom
  = Update Symbol Term
  | Predicate Term
  deriving (Eq, Ord, Show)

type Formula = TL.Formula Atom

data Spec = Spec
  { variables :: Variables
  , assumptions :: [Formula]
  , guarantees :: [Formula]
  } deriving (Eq, Ord, Show)

toFormula :: Spec -> Formula
toFormula spec = TL.Or [TL.Not (TL.And (assumptions spec)), TL.And (guarantees spec)]

preds :: Spec -> Set Term
preds =
  Set.unions
    . Set.map
        (\case
           Predicate pred -> Set.singleton pred
           _ -> Set.empty)
    . TL.atoms
    . toFormula

updates :: Spec -> Set (Symbol, Term)
updates =
  Set.unions
    . Set.map
        (\case
           Update var upd -> Set.singleton (var, upd)
           _ -> Set.empty)
    . TL.atoms
    . toFormula
