module Issy.Logic.RPLTL
  ( Formula
  , Spec(..)
  , toFormula
  , isSafety
  , preds
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)
import Issy.Logic.FOL (Term)
import Issy.Logic.Temporal (TL(TLAnd, TLNot, TLOr))
import qualified Issy.Logic.Temporal as TL

type Formula = TL Term

data Spec = Spec
  { variables :: Variables
  , assumptions :: [Formula]
  , guarantees :: [Formula]
  } deriving (Eq, Ord, Show)

toFormula :: Spec -> Formula
toFormula spec = TLOr [TLNot (TLAnd (assumptions spec)), TLAnd (guarantees spec)]

isSafety :: Spec -> Bool
isSafety spec = all TL.isTemporalBounded (assumptions spec) && all TL.isSafety (guarantees spec)

preds :: Spec -> Set Term
preds spec = Set.unions $ map TL.tlAtoms $ assumptions spec ++ guarantees spec
