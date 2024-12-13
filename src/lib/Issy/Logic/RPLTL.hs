module Issy.Logic.RPLTL
  ( Formula
  , Spec(..)
  , preds
  , isSafety
  , toFormula
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.Temporal as TL

type Formula = TL.Formula Term

data Spec = Spec
  { variables :: Variables
  , assumptions :: [Formula]
  , guarantees :: [Formula]
  } deriving (Eq, Ord, Show)

toFormula :: Spec -> Formula
toFormula spec = TL.Or [TL.Not (TL.And (assumptions spec)), TL.And (guarantees spec)]

isSafety :: Spec -> Bool
isSafety spec = all TL.isTemporalBounded (assumptions spec) && all TL.isSafety (guarantees spec)

preds :: Spec -> Set Term
preds spec = Set.unions $ map TL.atoms $ assumptions spec ++ guarantees spec
