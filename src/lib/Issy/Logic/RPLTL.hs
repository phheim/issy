module Issy.Logic.RPLTL
  ( Formula
  , Spec(..)
  , toFormula
  , isSafety
  ) where

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

-- TODO: enhance safety check beyond this simple one!
isSafety :: Spec -> Bool
isSafety spec = null (assumptions spec) && all TL.isSafety (guarantees spec)
