{-# LANGUAGE Safe #-}

module Issy.Logic.RPLTL
  ( Atom
  , preds
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Term)
import qualified Issy.Logic.Temporal as TL

type Atom = Term

preds :: TL.Spec Atom -> Set Term
preds spec = Set.unions $ map TL.atoms $ TL.assumptions spec ++ TL.guarantees spec
