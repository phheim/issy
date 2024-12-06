{-# LANGUAGE LambdaCase #-}

module Issy.Logic.TSLMT
  ( TSLAtom(..)
  , TSL
  , TSLSpec(..)
  , toFormula
  , tslSpecUpdates
  , tslSpecPreds
  ) where

import Data.Set (Set)
import qualified Data.Set as Set (fromList, toList)

import Issy.Base.Variables (Variables)
import Issy.Logic.FOL (Symbol, Term)
import Issy.Logic.Temporal (TL(TLAnd, TLNot, TLOr), tlAtoms)

data TSLAtom
  = TSLUpdate Symbol Term
  | TSLPredicate Term
  deriving (Eq, Ord, Show)

type TSL = TL TSLAtom

data TSLSpec = TSLSpec
  { variables :: Variables
  , assumptions :: [TSL]
  , guarantees :: [TSL]
  } deriving (Eq, Ord, Show)

toFormula :: TSLSpec -> TSL
toFormula spec = TLOr [TLNot (TLAnd (assumptions spec)), TLAnd (guarantees spec)]

tslUpdates :: TSL -> Set (Symbol, Term)
tslUpdates tsl =
  Set.fromList
    $ concatMap
        (\case
           TSLUpdate var upd -> [(var, upd)]
           _ -> [])
    $ Set.toList
    $ tlAtoms tsl

tslPreds :: TSL -> Set Term
tslPreds tsl =
  Set.fromList
    $ concatMap
        (\case
           TSLPredicate pred -> [pred]
           _ -> [])
    $ Set.toList
    $ tlAtoms tsl

tslSpecUpdates :: TSLSpec -> Set (Symbol, Term)
tslSpecUpdates = tslUpdates . toFormula

tslSpecPreds :: TSLSpec -> Set Term
tslSpecPreds = tslPreds . toFormula
