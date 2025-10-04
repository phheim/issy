{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Logic.RPLTL
  ( Atom
  , preds
  , pullBool
  , pullBoolF
  , pushBool
  , pushBoolF
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Function(FAnd, FImply, FNot, FOr), Term(Func))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Temporal as TL
import Issy.Logic.Temporal (Formula(..), Spec(..))

type Atom = Term

preds :: TL.Spec Term -> Set Term
preds spec = Set.unions $ map TL.atoms $ assumptions spec ++ guarantees spec

pullBool :: TL.Spec Term -> TL.Spec Term
pullBool spec =
  spec
    {assumptions = map pullBoolF $ assumptions spec, guarantees = map pullBoolF $ guarantees spec}

pullBoolF :: Formula Term -> Formula Term
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

pushBool :: TL.Spec Term -> TL.Spec Term
pushBool spec =
  spec
    {assumptions = map pushBoolF $ assumptions spec, guarantees = map pushBoolF $ guarantees spec}

pushBoolF :: Formula Term -> Formula Term
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
