---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.Propositional
-- Description : Propositional logic operations
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Propositional
  ( Prop(..)
  , Propositional(..)
  , NNF(..)
  , toNNF
  , normNNF
  , DNF(..)
  , toDNF
  , CNF(..)
  , toCNF
  ) where

---------------------------------------------------------------------------------------------------
-- Definitions
---------------------------------------------------------------------------------------------------
-- | 'Prop' represents a propositional formula of propositions of some arbitrary type
data Prop a
  = PConst Bool
  | PLit a
  | PAnd [Prop a]
  | POr [Prop a]
  | PNot (Prop a)
  deriving (Eq, Ord, Show)

-- | A formula in disjunctive normal form over propositions, as
-- list (disjunction) of lists (conjunctions) of literals. A negative boolean value represents
-- a negated literal.
newtype DNF a =
  DNF [[(Bool, a)]]
  deriving (Eq, Ord, Show)

-- | A formula in conjunctive normal form over propositions, as
-- list (conjunction) of lists (disjunctions) of literals. A negative boolean value represents
-- a negated literal.
newtype CNF a =
  CNF [[(Bool, a)]]
  deriving (Eq, Ord, Show)

-- | This class represent types that can have a top-level propositional logic
-- structure, i.e. are semantically Boolean combinations of their own type.
class Propositional p where
  -- | 'toProp' unfolds the boolean structure from the type as 'Prop'. Note that this must
  -- only be semantic-preserving not necessary syntax-preserving (e.g. implications can
  -- be transformed to other operations)
  toProp :: p -> Prop p
  -- | 'fromProp' refolds the explicit structure from 'Prop' back into the original type
  fromProp :: Prop p -> p

-- | 'toCNF' transforms the top-level boolean structure of 'Propositional' objects to CNF
toNNF :: Propositional a => a -> NNF a
toNNF = propToNNF . toProp

normNNF :: Propositional a => a -> a
normNNF = fromProp . nnfToProp . toNNF

-- | 'toDNF' transforms the top-level boolean structure of 'Propositional' objects to 'DNF
toDNF :: Propositional a => a -> DNF a
toDNF = nnfToDNF . toNNF

-- | 'toCNF' transforms the top-level boolean structure of 'Propositional' objects to CNF
toCNF :: Propositional a => a -> CNF a
toCNF = nnfToCNF . toNNF

---------------------------------------------------------------------------------------------------
-- Class instances
---------------------------------------------------------------------------------------------------
instance Functor Prop where
  fmap m =
    \case
      PConst c -> PConst c
      PLit a -> PLit (m a)
      PAnd fs -> PAnd $ map (fmap m) fs
      POr fs -> POr $ map (fmap m) fs
      PNot f -> PNot $ fmap m f

---------------------------------------------------------------------------------------------------
-- Normal Form Transformations
---------------------------------------------------------------------------------------------------
data NNF a
  = NNFLit Bool a
  | NNFAnd [NNF a]
  | NNFOr [NNF a]
  deriving (Eq, Ord, Show)

propToNNF :: Prop a -> NNF a
propToNNF =
  \case
    PConst True -> NNFAnd []
    PConst False -> NNFOr []
    PLit a -> NNFLit True a
    PAnd fs -> NNFAnd $ map propToNNF fs
    POr fs -> NNFOr $ map propToNNF fs
    PNot (PConst c) -> propToNNF $ PConst $ not c
    PNot (PLit a) -> NNFLit False a
    PNot (PNot f) -> propToNNF f
    PNot (PAnd fs) -> NNFOr $ map (propToNNF . PNot) fs
    PNot (POr fs) -> NNFAnd $ map (propToNNF . PNot) fs

nnfToProp :: NNF a -> Prop a
nnfToProp =
  \case
    NNFLit True a -> PLit a
    NNFLit False a -> PNot $ PLit a
    NNFAnd [] -> PConst True
    NNFAnd [f] -> nnfToProp f
    NNFAnd fs -> PAnd $ map nnfToProp fs
    NNFOr [] -> PConst False
    NNFOr [f] -> nnfToProp f
    NNFOr fs -> POr $ map nnfToProp fs

nnfToDNF :: NNF a -> DNF a
nnfToDNF = DNF . go
  where
    go =
      \case
        NNFLit pol a -> [[(pol, a)]]
        NNFOr fs -> concatMap go fs
        NNFAnd fs -> map concat $ distribute $ map go fs

nnfToCNF :: NNF a -> CNF a
nnfToCNF = CNF . go
  where
    go =
      \case
        NNFLit pol a -> [[(pol, a)]]
        NNFAnd fs -> concatMap go fs
        NNFOr fs -> map concat $ distribute $ map go fs

distribute :: [[a]] -> [[a]]
distribute =
  \case
    [] -> [[]]
    [xs] -> [[x] | x <- xs]
    x:xr -> map (uncurry (:)) $ listProduct x $ distribute xr

-- | 'listProduct' computes the cross-product for lists
listProduct :: [a] -> [b] -> [(a, b)]
listProduct xs =
  \case
    [] -> []
    y:yr -> map (\x -> (x, y)) xs ++ listProduct xs yr
---------------------------------------------------------------------------------------------------
