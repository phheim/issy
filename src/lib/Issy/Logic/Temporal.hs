{-# LANGUAGE LambdaCase #-}

module Issy.Logic.Temporal
  ( BOp(..)
  , UOp(..)
  , Formula(..)
  , next
  , globally
  , eventually
  , atoms
  , isSafety
  , isTemporalBounded
  , toLTLStr
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

data BOp
  = Until
  | WeakUntil
  | Release
  deriving (Eq, Ord, Show)

data UOp
  = Next
  | Globally
  | Eventually
  deriving (Eq, Ord, Show)

data Formula a
  = Atom a
  | And [Formula a]
  | Or [Formula a]
  | Not (Formula a)
  -- Temporal operators
  | UExp UOp (Formula a)
  | BExp BOp (Formula a) (Formula a)
  deriving (Eq, Ord, Show)

isTemporalBounded :: Formula a -> Bool
isTemporalBounded =
  \case
    Atom _ -> True
    And fs -> all isTemporalBounded fs
    Or fs -> all isTemporalBounded fs
    Not f -> isTemporalBounded f
    UExp Next f -> isTemporalBounded f
    UExp _ _ -> False
    BExp {} -> False

isSafety :: Formula a -> Bool
isSafety =
  \case
    And fs -> all isSafety fs
    Or fs -> all isSafety fs
    UExp Globally f -> isSafety f
    UExp Next f -> isSafety f
    BExp WeakUntil f g -> isSafety f && isSafety g
    BExp Release f g -> isSafety f && isSafety g
    f -> isTemporalBounded f

atoms :: Ord a => Formula a -> Set a
atoms =
  \case
    Atom atom -> Set.singleton atom
    And fs -> Set.unions $ map atoms fs
    Or fs -> Set.unions $ map atoms fs
    Not f -> atoms f
    UExp _ f -> atoms f
    BExp _ f g -> atoms f `Set.union` atoms g

toLTLStr :: (a -> String) -> Formula a -> String
toLTLStr ap2str = go
  where
    go =
      \case
        Atom atom -> ap2str atom
        And fs -> nop "&" "true" $ map go fs
        Or fs -> nop "|" "false" $ map go fs
        Not f -> "(! " ++ go f ++ ")"
        UExp op f -> "(" ++ uop2str op ++ " " ++ go f ++ ")"
        BExp op f g -> "(" ++ go f ++ " " ++ bop2str op ++ " " ++ go g ++ ")"
     --
    nop _ neut [] = neut
    nop op _ (f:fr) = "(" ++ f ++ concatMap (\g -> " " ++ op ++ " " ++ g) fr ++ ")"
     -- 
    bop2str =
      \case
        Until -> "U"
        WeakUntil -> "W"
        Release -> "R"
     --
    uop2str =
      \case
        Next -> "X"
        Globally -> "G"
        Eventually -> "F"

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------
next :: Formula a -> Formula a
next = UExp Next

globally :: Formula a -> Formula a
globally = UExp Globally

eventually :: Formula a -> Formula a
eventually = UExp Eventually
