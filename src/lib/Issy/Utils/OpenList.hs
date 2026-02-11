---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Utils.OpenList
-- Description : Simple open-list data structure for ordered types
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a simple FIFO open-list data structure for types that implement 'Ord'
-- that can be used for search algorithms.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Utils.OpenList
  ( OpenList
  , pop
  , push
  , pushOne
  , pushList
  , empty
  , fromSet
  , fromList
  ) where

---------------------------------------------------------------------------------------------------
import Data.Set (Set)
import qualified Data.Set as Set

---------------------------------------------------------------------------------------------------
-- | An open-list over types that implements 'Ord'. The list is a FIFO queue for new elements.
-- Elements that are already queue are ignored, i.e. each element appears at most once.
newtype OpenList a =
  OpenList ([a], Set a)
  deriving (Eq, Ord, Show)

-- | The empty open-list
empty :: Ord a => OpenList a
empty = OpenList ([], Set.empty)

-- | Return and remove the first element in the open-list, if the open-list is not empty
pop :: Ord a => OpenList a -> Maybe (a, OpenList a)
pop =
  \case
    OpenList ([], _) -> Nothing
    OpenList (o:or, s) -> Just (o, OpenList (or, o `Set.delete` s))

-- | Add a single element to the open-list
pushOne :: Ord a => a -> OpenList a -> OpenList a
pushOne new ol = Set.singleton new `push` ol

-- | Add a set of element to the open-list in some undefined order
push :: Ord a => Set a -> OpenList a -> OpenList a
push new (OpenList (list, set)) =
  let reallyNew = new `Set.difference` set
   in OpenList (list ++ Set.toList reallyNew, set `Set.union` reallyNew)

-- | Add a list of elements to the open-list in some undefined order
pushList :: Ord a => [a] -> OpenList a -> OpenList a
pushList = push . Set.fromList

-- | Creates an open-list from a set of elements
fromSet :: Ord a => Set a -> OpenList a
fromSet set = set `push` empty

-- | Creates an open-list from a list of elements
fromList :: Ord a => [a] -> OpenList a
fromList = foldl (flip pushOne) empty
---------------------------------------------------------------------------------------------------
