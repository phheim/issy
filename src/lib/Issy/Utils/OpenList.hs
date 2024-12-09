{-# LANGUAGE LambdaCase #-}

module Issy.Utils.OpenList
  ( OpenList
  , pop
  , push
  , pushOne
  , pushList
  , empty
  , fromSet
  , fromList
  , toSet
  , toList
  ) where

import qualified Data.Set as Set (empty, fromList, toList)
import Data.Set (Set, delete, difference, singleton, union)

newtype OpenList a =
  OpenList ([a], Set a)
 deriving (Eq, Ord, Show)

pop :: Ord a => OpenList a -> Maybe (a, OpenList a)
pop =
  \case
    OpenList ([], _) -> Nothing
    OpenList (o:or, s) -> Just (o, OpenList (or, o `delete` s))

pushOne :: Ord a => a -> OpenList a -> OpenList a
pushOne new ol = singleton new `push` ol

push :: Ord a => Set a -> OpenList a -> OpenList a
push new (OpenList (list, set)) =
  let reallyNew = new `difference` set
   in OpenList (list ++ Set.toList reallyNew, set `union` reallyNew)

pushList :: Ord a => [a] -> OpenList a -> OpenList a
pushList = push . Set.fromList

empty :: Ord a => OpenList a
empty = OpenList ([], Set.empty)

fromSet :: Ord a => Set a -> OpenList a
fromSet set = set `push` empty

fromList :: Ord a => [a] -> OpenList a
fromList = foldl (flip pushOne) empty

toSet :: Ord a => OpenList a -> Set a
toSet (OpenList (_, s)) = s

toList :: Ord a => OpenList a -> [a]
toList (OpenList (l, _)) = l
