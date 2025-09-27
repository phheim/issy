{-# LANGUAGE Safe, LambdaCase #-}

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

import Data.Set (Set)
import qualified Data.Set as Set

newtype OpenList a =
  OpenList ([a], Set a)
  deriving (Eq, Ord, Show)

pop :: Ord a => OpenList a -> Maybe (a, OpenList a)
pop =
  \case
    OpenList ([], _) -> Nothing
    OpenList (o:or, s) -> Just (o, OpenList (or, o `Set.delete` s))

pushOne :: Ord a => a -> OpenList a -> OpenList a
pushOne new ol = Set.singleton new `push` ol

push :: Ord a => Set a -> OpenList a -> OpenList a
push new (OpenList (list, set)) =
  let reallyNew = new `Set.difference` set
   in OpenList (list ++ Set.toList reallyNew, set `Set.union` reallyNew)

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
