---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Games.Locations
-- Description : Encapsulated game-graph locations
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Games.Locations
  ( Loc
  , Store
  , toSet
  , toList
  , add
  , name
  , toString
  , toNumber
  , empty
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

---------------------------------------------------------------------------------------------------
-- | 'Loc' is a location. Note that locations are in the context of a 'Store' which is usually
-- provided by a game arena or so. 'Loc's from different 'Store's could be equally without
-- semantically being the same.
newtype Loc =
  Loc Integer
  deriving (Eq, Ord, Show)

data Store = Store
  { cnt :: Integer
  , names :: Map Loc String
  } deriving (Eq, Ord, Show)

empty :: Store
empty = Store {cnt = 0, names = Map.empty}

toSet :: Store -> Set Loc
toSet = Set.fromList . toList

toList :: Store -> [Loc]
toList locs
  | cnt locs > 0 = map Loc [0 .. cnt locs - 1]
  | otherwise = []

add :: Store -> String -> (Loc, Store)
add locs name =
  ( Loc (cnt locs)
  , Store {cnt = cnt locs + 1, names = Map.insert (Loc (cnt locs)) name (names locs)})

name :: Store -> Loc -> String
name locs l =
  case names locs !? l of
    Nothing -> error $ "Could not find location name of " ++ show l
    Just str -> str

toString :: Store -> Loc -> String
toString locs (Loc n) = "l" ++ show n ++ "_" ++ name locs (Loc n)

toNumber :: Loc -> Integer
toNumber (Loc n) = n
---------------------------------------------------------------------------------------------------
