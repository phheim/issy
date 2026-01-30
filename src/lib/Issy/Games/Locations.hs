---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Games.Locations
-- Description : Encapsulated game-graph locations
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module provides an abstraction of game-graph locations. The locations are
-- provided by a type 'Loc'. These locations are always in the context of locations
-- 'Store' which is then usually a part of the game-graph. Note that locations from
-- different stores can be equal. Hence, it is up to the user to ensure that locations
-- are only used within their respective context.
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
-- | 'Loc' is a location which has to be interpreted in the context of a 'Store'.
newtype Loc =
  Loc Integer
  deriving (Eq, Ord, Show)

-- | 'Store' provides the context for a set of locations used by  a game arena
data Store = Store
  { cnt :: Integer
  , names :: Map Loc String
  } deriving (Eq, Ord, Show)

-- | 'empty' is a location 'Store' without any locations
empty :: Store
empty = Store {cnt = 0, names = Map.empty}

-- | 'toSet' returns the set of all locations in the store
toSet :: Store -> Set Loc
toSet = Set.fromList . toList

-- | 'toList' returns a list of all locations in the store
toList :: Store -> [Loc]
toList locs
  | cnt locs > 0 = map Loc [0 .. cnt locs - 1]
  | otherwise = []

-- | 'add' creates a new named location in a store
add :: Store -> String -> (Loc, Store)
add locs name =
  ( Loc (cnt locs)
  , Store {cnt = cnt locs + 1, names = Map.insert (Loc (cnt locs)) name (names locs)})

-- | 'name' returns the name of a location in a store. If the location is
-- not inside the store, this will fail.
name :: Store -> Loc -> String
name locs l =
  case names locs !? l of
    Nothing -> error $ "assert: could not find location name of " ++ show l
    Just str -> str

-- | 'toString' creates a unique string for a location in a store
-- which also includes the name
toString :: Store -> Loc -> String
toString locs (Loc n) = "l" ++ show n ++ "_" ++ name locs (Loc n)

-- | 'toNumber' turns a location into a number. As this relies on internal
-- mechanisms, this functions should be used ONLY FOR ENCODINGS
toNumber :: Loc -> Integer
toNumber (Loc n) = n
---------------------------------------------------------------------------------------------------
