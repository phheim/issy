---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Games.SymbolicState
-- Description : Implementation of a symbolic state
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a symbolic states in the context of RPG / symbolic game solving.
-- A symbolic state maps each locations in an RPG or symbolic game to a first-order logic
-- formula, which represents then a set of states.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Games.SymbolicState
  ( SymSt
  , symSt
  , null
  , get
  , set
  , map
  , mapWithLoc
  , disj
  , disjS
  , difference
  , simplify
  , implies
  , locations
  , symbols
  , toList
  , toString
  ) where

-------------------------------------------------------------------------------
import Prelude hiding (map, null)

import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Config (Config)
import Issy.Games.Locations (Loc)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT (simplify, valid)
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- Symbolic state
-------------------------------------------------------------------------------
-- | The representation of a symbolic state. A symbolic state is only
-- well-defined in the context of a set of given locations usually provided
-- by some kind of symbolic arena or location store.
newtype SymSt =
  SymSt (Map Loc Term) -- assert that all location are mapped
  deriving (Eq, Ord, Show)

-- | Create a symbolic state for a set of locations.
-- It is required that that the given set of location is complete within the
-- context. Otherwise, operations on this symbolic state are undefined.
symSt :: Set Loc -> (Loc -> Term) -> SymSt
symSt locs gen = SymSt $ Map.fromSet gen locs

-- | Check if the symbolic state represent the trivial empty set, i.e. the
-- formula for all locations are syntactically false.
null :: SymSt -> Bool
null = all ((== FOL.false) . snd) . toList

-- | Get the value of the symbolic state at a given location. This location has
-- to be part of the aforementioned context.
get :: SymSt -> Loc -> Term
get (SymSt s) l = fromMaybe (error "assert: all locations should be mapped") (s !? l)

-- | Set the value of the symbolic state at a given location. This location has
-- to be part of the aforementioned context.
set :: SymSt -> Loc -> Term -> SymSt
set (SymSt s) l f = SymSt $ Map.insert l f s

-- | Map all terms in a symbolic state.
map :: (Term -> Term) -> SymSt -> SymSt
map = mapSt . Map.map

-- | Map all terms in a symbolic state with the location.
mapWithLoc :: (Loc -> Term -> Term) -> SymSt -> SymSt
mapWithLoc = mapSt . Map.mapWithKey

-- | The location-wise disjunction of two symbolic states.
disjS :: SymSt -> SymSt -> SymSt
disjS (SymSt a) b = SymSt $ Map.mapWithKey (\l f -> FOL.orf [f, b `get` l]) a

-- | The location-wise difference of two symbolic states.
difference :: SymSt -> SymSt -> SymSt
difference (SymSt a) b = SymSt $ Map.mapWithKey (\l f -> FOL.andf [f, FOL.neg (b `get` l)]) a

-- | The disjunction of a term and the value of a symbolic state at a given location.
disj :: SymSt -> Loc -> Term -> SymSt
disj s l f = set s l $ FOL.orf [f, s `get` l]

-- | Check if one symbolic state represent a subset of the other one. Note that
-- this check will invoke an SMT solver.
implies :: Config -> SymSt -> SymSt -> IO Bool
implies cfg (SymSt a) b =
  SMT.valid cfg $ FOL.andf $ (\l -> (SymSt a `get` l) `FOL.impl` (b `get` l)) <$> Map.keys a

-- | Apply simplifications to a symbolic state. This operation will invoke an SMT solver.
simplify :: Config -> SymSt -> IO SymSt
simplify cfg (SymSt s) = SymSt <$> mapM (SMT.simplify cfg) s

-- | The locations of the symbolic state.
locations :: SymSt -> [Loc]
locations = liftSt Map.keys

-- | A list representation of the symbolic state.
toList :: SymSt -> [(Loc, Term)]
toList = liftSt Map.toList

-- | All symbols that appear in the symbolic state.
symbols :: SymSt -> Set Symbol
symbols = liftSt $ Set.unions . fmap FOL.symbols . Map.elems

-- | Pretty print a symbolic state.
toString :: (Loc -> String) -> SymSt -> String
toString = liftSt . flip strM SMTLib.toString

mapSt :: (Map Loc Term -> Map Loc Term) -> SymSt -> SymSt
mapSt f (SymSt s) = SymSt $ f s

liftSt :: (Map Loc Term -> a) -> SymSt -> a
liftSt f (SymSt s) = f s
---------------------------------------------------------------------------------------------------
