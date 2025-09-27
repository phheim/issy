{-# LANGUAGE Safe #-}

module Issy.Games.SymbolicState
  ( SymSt
  , symSt
  , get
  , set
  , disj
  , disjS
  , difference
  , implies
  , restrictTo
  , locations
  , toList
  , null
  , simplify
  , map
  , mapWithLoc
  , symbols
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
newtype SymSt =
  SymSt (Map Loc Term) -- assert that all location are mapped
  deriving (Eq, Ord, Show)

liftSt :: (Map Loc Term -> a) -> SymSt -> a
liftSt f (SymSt s) = f s

mapSt :: (Map Loc Term -> Map Loc Term) -> SymSt -> SymSt
mapSt f (SymSt s) = SymSt $ f s

symSt :: Set Loc -> (Loc -> Term) -> SymSt
symSt locs gen = SymSt $ Map.fromSet gen locs

get :: SymSt -> Loc -> Term
get (SymSt s) l = fromMaybe (error "Assertion: All locations should be mapped") (s !? l)

set :: SymSt -> Loc -> Term -> SymSt
set (SymSt s) l f = SymSt $ Map.insert l f s

disj :: SymSt -> Loc -> Term -> SymSt
disj s l f = set s l $ FOL.orf [f, s `get` l]

disjS :: SymSt -> SymSt -> SymSt
disjS (SymSt a) b = SymSt $ Map.mapWithKey (\l f -> FOL.orf [f, b `get` l]) a

difference :: SymSt -> SymSt -> SymSt
difference (SymSt a) b = SymSt $ Map.mapWithKey (\l f -> FOL.andf [f, FOL.neg (b `get` l)]) a

implies :: Config -> SymSt -> SymSt -> IO Bool
implies cfg (SymSt a) b =
  SMT.valid cfg $ FOL.andf $ (\l -> (SymSt a `get` l) `FOL.impl` (b `get` l)) <$> Map.keys a

locations :: SymSt -> [Loc]
locations = liftSt Map.keys

toList :: SymSt -> [(Loc, Term)]
toList = liftSt Map.toList

null :: SymSt -> Bool
null = all ((== FOL.false) . snd) . toList

simplify :: Config -> SymSt -> IO SymSt
simplify cfg (SymSt s) = SymSt <$> mapM (SMT.simplify cfg) s

map :: (Term -> Term) -> SymSt -> SymSt
map = mapSt . Map.map

mapWithLoc :: (Loc -> Term -> Term) -> SymSt -> SymSt
mapWithLoc = mapSt . Map.mapWithKey

toString :: (Loc -> String) -> SymSt -> String
toString = liftSt . flip strM SMTLib.toString

restrictTo :: Set Loc -> SymSt -> SymSt
restrictTo locs =
  mapSt
    $ Map.mapWithKey
        (\l v ->
           if l `elem` locs
             then v
             else FOL.false)

symbols :: SymSt -> Set Symbol
symbols = liftSt $ Set.unions . fmap FOL.symbols . Map.elems
