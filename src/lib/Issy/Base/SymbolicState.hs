module Issy.Base.SymbolicState
  ( SymSt
  , symSt
  , get
  , set
  , disj
  , disjS
  , differenceS
  , impliesS
  , locsSymSt
  , listSymSt
  , isEmptySt
  , simplifySymSt
  , mapSymSt
  , toString
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)

import Issy.Base.Locations (Loc)
import Issy.Config (Config)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT (simplify, valid)
import qualified Issy.Printers.SMTLib as SMTLib (smtLib2)
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- Symbolic state
-------------------------------------------------------------------------------
newtype SymSt =
  SymSt (Map Loc Term) -- assert that all location are mapped
  deriving (Eq, Ord, Show)

symSt :: Set Loc -> (Loc -> Term) -> SymSt
symSt locs gen = SymSt (Map.fromSet gen locs)

get :: SymSt -> Loc -> Term
get (SymSt s) l = fromMaybe (error "Assertion: All locations should be mapped") (s !? l)

set :: SymSt -> Loc -> Term -> SymSt
set (SymSt s) l f = SymSt (Map.insert l f s)

disj :: SymSt -> Loc -> Term -> SymSt
disj s l f = set s l (FOL.orf [f, s `get` l])

disjS :: SymSt -> SymSt -> SymSt
disjS (SymSt a) b = SymSt (Map.mapWithKey (\l f -> FOL.orf [f, b `get` l]) a)

differenceS :: SymSt -> SymSt -> SymSt
differenceS (SymSt a) b = SymSt (Map.mapWithKey (\l f -> FOL.andf [f, FOL.neg (b `get` l)]) a)

impliesS :: Config -> SymSt -> SymSt -> IO Bool
impliesS cfg (SymSt a) b =
  SMT.valid cfg $ FOL.andf ((\l -> (SymSt a `get` l) `FOL.impl` (b `get` l)) <$> Map.keys a)

locsSymSt :: SymSt -> [Loc]
locsSymSt (SymSt s) = Map.keys s

listSymSt :: SymSt -> [(Loc, Term)]
listSymSt (SymSt s) = Map.toList s

isEmptySt :: SymSt -> Bool
isEmptySt = all ((== FOL.false) . snd) . listSymSt

simplifySymSt :: Config -> SymSt -> IO SymSt
simplifySymSt cfg (SymSt s) = SymSt <$> mapM (SMT.simplify cfg) s

mapSymSt :: (Term -> Term) -> SymSt -> SymSt
mapSymSt mp (SymSt s) = SymSt (fmap mp s)

toString :: (Loc -> String) -> SymSt -> String
toString locToStr (SymSt s) = strM locToStr SMTLib.smtLib2 s
