---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.PolyhedraGeometricAccel
-- Description : Implementaion of the general version of geometric acceleration based on polyhedra
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.PolyhedraGeometricAccel
  ( accelReach
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, extendAcceleration, setName)
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.Acceleration.Strengthening (strengthenBool)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra (andM, orM)
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

---------------------------------------------------------------------------------------------------
-- Top-level acceleration
---------------------------------------------------------------------------------------------------
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GGeoA" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  error "TODO IMPLEMENT"

accelGAL :: Config -> Player -> Arena -> Loc -> SymSt -> Term -> Term -> IO (Term, SyBo)
accelGAL conf player arena loc reach maintain inv = error "TODO IMPLEMENT"
  where
    iter = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Attractor through loop arena
---------------------------------------------------------------------------------------------------
preCond :: Config -> Player -> Arena -> Loc -> SymSt -> (Term, Term, Term) -> Term
preCond = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Lemma Guessing based on polyhedra
---------------------------------------------------------------------------------------------------
data GenAccelLemma = GenAccelLemma
  { base :: Term
  , step :: Term
  , stay :: Term
  , conc :: Term
  }

lemmaGuess :: Config -> Heur -> Symbol -> Player -> Arena -> Term -> IO (Maybe GenAccelLemma)
lemmaGuess = error "TODO IMPLEMENT"

galUnion :: [GenAccelLemma] -> GenAccelLemma
galUnion = error "TODO IMPLEMENT"

data Polyhedron = Polyhedron
  { variables :: [Symbol]
  , conditions :: [([Term], Term)]
  }

fromPolyhedron :: Polyhedron -> GenAccelLemma
fromPolyhedron = error "TODO IMPLEMENT"

extractPolyhedra :: Term -> [(Polyhedron, Term)]
extractPolyhedra = error "TODO IMPLEMENT"

toDNF :: Term -> [[Term]]
toDNF = error "TODO IMPLEMENT"
---------------------------------------------------------------------------------------------------
