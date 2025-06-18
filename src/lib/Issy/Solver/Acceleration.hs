---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration
-- Description : Top-level module for attractor acceleration
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration
  ( accelReach
  , canAccel
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Base.SymbolicState (SymSt)
import Issy.Config (Config, genGeomAccel, ufAcceleration)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Solver.Acceleration.Heuristics as H
import qualified Issy.Solver.Acceleration.MDAcceleration as MDAcc (accelReach)
import qualified Issy.Solver.Acceleration.PolyhedraGeometricAccel as PoGeoA (accelReach)
import qualified Issy.Solver.Acceleration.UFLAcceleration as UFLAcc (accelReach)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)

---------------------------------------------------------------------------------------------------
-- | 'accelReach' applies a pre-configured version of attractor acceleration
accelReach :: Config -> Int -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf visits player arena =
  let heur = H.forVisits conf arena visits
   in if ufAcceleration conf
        then UFLAcc.accelReach conf heur player arena
        else if genGeomAccel conf
               then PoGeoA.accelReach conf heur player arena
               else MDAcc.accelReach conf heur player arena

---------------------------------------------------------------------------------------------------
-- | 'canAccel' check if in a given location attractor acceleration even makes sense
canAccel :: Arena -> Loc -> Bool
canAccel arena l =
  any (\v -> FOL.isNumber (sortOf arena v) && not (boundedVar arena v)) (stateVars arena)
    && (arena `cyclicIn` l)
---------------------------------------------------------------------------------------------------
