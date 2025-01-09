-------------------------------------------------------------------------------
module Issy.Solver.Acceleration
  ( accelReach
  , canAccel
  ) where

-------------------------------------------------------------------------------
import Issy.Base.SymbolicState (SymSt)
import Issy.Config (Config, ufAcceleration)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Solver.Acceleration.MDAcceleration as MDAcc (accelReach)
import qualified Issy.Solver.Acceleration.UFLAcceleration as UFLAcc (accelReach)
import Issy.Solver.ControlFlowGraph (CFG)
import Issy.Solver.GameInterface

-------------------------------------------------------------------------------
-- TODO: Replace limit by more abstract limiting state, that is tracking over time!
accelReach :: Config -> Int -> Player -> Arena -> Loc -> SymSt -> IO (Term, CFG)
accelReach conf
  | ufAcceleration conf = UFLAcc.accelReach conf
  | otherwise = MDAcc.accelReach conf

-------------------------------------------------------------------------------
canAccel :: Arena -> Loc -> Bool
canAccel arena l =
  any (\v -> FOL.isNumber (sortOf arena v) && not (boundedVar arena v)) (stateVars arena)
    && (arena `cyclicIn` l)
-------------------------------------------------------------------------------
