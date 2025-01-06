-------------------------------------------------------------------------------
module Issy.Solver.Acceleration
  ( accelReach
  ) where

-------------------------------------------------------------------------------
import Issy.Base.SymbolicState (SymSt)
import Issy.Config (Config)
import Issy.Logic.FOL (Term)
import qualified Issy.Solver.Acceleration.UFLAcceleration as UFLAcc (accelReach)
import Issy.Solver.ControlFlowGraph (CFG)
import Issy.Solver.GameInterface

-------------------------------------------------------------------------------
-- TODO: Replace limit by more abstract limiting state, that is tracking over time!
accelReach :: Config -> Int -> Ply -> Game -> Loc -> SymSt -> IO (Term, CFG)
accelReach = UFLAcc.accelReach
-------------------------------------------------------------------------------
