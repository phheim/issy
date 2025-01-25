module Issy.Solver.Acceleration.LoopScenario
  ( loopScenario
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra (allM, justOn)
import Issy.Utils.Logging

-------------------------------------------------------------------------------
loopScenario ::
     Config -> Heur -> Arena -> Loc -> SymSt -> Symbol -> IO (Arena, Loc, Loc, SymSt, Term, SyBo)
loopScenario conf heur arena loc target prime = do
  let (loopAr, loc') = loopArena arena loc
  let subs = subArena heur loopAr (loc, loc')
  lg conf ["Loop Scenario on", strS (locName loopAr) subs]
  (loopAr, oldToNew) <- pure $ inducedSubArena loopAr subs
  loc <- pure $ oldToNew loc
  loc' <- pure $ oldToNew loc'
  let loopTarget = SymSt.symSt (locations loopAr) (const FOL.false)
  loopTarget <-
    pure
      $ foldl
          (\st oldloc ->
             if oldToNew oldloc == loc'
               then st
               else set st (oldToNew oldloc) (target `get` oldloc))
          loopTarget
          subs
  indeps <- independentProgVars conf loopAr
  lg conf ["Independent state variables", strS id indeps]
  (loopTarget, fixedInv) <- accTarget conf loopAr loc indeps loopTarget
  let newToOld =
        Map.fromList
          $ mapMaybe (\old -> justOn (old `elem` subs) (oldToNew old, old))
          $ Set.toList
          $ locations arena
  let prog = Synt.returnOn loopTarget $ Synt.loopSyBo conf loopAr loc loc' prime newToOld
  pure (loopAr, loc, loc', loopTarget, fixedInv, prog)

accTarget :: Config -> Arena -> Loc -> Set Symbol -> SymSt -> IO (SymSt, Term)
accTarget conf arena loc indeps st = do
  let deps = Vars.stateVars (vars arena) `Set.difference` indeps
  fixedInv <- SMT.simplify conf $ FOL.exists (Set.toList deps) $ get st loc
  let st' = SymSt.map (\phi -> FOL.forAll (Set.toList indeps) (fixedInv `FOL.impl` phi)) st
  lg conf ["Guess fixed invariant", SMTLib.toString fixedInv]
  st' <- SymSt.simplify conf st'
  lg conf ["Guess new target", strSt arena st']
  checkImpl <-
    allM
      (\l -> SMT.valid conf (FOL.andf [st' `get` l, fixedInv] `FOL.impl` get st l))
      (SymSt.locations st)
  checkSat <- SMT.sat conf $ st' `get` loc
  if checkImpl && checkSat
    then do
      lg conf ["Guessing fixed invariant succeeded"]
      pure (st', fixedInv)
    else do
      lg conf ["Guessing fixed invariant failed"]
      pure (st, FOL.true)

-- The choosen sub-arena should contain the sucessors of 
-- the accelerated location and all locations that are 
-- on a (simple) path of lenght smaller equal the bound 
-- form loc to loc'
subArena :: Heur -> Arena -> (Loc, Loc) -> Set Loc
subArena heur loopArena (loc, loc') =
  let bound = H.loopArenaSize heur
      forwDist = distances (Just bound) (succs loopArena) loc
      backDist = distances (Just bound) (preds loopArena) loc'
      minPath = Map.intersectionWith (+) forwDist backDist
      pathInc = Map.keysSet $ Map.filter (<= bound) minPath
      succ
        | H.loopArenaIncludeSucc heur = succs loopArena loc
        | otherwise = Set.empty
   in pathInc `Set.union` Set.fromList [loc, loc'] `Set.union` succ

distances :: Ord a => Maybe Int -> (a -> Set a) -> a -> Map a Int
distances bound next init = go 0 (Set.singleton init) $ Map.singleton init 0
  where
    go depth last acc
      | null last = acc
      | bound == Just depth = acc
      | otherwise =
        let new = Set.unions (Set.map next last) `Set.difference` Map.keysSet acc
         in go (depth + 1) new $ foldr (\l -> Map.insert l (depth + 1)) acc new
-------------------------------------------------------------------------------
