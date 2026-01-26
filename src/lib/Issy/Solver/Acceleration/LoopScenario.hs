---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Acceleration.LoopScenario
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.LoopScenario
  ( loopScenario
  , reducedLoopArena
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------------
import Issy.Prelude

import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra

-------------------------------------------------------------------------------
loopScenario ::
     Config -> Heur -> Arena -> Loc -> SymSt -> Symbol -> IO (Arena, Loc, Loc, SymSt, Term, SyBo)
loopScenario conf heur arena loc target prime = do
  (loopAr, loc, loc', subs, loopTarget, loopProg) <-
    pure $ reducedLoopArena conf heur arena loc target prime
  lg conf ["Loop Scenario on", strS (locName loopAr) subs]
  indeps <- independentProgVars conf loopAr
  lg conf ["Independent state variables", strS id indeps]
  (loopTarget, fixedInv) <- accTarget conf loopAr loc indeps loopTarget
  let prog = Synt.returnOn loopTarget loopProg
  pure (loopAr, loc, loc', loopTarget, fixedInv, prog)

-- | 'reducedLoopArena' compute a heuristically reduced sub-arena to be limited on a
-- potentially smaller part of the game. Note that you still need to
--  - set the start value in loc'
--  - return upon reaching the loop target
reducedLoopArena ::
     Config -> Heur -> Arena -> Loc -> SymSt -> Symbol -> (Arena, Loc, Loc, Set Loc, SymSt, SyBo)
reducedLoopArena conf heur arena loc target prime =
  let (rawLoopAr, rawLoc') = loopArena arena loc
      subs = subArena heur rawLoopAr (loc, rawLoc')
      (loopAr, (oldToNew, _)) = inducedSubArena rawLoopAr subs
      newLoc = oldToNew loc
      newLoc' = oldToNew rawLoc'
      loopTarget =
        foldl
          (\st oldloc ->
             if oldToNew oldloc == newLoc'
               then st
               else set st (oldToNew oldloc) (target `get` oldloc))
          (SymSt.symSt (locations loopAr) (const FOL.false))
          subs
      newToOld =
        Map.fromList
          $ mapMaybe (\old -> justOn (old `elem` subs) (oldToNew old, old))
          $ Set.toList
          $ locations arena
      loopProg = Synt.loopSyBo conf loopAr newLoc newLoc' prime newToOld
   in (loopAr, newLoc, newLoc', Set.map oldToNew subs, loopTarget, loopProg)

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
---------------------------------------------------------------------------------------------------
