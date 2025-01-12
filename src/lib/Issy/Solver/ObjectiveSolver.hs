---------------------------------------------------------------------------------------------------
-- | 
-- Module       :   Solver.ObjectiveSolver
--
-- Implements the different solving techniques for the different types of winning conditions
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.ObjectiveSolver
  ( solve
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad (when)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import Issy.Base.SymbolicState (SymSt, get)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, generateProgram, setName)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Attractor (attractor, attractorEx, noCheck)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- Overall Solving
---------------------------------------------------------------------------------------------------
solve :: Config -> (Arena, Objective) -> IO ()
solve conf (arena, obj) = do
  conf <- pure $ setName "Solve" conf
  let init = initialLoc obj
  (res, prog) <-
    case winningCond obj of
      Reachability ls -> solveReach conf arena ls init
      Safety ls -> solveSafety conf arena ls init
      Buechi ls -> solveBuechi conf arena ls init
      CoBuechi ls -> solveCoBuechi conf arena ls init
      Parity rank -> solveParity conf arena rank init
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram conf) $ CFG.simplify conf prog >>= putStrLn . CFG.printCFG (vars arena)
    else putStrLn "Unrealizable"

---------------------------------------------------------------------------------------------------
-- Safety and reachability solving
---------------------------------------------------------------------------------------------------
solveReach :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveReach conf arena reach init = do
  lg conf ["Reachability game with target", strS (locName arena) reach]
  let stopCheck l st
        | l == init = SMT.valid conf $ inv arena init `FOL.impl` (st `get` init)
        | otherwise = pure False
  (wsys, prog) <- attractorEx conf Sys arena (Just stopCheck) $ selectInv arena reach
  lg conf ["Sys. winning region", strSt arena wsys]
  res <- SMT.valid conf $ inv arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  if res && generateProgram conf
    then do
      prog <- pure $ CFG.redirectGoal arena (invSymSt arena) prog
      prog <- pure $ CFG.setInitialCFG prog init
      return (res, prog)
    else return (res, CFG.empty)

solveSafety :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveSafety conf arena safes init = do
  lg conf ["Safety game with safe locations", strS (locName arena) safes]
  let envGoal = selectInv arena $ locations arena `Set.difference` safes
  let stopCheck l st
        | l == init = SMT.sat conf (FOL.andf [inv arena init, st `get` init])
        | otherwise = pure False
  wenv <- attractor conf Env arena (Just stopCheck) envGoal
  lg conf ["Env. winning region", strSt arena wenv]
  res <- SMT.unsat conf $ FOL.andf [inv arena init, wenv `get` init]
  lg conf ["Game realizable =>", show res]
  if res && generateProgram conf
    then do
      prog <-
        pure
          $ foldLocs (locations arena) (CFG.addUpd (SymSt.map FOL.neg wenv) arena)
          $ CFG.mkCFG
          $ Set.toList
          $ locations arena
      prog <- pure $ CFG.setInitialCFG prog init
      return (res, prog)
    else return (res, CFG.empty)

---------------------------------------------------------------------------------------------------
-- Buechi and coBuechi solving
---------------------------------------------------------------------------------------------------
solveBuechi :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveBuechi conf arena accepts init = do
  lg conf ["Game type Buechi with GF", strS (locName arena) accepts]
  (wenv, fset) <- iterBuechi conf Sys arena accepts init
  lg conf ["Winning region Env in initial location", SMTLib.toString (wenv `get` init)]
  res <- SMT.unsat conf $ FOL.andf [inv arena init, wenv `get` init]
  lg conf ["Game realizable =>", show res]
  if res && generateProgram conf
    then do
      (attr, prog) <- attractorEx conf Sys arena noCheck fset
      prog <- pure $ CFG.redirectGoal arena attr prog
      prog <- pure $ CFG.setInitialCFG prog init
      return (True, prog)
    else return (res, CFG.empty)

solveCoBuechi :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveCoBuechi conf arena stays init = do
  let rejects = locations arena `Set.difference` stays
  lg conf ["Game type coBuechi with not GF", strS (locName arena) rejects]
  (wsys, _) <- iterBuechi conf Env arena rejects init
  lg conf ["Winning region Sys in initial location", SMTLib.toString (wsys `get` init)]
  res <- SMT.valid conf $ inv arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  if res && generateProgram conf
    then do
      safeSt <- SymSt.map FOL.neg <$> attractor conf Env arena noCheck (selectInv arena rejects)
      (_, prog) <- attractorEx conf Sys arena noCheck $ SymSt.map FOL.neg safeSt
      prog <- pure $ CFG.redirectGoal arena safeSt prog
      prog <- pure $ CFG.setInitialCFG prog init
      return (True, prog)
    else return (res, CFG.empty)

iterBuechi :: Config -> Player -> Arena -> Set Loc -> Loc -> IO (SymSt, SymSt)
iterBuechi conf player arena accept init = iter (selectInv arena accept) (0 :: Word)
  where
    iter fset i = do
      lg conf ["Iteration", show i]
      lg conf ["F_i =", strSt arena fset]
      bset <- attractor conf player arena noCheck fset
      lg conf ["B_i =", strSt arena bset]
      cset <- cpreS conf player arena bset
      lg conf ["C_i =", strSt arena cset]
      wset <- attractor conf (opponent player) arena noCheck $ SymSt.map FOL.neg cset
      lg conf ["W_i+1 =", strSt arena wset]
      fset' <- SymSt.simplify conf $ fset `SymSt.difference` wset
      lg conf ["F_i+1 =", strSt arena fset']
      fp <- SymSt.implies conf fset fset'
      if fp
        then do
          lg conf ["Fixed point reaced", strSt arena fset']
          return (wset, fset)
        else do
          earlyStop <-
            case player of
              Sys -> SMT.sat conf (wset `get` init)
              Env -> SMT.valid conf (wset `get` init)
          if earlyStop
            then do
              lg conf ["Early stop reached"]
              return (wset, fset)
            else do
              lg conf ["Recursion with", strSt arena fset']
              iter fset' (i + 1)

---------------------------------------------------------------------------------------------------
-- Parity solving
---------------------------------------------------------------------------------------------------
solveParity :: Config -> Arena -> Map Loc Word -> Loc -> IO (Bool, CFG)
solveParity conf arena colors init = do
  lg conf ["Game type Parity with colors", strM (locName arena) show colors]
  (_, wsys) <- zielonka arena
  res <- SMT.valid conf $ inv arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game is realizable? ", show res]
  if res && generateProgram conf
    then error "TODO IMPLEMENT: Parity extraction"
    else return (res, CFG.empty)
  where
    colorList = Map.toList colors
    --
    maxColor :: Arena -> Word
    maxColor arena = maximum [col | (l, col) <- colorList, inv arena l /= FOL.false]
    --
    colorPlayer :: Word -> Player
    colorPlayer col
      | even col = Env
      | otherwise = Sys
    --
    playerSet Env = fst
    playerSet Sys = snd
    mkPlSet Env (wply, wopp) = (wply, wopp)
    mkPlSet Sys (wply, wopp) = (wopp, wply)
    removeFromGame symst arena = do
      newInv <- SymSt.simplify conf (invSymSt arena `SymSt.difference` symst)
      pure $ foldl (\arena l -> setInv arena l (newInv `get` l)) arena (locations arena)
    --
    zielonka :: Arena -> IO (SymSt, SymSt)
    zielonka arena
      | SymSt.null (invSymSt arena) = pure (emptySt arena, emptySt arena)
      | otherwise = do
        let color = maxColor arena
        let player = colorPlayer color
        let opp = opponent player
        let targ =
              SymSt.symSt
                (locations arena)
                (\l ->
                   if colors ! l == color
                     then inv arena l
                     else FOL.false)
        let full = invSymSt arena
        lg conf ["Parity on", strSt arena full]
        lg conf ["Parity color", show color]
        lg conf ["Parity target", strSt arena targ]
        aset <- attractor conf player arena noCheck targ
        eqiv <- SymSt.implies conf full aset
        if eqiv
          then do
            lg conf ["Parity return 0"]
            pure $ mkPlSet player (full, emptySt arena)
          else do
            arena' <- removeFromGame aset arena
            lg conf ["Parity Recurse 1"]
            winOp' <- playerSet opp <$> zielonka arena'
            winOp' <- SymSt.simplify conf winOp'
            if SymSt.null winOp'
              then do
                lg conf ["Parity return 1"]
                pure $ mkPlSet player (full, emptySt arena)
              else do
                remove <- attractor conf opp arena noCheck winOp'
                arena'' <- removeFromGame remove arena
                lg conf ["Parity Recurse 2"]
                winPl'' <- playerSet player <$> zielonka arena''
                lg conf ["Parity return 2"]
                pure $ mkPlSet player (winPl'', full `SymSt.difference` winPl'')

---------------------------------------------------------------------------------------------------
-- Helper methods
---------------------------------------------------------------------------------------------------
selectInv :: Arena -> Set Loc -> SymSt
selectInv arena locs =
  SymSt.symSt
    (locations arena)
    (\l ->
       if l `elem` locs
         then arena `inv` l
         else FOL.false)

foldLocs :: Set Loc -> (Loc -> CFG -> CFG) -> CFG -> CFG
foldLocs locs f prog = foldl (flip f) prog locs
---------------------------------------------------------------------------------------------------
