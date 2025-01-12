-------------------------------------------------------------------------------
-- | 
-- Module       :   Solving
--
-- 'Solving' implements the different solving techniques for the different
-- games. 
--
-------------------------------------------------------------------------------
module Issy.Solver.ObjectiveSolver
  ( solve
  ) where

-------------------------------------------------------------------------------
import Control.Monad (when)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import Issy.Base.SymbolicState (SymSt, get)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL
import Issy.Logic.SMT (sat, valid)
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Attractor
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- Solving
-------------------------------------------------------------------------------
solve :: Config -> (Arena, Objective) -> IO ()
solve cfg (arena, obj) = do
  cfg <- pure $ setName "Solve" cfg
  let init = initialLoc obj
  (res, prog) <-
    case winningCond obj of
      Reachability ls -> solveReach cfg arena ls init
      Safety ls -> solveSafety cfg arena ls init
      Buechi ls -> solveBuechi cfg arena ls init
      CoBuechi ls -> solveCoBuechi cfg arena ls init
      Parity rank -> solveParity cfg arena rank init
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram cfg) $ CFG.simplify cfg prog >>= putStrLn . CFG.printCFG (vars arena)
    else putStrLn "Unrealizable"

selectInv :: Arena -> Set Loc -> SymSt
selectInv arena locs =
  SymSt.symSt
    (locations arena)
    (\l ->
       if l `elem` locs
         then arena `inv` l
         else false)

solveReach :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveReach cfg arena reach init = do
  lg cfg ["Game type reachability"]
  let stopCheck l st
        | l == init = valid cfg $ inv arena init `impl` (st `get` init)
        | otherwise = pure False
  (a, prog) <- attractorEx cfg Sys arena (Just stopCheck) $ selectInv arena reach
  res <- valid cfg $ inv arena init `impl` (a `get` init)
  lg cfg ["Game is realizable? ", show res]
  if res && generateProgram cfg
    then do
      prog <- pure $ CFG.redirectGoal arena (invSymSt arena) prog
      prog <- pure $ CFG.setInitialCFG prog init
      return (res, prog)
    else return (res, CFG.empty)

foldLocs :: Set Loc -> (Loc -> CFG -> CFG) -> CFG -> CFG
foldLocs locs f prog = foldl (flip f) prog locs

solveSafety :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveSafety cfg arena safes init = do
  lg cfg ["Game type safety"]
  let envGoal = selectInv arena $ locations arena `Set.difference` safes
  let stopCheck l st
        | l == init = sat cfg (andf [inv arena init, st `get` init])
        | otherwise = pure False
  a <- attractor cfg Env arena (Just stopCheck) envGoal
  lg cfg ["Unsafe states are", strSt arena a]
  lg cfg ["Initial formula is", SMTLib.toString (a `get` init)]
  res <- not <$> sat cfg (andf [inv arena init, a `get` init])
  lg cfg ["Game is realizable? ", show res]
  if res && generateProgram cfg
    then do
      prog <-
        pure
          $ foldLocs (locations arena) (CFG.addUpd (SymSt.map neg a) arena)
          $ CFG.mkCFG
          $ Set.toList
          $ locations arena
      prog <- pure $ CFG.setInitialCFG prog init
      return (res, prog)
    else return (res, CFG.empty)

iterBuechi :: Config -> Player -> Arena -> Set Loc -> Loc -> IO (SymSt, SymSt)
iterBuechi cfg player arena accept init = iter (selectInv arena accept) (0 :: Word)
  where
    iter fset i = do
      lg cfg ["Iteration", show i]
      lg cfg ["F_i =", strSt arena fset]
      bset <- attractor cfg player arena noCheck fset
      lg cfg ["B_i =", strSt arena bset]
      cset <- cpreS cfg player arena bset
      lg cfg ["C_i =", strSt arena cset]
      wset <- attractor cfg (opponent player) arena noCheck $ SymSt.map neg cset
      lg cfg ["W_i+1 =", strSt arena wset]
      fset' <- SymSt.simplify cfg $ fset `SymSt.difference` wset
      lg cfg ["F_i+1 =", strSt arena fset']
      fp <- SymSt.implies cfg fset fset'
      if fp
        then do
          lg cfg ["Fixed point reaced", strSt arena fset']
          return (wset, fset)
        else do
          earlyStop <-
            case player of
              Sys -> sat cfg (wset `get` init)
              Env -> valid cfg (wset `get` init)
          if earlyStop
            then do
              lg cfg ["Early stop reached"]
              return (wset, fset)
            else do
              lg cfg ["Recursion with", strSt arena fset']
              iter fset' (i + 1)

solveBuechi :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveBuechi cfg arena accepts init = do
  lg cfg ["Game type Buechi"]
  lg cfg ["Acceptings locations", strS (locName arena) accepts]
  (wenv, fset) <- iterBuechi cfg Sys arena accepts init
  res <- not <$> sat cfg (andf [inv arena init, wenv `get` init])
  lg cfg ["Environment result in initial location", SMTLib.toString (wenv `get` init)]
  lg cfg ["Game is realizable? ", show res]
  if res && generateProgram cfg
    then do
      (attr, prog) <- attractorEx cfg Sys arena noCheck fset
      prog <- pure $ CFG.redirectGoal arena attr prog
      prog <- pure $ CFG.setInitialCFG prog init
      return (True, prog)
    else return (res, CFG.empty)

solveCoBuechi :: Config -> Arena -> Set Loc -> Loc -> IO (Bool, CFG)
solveCoBuechi cfg arena stays init = do
  let rejects = locations arena `Set.difference` stays
  lg cfg ["Game type coBuechi"]
  lg cfg ["Rejecting locations", strS (locName arena) rejects]
  (wsys, _) <- iterBuechi cfg Env arena rejects init
  res <- valid cfg $ inv arena init `impl` (wsys `get` init)
  lg cfg ["Environment result in initial location", SMTLib.toString (wsys `get` init)]
  lg cfg ["Game is realizable? ", show res]
  if res && generateProgram cfg
    then do
      safeSt <- SymSt.map neg <$> attractor cfg Env arena noCheck (selectInv arena rejects)
      (_, prog) <- attractorEx cfg Sys arena noCheck $ SymSt.map neg safeSt
      prog <- pure $ CFG.redirectGoal arena safeSt prog
      prog <- pure $ CFG.setInitialCFG prog init
      return (True, prog)
    else return (res, CFG.empty)

solveParity :: Config -> Arena -> Map Loc Word -> Loc -> IO (Bool, CFG)
solveParity cfg arena colors init = do
  lg cfg ["Game type Parity"]
  lg cfg ["Coloring", strM (locName arena) show colors]
  (_, wsys) <- zielonka arena
  res <- valid cfg $ inv arena init `impl` (wsys `get` init)
  lg cfg ["Game is realizable? ", show res]
  if res && generateProgram cfg
    then error "TODO IMPLEMENT: Parity extraction"
    else return (res, CFG.empty)
  where
    colorList = Map.toList colors
    --
    maxColor :: Arena -> Word
    maxColor arena = maximum [col | (l, col) <- colorList, inv arena l /= false]
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
      newInv <- SymSt.simplify cfg (invSymSt arena `SymSt.difference` symst)
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
                     else false)
        let full = invSymSt arena
        lg cfg ["Parity on", strSt arena full]
        lg cfg ["Parity color", show color]
        lg cfg ["Parity target", strSt arena targ]
        aset <- attractor cfg player arena noCheck targ
        eqiv <- SymSt.implies cfg full aset
        if eqiv
          then do
            lg cfg ["Parity return 0"]
            pure $ mkPlSet player (full, emptySt arena)
          else do
            arena' <- removeFromGame aset arena
            lg cfg ["Parity Recurse 1"]
            winOp' <- playerSet opp <$> zielonka arena'
            winOp' <- SymSt.simplify cfg winOp'
            if SymSt.null winOp'
              then do
                lg cfg ["Parity return 1"]
                pure $ mkPlSet player (full, emptySt arena)
              else do
                remove <- attractor cfg opp arena noCheck winOp'
                arena'' <- removeFromGame remove arena
                lg cfg ["Parity Recurse 2"]
                winPl'' <- playerSet player <$> zielonka arena''
                lg cfg ["Parity return 2"]
                pure $ mkPlSet player (winPl'', full `SymSt.difference` winPl'')
-------------------------------------------------------------------------------
