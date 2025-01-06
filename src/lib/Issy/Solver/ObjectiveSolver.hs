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
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Attractor
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- Solving
-------------------------------------------------------------------------------
solve :: Config -> (Game, Objective) -> IO ()
solve ctx (g, obj) = do
  ctx <- pure $ setName "Solve" ctx
  let init = initialLoc obj
  (res, cfg) <-
    case winningCond obj of
      Reachability ls -> solveReach ctx g ls init
      Safety ls -> solveSafety ctx g ls init
      Buechi ls -> solveBuechi ctx g ls init
      CoBuechi ls -> solveCoBuechi ctx g ls init
      Parity rank -> solveParity ctx g rank init
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram ctx) $ CFG.simplify ctx cfg >>= putStrLn . CFG.printCFG (vars g)
    else putStrLn "Unrealizable"

selectInv :: Game -> Set Loc -> SymSt
selectInv g locs =
  SymSt.symSt
    (locations g)
    (\l ->
       if l `elem` locs
         then g `inv` l
         else false)

solveReach :: Config -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveReach ctx g reach init = do
  lg ctx ["Game type reachability"]
  (a, cfg) <- attractorEx ctx Sys g $ selectInv g reach
  res <- valid ctx $ inv g init `impl` (a `get` init)
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      cfg <- pure $ CFG.redirectGoal g (invSymSt g) cfg
      cfg <- pure $ CFG.setInitialCFG cfg init
      return (res, cfg)
    else return (res, CFG.empty)

foldLocs :: Set Loc -> (Loc -> CFG -> CFG) -> CFG -> CFG
foldLocs locs f cfg = foldl (flip f) cfg locs

solveSafety :: Config -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveSafety ctx g safes init = do
  lg ctx ["Game type safety"]
  let envGoal = selectInv g $ locations g `Set.difference` safes
  a <- attractor ctx Env g envGoal
  lg ctx ["Unsafe states are", strSt g a]
  lg ctx ["Initial formula is", smtLib2 (a `get` init)]
  res <- not <$> sat ctx (andf [inv g init, a `get` init])
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      cfg <-
        pure
          $ foldLocs (locations g) (CFG.addUpd (SymSt.map neg a) g)
          $ CFG.mkCFG
          $ Set.toList
          $ locations g
      cfg <- pure $ CFG.setInitialCFG cfg init
      return (res, cfg)
    else return (res, CFG.empty)

iterBuechi :: Config -> Ply -> Game -> Set Loc -> Loc -> IO (SymSt, SymSt)
iterBuechi ctx p g accept init = iter (selectInv g accept) (0 :: Word)
  where
    iter fset i = do
      lg ctx ["Iteration", show i]
      lg ctx ["F_i =", strSt g fset]
      bset <- attractor ctx p g fset
      lg ctx ["B_i =", strSt g bset]
      cset <- cpreS ctx p g bset
      lg ctx ["C_i =", strSt g cset]
      wset <- attractor ctx (opponent p) g $ SymSt.map neg cset
      lg ctx ["W_i+1 =", strSt g wset]
      fset' <- SymSt.simplify ctx $ fset `SymSt.difference` wset
      lg ctx ["F_i+1 =", strSt g fset']
      fp <- SymSt.implies ctx fset fset'
      if fp
        then do
          lg ctx ["Fixed point reaced", strSt g fset']
          return (wset, fset)
        else do
          earlyStop <-
            case p of
              Sys -> sat ctx (wset `get` init)
              Env -> valid ctx (wset `get` init)
          if earlyStop
            then do
              lg ctx ["Early stop reached"]
              return (wset, fset)
            else do
              lg ctx ["Recursion with", strSt g fset']
              iter fset' (i + 1)

solveBuechi :: Config -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveBuechi ctx g accepts init = do
  lg ctx ["Game type Buechi"]
  lg ctx ["Acceptings locations", strS (locName g) accepts]
  (wenv, fset) <- iterBuechi ctx Sys g accepts init
  res <- not <$> sat ctx (andf [inv g init, wenv `get` init])
  lg ctx ["Environment result in initial location", smtLib2 (wenv `get` init)]
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      (attr, cfg) <- attractorEx ctx Sys g fset
      cfg <- pure $ CFG.redirectGoal g attr cfg
      cfg <- pure $ CFG.setInitialCFG cfg init
      return (True, cfg)
    else return (res, CFG.empty)

solveCoBuechi :: Config -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveCoBuechi ctx g stays init = do
  let rejects = locations g `Set.difference` stays
  lg ctx ["Game type coBuechi"]
  lg ctx ["Rejecting locations", strS (locName g) rejects]
  (wsys, _) <- iterBuechi ctx Env g rejects init
  res <- valid ctx $ inv g init `impl` (wsys `get` init)
  lg ctx ["Environment result in initial location", smtLib2 (wsys `get` init)]
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      safeSt <- SymSt.map neg <$> attractor ctx Env g (selectInv g rejects)
      (_, cfg) <- attractorEx ctx Sys g $ SymSt.map neg safeSt
      cfg <- pure $ CFG.redirectGoal g safeSt cfg
      cfg <- pure $ CFG.setInitialCFG cfg init
      return (True, cfg)
    else return (res, CFG.empty)

solveParity :: Config -> Game -> Map Loc Word -> Loc -> IO (Bool, CFG)
solveParity ctx g colors init = do
  lg ctx ["Game type Parity"]
  lg ctx ["Coloring", strM (locName g) show colors]
  (_, wsys) <- zielonka g
  res <- valid ctx $ inv g init `impl` (wsys `get` init)
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then error "TODO IMPLEMENT: Parity extraction"
    else return (res, CFG.empty)
  where
    colorList = Map.toList colors
    --
    maxColor :: Game -> Word
    maxColor g = maximum [col | (l, col) <- colorList, inv g l /= false]
    --
    colorPlayer :: Word -> Ply
    colorPlayer col
      | even col = Env
      | otherwise = Sys
    --
    playerSet Env = fst
    playerSet Sys = snd
    mkPlSet Env (wply, wopp) = (wply, wopp)
    mkPlSet Sys (wply, wopp) = (wopp, wply)
    removeFromGame symst g = do
      newInv <- SymSt.simplify ctx (invSymSt g `SymSt.difference` symst)
      pure $ foldl (\g l -> setInv g l (newInv `get` l)) g (locations g)
    --
    zielonka :: Game -> IO (SymSt, SymSt)
    zielonka g
      | SymSt.null (invSymSt g) = pure (emptySt g, emptySt g)
      | otherwise = do
        let color = maxColor g
        let player = colorPlayer color
        let opp = opponent player
        let targ =
              SymSt.symSt
                (locations g)
                (\l ->
                   if colors ! l == color
                     then inv g l
                     else false)
        let full = invSymSt g
        lg ctx ["Parity on", strSt g full]
        lg ctx ["Parity color", show color]
        lg ctx ["Parity target", strSt g targ]
        aset <- attractor ctx player g targ
        eqiv <- SymSt.implies ctx full aset
        if eqiv
          then do
            lg ctx ["Parity return 0"]
            pure $ mkPlSet player (full, emptySt g)
          else do
            g' <- removeFromGame aset g
            lg ctx ["Parity Recurse 1"]
            winOp' <- playerSet opp <$> zielonka g'
            winOp' <- SymSt.simplify ctx winOp'
            if SymSt.null winOp'
              then do
                lg ctx ["Parity return 1"]
                pure $ mkPlSet player (full, emptySt g)
              else do
                remove <- attractor ctx opp g winOp'
                g'' <- removeFromGame remove g
                lg ctx ["Parity Recurse 2"]
                winPl'' <- playerSet player <$> zielonka g''
                lg ctx ["Parity return 2"]
                pure $ mkPlSet player (winPl'', full `SymSt.difference` winPl'')
-------------------------------------------------------------------------------
