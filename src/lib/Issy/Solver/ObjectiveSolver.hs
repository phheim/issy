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
  , solveCache
  ) where

-------------------------------------------------------------------------------
import Control.Monad (when)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set, difference)
import qualified Data.Set as Set

import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import Issy.Base.SymbolicState
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL
import Issy.Logic.SMT (sat, valid)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Attractor
import Issy.Solver.ControlFlowGraph
import Issy.Solver.GameInterface (Game, Loc, inv, locName, locations, setInv)
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
      Reachability ls -> solveReach ctx [] g ls init
      Safety ls -> solveSafety ctx [] g ls init
      Buechi ls -> solveBuechi ctx [] g ls init
      CoBuechi ls -> solveCoBuechi ctx [] g ls init
      Parity rank -> solveParity ctx [] g rank init
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram ctx) (process ctx cfg >>= putStrLn . printCFG g)
    else putStrLn "Unrealizable"

solveCache :: Config -> Cache -> (Game, Objective) -> IO Bool
solveCache ctx cache (g, obj) = do
  ctx <- pure $ setName "SolveCache" ctx
  ctx <- pure $ ctx {generateProgram = False}
  let init = initialLoc obj
  (res, _) <-
    case winningCond obj of
      Reachability ls -> solveReach ctx cache g ls init
      Safety ls -> solveSafety ctx cache g ls init
      Buechi ls -> solveBuechi ctx cache g ls init
      CoBuechi ls -> solveCoBuechi ctx cache g ls init
      Parity rank -> solveParity ctx cache g rank init
  return res

selectInv :: Game -> Set Loc -> SymSt
selectInv g locs =
  symSt
    (locations g)
    (\l ->
       if l `elem` locs
         then g `inv` l
         else false)

solveReach :: Config -> Cache -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveReach ctx cache g reach init = do
  lg ctx ["Game type reachability"]
  (a, cfg) <- attractorEx ctx cache Sys g (selectInv g reach)
  res <- valid ctx (a `get` init)
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      cfg <- pure $ redirectGoal g (invSymSt g) cfg
      cfg <- pure $ setInitialCFG cfg init
      return (res, cfg)
    else return (res, emptyCFG)

foldLocs :: Set Loc -> (Loc -> CFG -> CFG) -> CFG -> CFG
foldLocs locs f cfg = foldl (flip f) cfg locs

solveSafety :: Config -> Cache -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveSafety ctx cache g safes init = do
  lg ctx ["Game type safety"]
  let envGoal = selectInv g (locations g `difference` safes)
  a <- attractorCache ctx Env g cache envGoal
  lg ctx ["Unsafe states are", lgS g a]
  lg ctx ["Initial formula is", smtLib2 (a `get` init)]
  res <- not <$> sat ctx (a `get` init)
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      cfg <-
        pure $ foldLocs (locations g) (addUpd (mapSymSt neg a) g) (mkCFG (Set.toList (locations g)))
      cfg <- pure $ setInitialCFG cfg init
      return (res, cfg)
    else return (res, emptyCFG)

iterBuechi :: Config -> Cache -> Ply -> Game -> Set Loc -> Loc -> IO (SymSt, SymSt)
iterBuechi ctx cache p g accept init = iter (selectInv g accept) (0 :: Word)
  where
    iter fset i = do
      lg ctx ["Iteration", show i]
      lg ctx ["F_i =", lgS g fset]
      bset <- attractorCache ctx p g cache fset
      lg ctx ["B_i =", lgS g bset]
      cset <- cpreS ctx p g bset
      lg ctx ["C_i =", lgS g cset]
      wset <- attractorCache ctx (opponent p) g cache (mapSymSt neg cset)
      lg ctx ["W_i+1 =", lgS g wset]
      fset' <- simplifySymSt ctx (fset `differenceS` wset)
      lg ctx ["F_i+1 =", lgS g fset']
      fp <- impliesS ctx fset fset'
      if fp
        then do
          lg ctx ["Fixed point reaced", lgS g fset']
          return (wset, fset)
        else do
          earlyStop <-
            case p of
              Sys -> sat ctx (wset `get` init)
              Env -> valid ctx (wset `get` init)
          if False && earlyStop -- TODO FIXME what does this even do?
            then do
              lg ctx ["Early stop"]
              return (wset, fset)
            else do
              lg ctx ["Recursion with", lgS g fset']
              iter fset' (i + 1)

solveBuechi :: Config -> Cache -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveBuechi ctx cache g accepts init = do
  lg ctx ["Game type Buechi"]
  lg ctx ["Acceptings locations", strS (locName g) accepts]
  (wenv, fset) <- iterBuechi ctx cache Sys g accepts init
  res <- not <$> sat ctx (wenv `get` init)
  lg ctx ["Environment result in initial location", smtLib2 (wenv `get` init)]
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then do
      (attr, cfg) <- attractorEx ctx cache Sys g fset
      cfg <- pure $ redirectGoal g attr cfg
      cfg <- pure $ setInitialCFG cfg init
      return (True, cfg)
    else return (res, emptyCFG)

solveCoBuechi :: Config -> Cache -> Game -> Set Loc -> Loc -> IO (Bool, CFG)
solveCoBuechi ctx cache g stays init = do
  let rejects = locations g `difference` stays
  lg ctx ["Game type coBuechi"]
  lg ctx ["Rejecting locations", strS (locName g) rejects]
  (wsys, _) <- iterBuechi ctx cache Env g rejects init
  res <- valid ctx (wsys `get` init)
  lg ctx ["Environment result in initial location", smtLib2 (wsys `get` init)]
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then error "TODO IMPLEMENT: coBüchi extraction"
    else return (res, emptyCFG)

solveParity :: Config -> Cache -> Game -> Map Loc Word -> Loc -> IO (Bool, CFG)
solveParity ctx cache g colors init
    -- TODO: add logging
 = do
  lg ctx ["Game type Parity"]
  lg ctx ["Coloring", strM (locName g) show colors]
  (_, wsys) <- zielonka g
  res <- valid ctx (wsys `get` init)
  lg ctx ["Game is realizable? ", show res]
  if res && generateProgram ctx
    then error "TODO IMPLEMENT: Parity extraction"
    else return (res, emptyCFG)
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
      newInv <- simplifySymSt ctx (invSymSt g `differenceS` symst)
      pure $ foldl (\g l -> setInv g l (newInv `get` l)) g (locations g)
    --
    zielonka :: Game -> IO (SymSt, SymSt)
    zielonka g
     -- TODO: Check that this is really needed
      | isEmptySt (invSymSt g) = pure (emptySt g, emptySt g)
      | otherwise = do
        let color = maxColor g
        let player = colorPlayer color
        let opp = opponent player
        let targ =
              symSt
                (locations g)
                (\l ->
                   if colors ! l == color
                     then inv g l
                     else false)
        let full = invSymSt g
        lg ctx ["Parity on", lgS g full]
        lg ctx ["Parity color", show color]
        lg ctx ["Parity target", lgS g targ]
        aset <- attractorCache ctx player g cache targ
        eqiv <- impliesS ctx full aset
        if eqiv
          then do
            lg ctx ["Parity return 0"]
            pure $ mkPlSet player (full, emptySt g)
          else do
            g' <- removeFromGame aset g
            lg ctx ["Parity Recurse 1"]
            winOp' <- playerSet opp <$> zielonka g'
            winOp' <- simplifySymSt ctx winOp'
            if isEmptySt winOp'
              then do
                lg ctx ["Parity return 1"]
                pure $ mkPlSet player (full, emptySt g)
              else do
                remove <- attractorCache ctx opp g cache winOp'
                g'' <- removeFromGame remove g
                lg ctx ["Parity Recurse 2"]
                winPl'' <- playerSet player <$> zielonka g''
                lg ctx ["Parity return 2"]
                pure $ mkPlSet player (winPl'', full `differenceS` winPl'')

-------------------------------------------------------------------------------
-- Notions
-------------------------------------------------------------------------------
invSymSt :: Game -> SymSt
invSymSt g = symSt (locations g) (inv g)

emptySt :: Game -> SymSt
emptySt g = symSt (locations g) (const false)

-- TODO: Rename
lgS :: Game -> SymSt -> String
lgS = SymSt.toString . locName
-------------------------------------------------------------------------------
