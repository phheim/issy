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
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Statistics (Stats)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- Overall Solving
---------------------------------------------------------------------------------------------------
solve :: Config -> Stats -> (Arena, Objective) -> IO (Bool, Stats, Maybe (IO String))
solve conf stats (arena, obj) = do
  conf <- pure $ setName "Solve" conf
  let init = initialLoc obj
  (res, stats, prog) <-
    case winningCond obj of
      Reachability ls -> solveReach conf stats arena ls init
      Safety ls -> solveSafety conf stats arena ls init
      Buechi ls -> solveBuechi conf stats arena ls init
      CoBuechi ls -> solveCoBuechi conf stats arena ls init
      Parity rank -> solveParity conf stats arena rank init
  let progStr
        | res && generateProgram conf = Just $ Synt.extractProg conf init prog
        | otherwise = Nothing
  pure (res, stats, progStr)

---------------------------------------------------------------------------------------------------
-- Safety and reachability solving
---------------------------------------------------------------------------------------------------
solveReach :: Config -> Stats -> Arena -> Set Loc -> Loc -> IO (Bool, Stats, SyBo)
solveReach conf stats arena reach init = do
  lg conf ["Reachability game with target", strS (locName arena) reach]
  let fullSt = selectInv arena (locations arena)
  let reachSt = selectInv arena reach
  let stopCheck l st
        | l == init = SMT.valid conf $ dom arena init `FOL.impl` (st `get` init)
        | otherwise = pure False
  (wsys, stats, attrProg) <- attractorEx conf stats Sys arena (Just stopCheck) reachSt
  lg conf ["Sys. winning region", strSt arena wsys]
  res <- SMT.valid conf $ dom arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  let prog =
        Synt.enforceFromTo fullSt fullSt
          $ Synt.callOnSt wsys attrProg
          $ Synt.fromStayIn conf arena reachSt fullSt
  pure (res, stats, prog)

solveSafety :: Config -> Stats -> Arena -> Set Loc -> Loc -> IO (Bool, Stats, SyBo)
solveSafety conf stats arena safes init = do
  lg conf ["Safety game with safe locations", strS (locName arena) safes]
  let envGoal = selectInv arena $ locations arena `Set.difference` safes
  let stopCheck l st
        | l == init = SMT.sat conf (FOL.andf [dom arena init, st `get` init])
        | otherwise = pure False
  (wenv, stats) <- attractor conf stats Env arena (Just stopCheck) envGoal
  lg conf ["Env. winning region", strSt arena wenv]
  res <- SMT.unsat conf $ FOL.andf [dom arena init, wenv `get` init]
  lg conf ["Game realizable =>", show res]
  let wsys = SymSt.map FOL.neg wenv
  let prog = Synt.fromStayIn conf arena wsys wsys
  return (res, stats, prog)

---------------------------------------------------------------------------------------------------
-- Buechi and coBuechi solving
---------------------------------------------------------------------------------------------------
solveBuechi :: Config -> Stats -> Arena -> Set Loc -> Loc -> IO (Bool, Stats, SyBo)
solveBuechi conf stats arena accepts init = do
  lg conf ["Game type Buechi with GF", strS (locName arena) accepts]
  (wenv, stats, progSys, _) <- iterBuechi conf stats Sys arena accepts init
  lg conf ["Winning region Env in initial location", SMTLib.toString (wenv `get` init)]
  res <- SMT.unsat conf $ FOL.andf [dom arena init, wenv `get` init]
  lg conf ["Game realizable =>", show res]
  return (res, stats, progSys)

solveCoBuechi :: Config -> Stats -> Arena -> Set Loc -> Loc -> IO (Bool, Stats, SyBo)
solveCoBuechi conf stats arena stays init = do
  let rejects = locations arena `Set.difference` stays
  lg conf ["Game type coBuechi with not GF", strS (locName arena) rejects]
  (wsys, stats, _, progSys) <- iterBuechi conf stats Env arena rejects init
  lg conf ["Winning region Sys in initial location", SMTLib.toString (wsys `get` init)]
  res <- SMT.valid conf $ dom arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  return (res, stats, progSys)

iterBuechi :: Config -> Stats -> Player -> Arena -> Set Loc -> Loc -> IO (SymSt, Stats, SyBo, SyBo)
iterBuechi conf stats player arena accept init =
  iter stats (selectInv arena accept) (0 :: Word) Synt.empty
  where
    iter stats fset i progOp = do
      lg conf ["Iteration", show i]
      lg conf ["F_i =", strSt arena fset]
      (bset, stats, progReachF) <- attractorEx conf stats player arena noCheck fset
      -- Extraction
      let progPlayer = Synt.callOnSt bset progReachF $ Synt.fromStayIn conf arena fset bset
      progOp <-
        pure
          $ if i == 0
              then Synt.fromStayIn conf arena (SymSt.map FOL.neg fset) (SymSt.map FOL.neg fset)
              else progOp
      --
      lg conf ["B_i =", strSt arena bset]
      cset <- cpreS conf player arena bset
      lg conf ["C_i =", strSt arena cset]
      (wset, stats, subProg) <-
        attractorEx conf stats (opponent player) arena noCheck $ SymSt.map FOL.neg cset
      lg conf ["W_i+1 =", strSt arena wset]
      -- Extraction 
      progOp <-
        pure
          $ Synt.callOnSt wset subProg
          $ Synt.enforceFromTo (SymSt.map FOL.neg cset) (SymSt.map FOL.neg fset) progOp
      -- 
      fset' <- SymSt.simplify conf $ fset `SymSt.difference` wset
      lg conf ["F_i+1 =", strSt arena fset']
      fp <- SymSt.implies conf fset fset'
      if fp
        then do
          lg conf ["Fixed point reached", strSt arena fset']
          return (wset, stats, progPlayer, progOp)
        else do
          earlyStop <-
            case player of
              Sys -> SMT.sat conf (wset `get` init)
              Env -> SMT.valid conf (wset `get` init)
          if earlyStop
            then do
              lg conf ["Early stop reached"]
              return (wset, stats, progPlayer, progOp)
            else do
              lg conf ["Recursion with", strSt arena fset']
              iter stats fset' (i + 1) progOp

---------------------------------------------------------------------------------------------------
-- Parity solving
---------------------------------------------------------------------------------------------------
solveParity :: Config -> Stats -> Arena -> Map Loc Word -> Loc -> IO (Bool, Stats, SyBo)
solveParity conf stats arena colors init = do
  lg conf ["Game type Parity with colors", strM (locName arena) show colors]
  (_, (wsys, prog), stats) <- zielonka stats arena
  lg conf ["Winning region Sys", strSt arena wsys]
  res <- SMT.valid conf $ dom arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  pure (res, stats, prog)
  where
    colorList = Map.toList colors
    --
    maxColor :: Arena -> Word
    maxColor arena = maximum [col | (l, col) <- colorList, dom arena l /= FOL.false]
    --
    colorPlayer :: Word -> Player
    colorPlayer col
      | even col = Env
      | otherwise = Sys
    --
    playerSet Env (env, sys, stats) = (env, sys, stats)
    playerSet Sys (env, sys, stats) = (sys, env, stats)
    mkPlSet Env (wply, wopp, stats) = (wply, wopp, stats)
    mkPlSet Sys (wply, wopp, stats) = (wopp, wply, stats)
    removeFromGame player =
      case player of
        Sys -> removeAttrSys conf
        Env -> removeAttrEnv conf
    --
    zielonka :: Stats -> Arena -> IO ((SymSt, SyBo), (SymSt, SyBo), Stats)
    zielonka stats arena
      | SymSt.null (domSymSt arena) =
        pure ((emptySt arena, Synt.empty), (emptySt arena, Synt.empty), stats)
      | otherwise = do
        let color = maxColor arena
        let player = colorPlayer color
        let opp = opponent player
        let targ =
              SymSt.symSt
                (locations arena)
                (\l ->
                   if colors ! l == color
                     then dom arena l
                     else FOL.false)
        let full = domSymSt arena
        lg conf ["Parity for", show player, "with color", show color]
        lg conf ["Parity arena", strSt arena full]
        lg conf ["Parity target", strSt arena targ]
        (aset, stats, progA) <- attractorEx conf stats player arena noCheck targ
        eqiv <- SymSt.implies conf full aset
        if eqiv
          then do
            -- In this case this means that 'player' can reach the highest color
            -- for which it always win from every, therefore it wins everyhwere.
            lg conf ["Parity return:", show player, "wins everywhere"]
            let prog = Synt.callOnSt full progA $ Synt.fromStayIn conf arena targ full
            pure $ mkPlSet player ((full, prog), (emptySt arena, Synt.empty), stats)
          else do
            arena' <- removeFromGame player aset arena
            lg conf ["Zielonka first recursion"]
            ((winPl, progP1), (winOp, progO1), stats) <- playerSet player <$> zielonka stats arena'
            lg conf ["Again in", strSt arena full]
            winOp <- SymSt.simplify conf winOp
            if SymSt.null winOp
              then do
                -- In this case either 'player' player can win from everywhere where it cannot 
                -- reach the highest color. Hence it either reaches it or it wins and wins
                -- therefore everywhere.
                lg conf ["Parity return: ", show player, "reaches maxcolor or wins in subgame"]
                let prog =
                      Synt.callOnSt winPl progP1
                        $ Synt.callOnSt aset progA
                        $ Synt.fromStayIn conf arena targ full
                pure $ mkPlSet player ((full, prog), (emptySt arena, Synt.empty), stats)
              else do
                (remove, stats, progOR) <- attractorEx conf stats opp arena noCheck winOp
                arena'' <- removeFromGame opp remove arena
                lg conf ["Zielonka second recursion"]
                ((winPl'', progP2), (winOp'', progO2), stats) <-
                  playerSet player <$> zielonka stats arena''
                lg conf ["Parity return final"]
                -- Now we construct both strategies, for the player and the opponen as both
                -- win on some part of the game
                -- - Opponent, wins if either it goes into the first subgame and wins there or win in the remaining game
                -- - Player, winf if it wins in the remaining game
                let progO = Synt.callOnSt winOp'' progO2 $ Synt.callOnSt remove progOR progO1
                pure
                  $ mkPlSet
                      player
                      ((winPl'', progP2), (full `SymSt.difference` winPl'', progO), stats)

---------------------------------------------------------------------------------------------------
-- Helper methods
---------------------------------------------------------------------------------------------------
selectInv :: Arena -> Set Loc -> SymSt
selectInv arena locs =
  SymSt.symSt
    (locations arena)
    (\l ->
       if l `elem` locs
         then dom arena l
         else FOL.false)
---------------------------------------------------------------------------------------------------
