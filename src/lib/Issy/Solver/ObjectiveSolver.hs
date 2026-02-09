---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.ObjectiveSolver
-- Description : Solving of games with objectives
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements solving game with different winning conditions,like reachability,
-- Büchi, or parity conditions.
---------------------------------------------------------------------------------------------------
module Issy.Solver.ObjectiveSolver
  ( solve
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (accelerateObjective, generateProgram)
import Issy.Games.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.OuterFixPoint (accelCoBuechi)
import Issy.Solver.Attractor (SolSt(stats), attractor, attractorEx, emptySolSt, noCheck)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Statistics (Stats)
import qualified Issy.Statistics as Stats

---------------------------------------------------------------------------------------------------
-- Overall Solving
---------------------------------------------------------------------------------------------------
-- | Solve a game while collecting statistics. The boolean return value indicates if the
-- system wins, i.e. the game specification is realizable. In this case, if configured to do so
-- this methods will also extract and return a program strategy for the system player.
solve :: Config -> Stats -> (Arena, Objective) -> IO (Bool, Stats, Maybe (IO String))
solve conf stat (arena, obj) = do
  conf <- pure $ setName "Solve" conf
  let init = initialLoc obj
  let solst = emptySolSt $ registerStats stat
  (res, solst, prog) <-
    case winningCond obj of
      Reachability ls -> solveReach conf solst arena ls init
      Safety ls -> solveSafety conf solst arena ls init
      Buechi ls -> solveBuechi conf solst arena ls init
      CoBuechi ls -> solveCoBuechi conf solst arena ls init
      Parity rank -> solveParity conf solst arena rank init
  let progStr
        | res && generateProgram conf = Just $ Synt.generateProg conf init prog
        | otherwise = Nothing
  pure (res, stats solst, progStr)

registerStats :: Stats -> Stats
registerStats =
  Stats.registerCnt "Acceleration Attempts"
    . Stats.registerCnt "Acceleration Success"
    . Stats.registerCnt "Summary Applications"

---------------------------------------------------------------------------------------------------
-- Safety and reachability solving
---------------------------------------------------------------------------------------------------
solveReach :: Config -> SolSt -> Arena -> Set Loc -> Loc -> IO (Bool, SolSt, SyBo)
solveReach conf solst arena reach init = do
  lg conf ["Reachability game with target", strS (locName arena) reach]
  let fullSt = selectInv arena (locations arena)
  let reachSt = selectInv arena reach
  let stopCheck l st
        | l == init = SMT.valid conf $ dom arena init `FOL.impl` (st `get` init)
        | otherwise = pure False
  (wsys, solst, attrProg) <- attractorEx conf solst Sys arena (Just stopCheck) reachSt
  lg conf ["Sys. winning region", strSt arena wsys]
  res <- SMT.valid conf $ dom arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  let prog =
        Synt.enforceFromTo fullSt fullSt
          $ Synt.callOnSt wsys attrProg
          $ Synt.fromStayIn conf arena reachSt fullSt
  pure (res, solst, prog)

solveSafety :: Config -> SolSt -> Arena -> Set Loc -> Loc -> IO (Bool, SolSt, SyBo)
solveSafety conf solst arena safes init = do
  lg conf ["Safety game with safe locations", strS (locName arena) safes]
  let envGoal = selectInv arena $ locations arena `Set.difference` safes
  let stopCheck l st
        | l == init = SMT.sat conf (FOL.andf [dom arena init, st `get` init])
        | otherwise = pure False
  (wenv, solst) <- attractor conf solst Env arena (Just stopCheck) envGoal
  lg conf ["Env. winning region", strSt arena wenv]
  res <- SMT.unsat conf $ FOL.andf [dom arena init, wenv `get` init]
  lg conf ["Game realizable =>", show res]
  let wsys = SymSt.map FOL.neg wenv
  let prog = Synt.fromStayIn conf arena wsys wsys
  return (res, solst, prog)

---------------------------------------------------------------------------------------------------
-- Buechi and coBuechi solving
---------------------------------------------------------------------------------------------------
solveBuechi :: Config -> SolSt -> Arena -> Set Loc -> Loc -> IO (Bool, SolSt, SyBo)
solveBuechi conf solst arena accepts init = do
  lg conf ["Game type Buechi with GF", strS (locName arena) accepts]
  (wenv, solst, progSys, _) <- iterBuechi conf solst Sys arena accepts init
  lg conf ["Winning region Env in initial location", SMTLib.toString (wenv `get` init)]
  res <- SMT.unsat conf $ FOL.andf [dom arena init, wenv `get` init]
  lg conf ["Game realizable =>", show res]
  return (res, solst, progSys)

solveCoBuechi :: Config -> SolSt -> Arena -> Set Loc -> Loc -> IO (Bool, SolSt, SyBo)
solveCoBuechi conf solst arena stays init = do
  let rejects = locations arena `Set.difference` stays
  lg conf ["Game type coBuechi with not GF", strS (locName arena) rejects]
  (wsys, solst, _, progSys) <- iterBuechi conf solst Env arena rejects init
  lg conf ["Winning region Sys in initial location", SMTLib.toString (wsys `get` init)]
  res <- SMT.valid conf $ dom arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  return (res, solst, progSys)

iterBuechi :: Config -> SolSt -> Player -> Arena -> Set Loc -> Loc -> IO (SymSt, SolSt, SyBo, SyBo)
iterBuechi conf solst player arena accept init =
  iter solst (selectInv arena accept) (0 :: Word) Synt.empty
  where
    iter solst fset i progOp = do
      lg conf ["Iteration", show i]
      lg conf ["F_i =", strSt arena fset]
      (bset, solst, progReachF) <- attractorEx conf solst player arena noCheck fset
      -- Extraction
      let progPlayer = Synt.callOnSt bset progReachF $ Synt.fromStayIn conf arena fset bset
      progOp <-
        pure
          $ if i == 0
              then Synt.fromStayIn conf arena (SymSt.map FOL.neg fset) (SymSt.map FOL.neg fset)
              else progOp
      --
      lg conf ["B_i =", strSt arena bset]
      cset <- SymSt.simplify conf $ cpreS player arena bset
      lg conf ["C_i =", strSt arena cset]
      (wset, solst, subProg) <-
        attractorEx conf solst (opponent player) arena noCheck $ SymSt.map FOL.neg cset
      lg conf ["W_i+1 =", strSt arena wset]
      -- Extraction
      progOp <-
        pure
          $ Synt.callOnSt wset subProg
          $ Synt.enforceFromTo (SymSt.map FOL.neg cset) (SymSt.map FOL.neg fset) progOp
      -- Potential outer fixpoint acceleration
      (wset, progOp) <-
        if accelerateObjective conf
          then do
            fset' <- SymSt.simplify conf $ fset `SymSt.difference` wset
            flocs <- Set.fromList . map fst <$> filterM (SMT.sat conf . snd) (SymSt.toList fset')
            foldM
              (\(wset, progOp) loc -> do
                 (wsetAccel, subProg) <- accelCoBuechi conf player arena loc fset' wset
                 success <- SMT.sat conf $ FOL.andf [wsetAccel, FOL.neg (get wset loc)]
                 if success
                   then do
                     lg conf ["Buechi acceleration succeeded"]
                     wset <- set wset loc <$> SMT.simplify conf (FOL.orf [get wset loc, wsetAccel])
                     pure (wset, Synt.callOnSt wset subProg progOp)
                   else do
                     lg conf ["Buechi acceleration failed"]
                     pure (wset, progOp))
              (wset, progOp)
              flocs
          else pure (wset, progOp)
      --
      fset' <- SymSt.simplify conf $ fset `SymSt.difference` wset
      lg conf ["F_i+1 =", strSt arena fset']
      fp <- SymSt.implies conf fset fset'
      if fp
        then do
          lg conf ["Fixed point reached", strSt arena fset']
          return (wset, solst, progPlayer, progOp)
        else do
          earlyStop <-
            case player of
              Sys -> SMT.sat conf (wset `get` init)
              Env -> SMT.valid conf (wset `get` init)
          if earlyStop
            then do
              lg conf ["Early stop reached"]
              return (wset, solst, progPlayer, progOp)
            else do
              lg conf ["Recursion with", strSt arena fset']
              iter solst fset' (i + 1) progOp

---------------------------------------------------------------------------------------------------
-- Parity solving
---------------------------------------------------------------------------------------------------
solveParity :: Config -> SolSt -> Arena -> Map Loc Word -> Loc -> IO (Bool, SolSt, SyBo)
solveParity conf solst arena colors init = do
  lg conf ["Game type Parity with colors", strM (locName arena) show colors]
  (_, (wsys, prog), solst) <- zielonka solst arena
  lg conf ["Winning region Sys", strSt arena wsys]
  res <- SMT.valid conf $ dom arena init `FOL.impl` (wsys `get` init)
  lg conf ["Game realizable =>", show res]
  pure (res, solst, prog)
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
    playerSet Env (env, sys, solst) = (env, sys, solst)
    playerSet Sys (env, sys, solst) = (sys, env, solst)
    mkPlSet Env (wply, wopp, solst) = (wply, wopp, solst)
    mkPlSet Sys (wply, wopp, solst) = (wopp, wply, solst)
    removeFromGame player =
      case player of
        Sys -> removeAttrSys conf
        Env -> removeAttrEnv conf
    --
    zielonka :: SolSt -> Arena -> IO ((SymSt, SyBo), (SymSt, SyBo), SolSt)
    zielonka solst arena
      | SymSt.null (domSymSt arena) =
        pure ((emptySt arena, Synt.empty), (emptySt arena, Synt.empty), solst)
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
        (aset, solst, progA) <- attractorEx conf solst player arena noCheck targ
        eqiv <- SymSt.implies conf full aset
        if eqiv
          then do
            -- In this case this means that 'player' can reach the highest color
            -- for which it always win from every, therefore it wins everyhwere.
            lg conf ["Parity return:", show player, "wins everywhere"]
            let prog = Synt.callOnSt full progA $ Synt.fromStayIn conf arena targ full
            pure $ mkPlSet player ((full, prog), (emptySt arena, Synt.empty), solst)
          else do
            arena' <- removeFromGame player aset arena
            lg conf ["Zielonka first recursion"]
            ((winPl, progP1), (winOp, progO1), solst) <- playerSet player <$> zielonka solst arena'
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
                pure $ mkPlSet player ((full, prog), (emptySt arena, Synt.empty), solst)
              else do
                (remove, solst, progOR) <- attractorEx conf solst opp arena noCheck winOp
                arena'' <- removeFromGame opp remove arena
                lg conf ["Zielonka second recursion"]
                ((winPl'', progP2), (winOp'', progO2), solst) <-
                  playerSet player <$> zielonka solst arena''
                lg conf ["Parity return final"]
                -- Now we construct both strategies, for the player and the opponen as both
                -- win on some part of the game
                -- - Opponent, wins if either it goes into the first subgame and wins there or win in the remaining game
                -- - Player, winf if it wins in the remaining game
                let progO = Synt.callOnSt winOp'' progO2 $ Synt.callOnSt remove progOR progO1
                pure
                  $ mkPlSet
                      player
                      ((winPl'', progP2), (full `SymSt.difference` winPl'', progO), solst)

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
