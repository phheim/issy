---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Encoders.ToFixpoints
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

module Issy.Encoders.ToFixpoints
  ( FPSystem(..)
  , FPTerm(..)
  , FPType(..)
  , gameToFP
  ) where

import qualified Data.Map.Strict as Map
import Issy.Prelude

import Issy.Games.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import Issy.Solver.GameInterface

data FPSystem = FPSystem
  { systemTerm :: Term
  , fpTerms :: Map Symbol FPTerm
  } deriving (Eq, Ord, Show)

data FPTerm = FPTerm
  { fpType :: FPType
  , fpSignature :: [(Symbol, Sort)]
  , term :: Term
  } deriving (Eq, Ord, Show)

data FPType
  = GFP
  | LFP
  deriving (Eq, Ord, Show)

gameToFP :: Arena -> Objective -> FPSystem
gameToFP arena obj =
  case winningCond obj of
    Safety safes -> encodeSafety arena (initialLoc obj) safes
    Reachability reach -> encodeReach arena (initialLoc obj) reach
    Buechi fset -> encodeBuechi arena (initialLoc obj) fset
    CoBuechi sset -> encodeCoBuechi arena (initialLoc obj) sset
    Parity rank -> encodeParity arena (initialLoc obj) rank

encTop :: Arena -> (Loc, Term) -> (Loc -> [(Symbol, FPTerm)]) -> FPSystem
encTop arena (initLoc, initCond) encLoc =
  FPSystem
    { systemTerm = Vars.forallX (vars arena) $ dom arena initLoc `FOL.impl` initCond
    , fpTerms = Map.fromList $ concatMap encLoc $ locationL arena
    }

encodeSafety :: Arena -> Loc -> Set Loc -> FPSystem
encodeSafety arena init safes =
  encTop arena (init, safePred init) $ \loc -> [(safePredName loc, safeFor loc)]
  where
    safeFor loc =
      gfp states
        $ if loc `elem` safes
            then FOL.andf
                   [safePred loc, cpre Sys arena (SymSt.symSt (locations arena) safePred) loc]
            else FOL.false
    safePred loc = FOL.unintFunc (safePredName loc) FOL.SBool states
    safePredName loc = prefix ++ "_" ++ locName arena loc -- TODO: guarnatee uniqueness??!
    prefix = FOL.uniquePrefix "Pred" (usedSymbols arena)
    states = map (\v -> (v, Vars.sortOf (vars arena) v)) $ Vars.stateVarL $ vars arena

encodeReach :: Arena -> Loc -> Set Loc -> FPSystem
encodeReach arena init reachs =
  encTop arena (init, reachPred init) $ \loc -> [(reachPredName loc, reachFor loc)]
  where
    reachFor loc =
      lfp states
        $ if loc `elem` reachs
            then FOL.true
            else FOL.orf
                   [reachPred loc, cpre Sys arena (SymSt.symSt (locations arena) reachPred) loc]
    reachPred loc = FOL.unintFunc (reachPredName loc) FOL.SBool states
    reachPredName loc = prefix ++ "_" ++ locName arena loc -- TODO: guarnatee uniqueness??!
    prefix = FOL.uniquePrefix "Pred" (usedSymbols arena)
    states = map (\v -> (v, Vars.sortOf (vars arena) v)) $ Vars.stateVarL $ vars arena

encodeBuechi :: Arena -> Loc -> Set Loc -> FPSystem
encodeBuechi arena init fset =
  encTop arena (init, gfpPred init) $ \loc -> [(gfpName loc, encGFP loc), (lfpName loc, encLFP loc)]
  where
    encGFP = gfp states . lfpPred
    encLFP loc =
      lfp states
        $ if loc `elem` fset
            then cpre Sys arena (SymSt.symSt (locations arena) gfpPred) loc
            else cpre Sys arena (SymSt.symSt (locations arena) lfpPred) loc
    gfpPred loc = FOL.unintFunc (gfpName loc) FOL.SBool states
    gfpName loc = prefix ++ "GFP" ++ "_" ++ locName arena loc
    lfpPred loc = FOL.unintFunc (lfpName loc) FOL.SBool states
    lfpName loc = prefix ++ "LFP" ++ "_" ++ locName arena loc
    prefix = FOL.uniquePrefix "Pred" (usedSymbols arena)
    states = map (\v -> (v, Vars.sortOf (vars arena) v)) $ Vars.stateVarL $ vars arena

encodeCoBuechi :: Arena -> Loc -> Set Loc -> FPSystem
encodeCoBuechi arena init sset =
  encTop arena (init, lfpPred init) $ \loc -> [(lfpName loc, encLFP loc), (gfpName loc, encGFP loc)]
  where
    encLFP = lfp states . gfpPred
    encGFP loc =
      gfp states
        $ if loc `elem` sset
            then cpre Sys arena (SymSt.symSt (locations arena) lfpPred) loc
            else cpre Sys arena (SymSt.symSt (locations arena) gfpPred) loc
    gfpPred loc = FOL.unintFunc (gfpName loc) FOL.SBool states
    gfpName loc = prefix ++ "GFP" ++ "_" ++ locName arena loc
    lfpPred loc = FOL.unintFunc (lfpName loc) FOL.SBool states
    lfpName loc = prefix ++ "LFP" ++ "_" ++ locName arena loc
    prefix = FOL.uniquePrefix "Pred" (usedSymbols arena)
    states = map (\v -> (v, Vars.sortOf (vars arena) v)) $ Vars.stateVarL $ vars arena

encodeParity :: Arena -> Loc -> Map Loc Word -> FPSystem
encodeParity arena init rank =
  encTop arena (init, pred maxColor init) $ \loc ->
    fpPair (0 :: Word) loc : map (`fpPair` loc) [1 .. maxColor]
  where
    maxColor = maximum $ Map.elems rank
    fpPair col loc = (predName col loc, encFP col loc)
    encFP col loc
      | col == 0 =
        lfp states $ cpre Sys arena (SymSt.symSt (locations arena) (pred (rank ! loc))) loc
      | even col = lfp states $ pred (col - 1) loc
      | otherwise = gfp states $ pred (col - 1) loc
    pred col loc = FOL.unintFunc (predName col loc) FOL.SBool states
    predName col loc = prefix ++ "_ " ++ show col ++ "_" ++ locName arena loc
    prefix = FOL.uniquePrefix "Pred" (usedSymbols arena)
    states = map (\v -> (v, Vars.sortOf (vars arena) v)) $ Vars.stateVarL $ vars arena

lfp :: [(Symbol, Sort)] -> Term -> FPTerm
lfp sig t = FPTerm {fpType = LFP, fpSignature = sig, term = t}

gfp :: [(Symbol, Sort)] -> Term -> FPTerm
gfp sig t = FPTerm {fpType = GFP, fpSignature = sig, term = t}
---------------------------------------------------------------------------------------------------
