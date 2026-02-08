---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.GameInterface
-- Description : Solving interface to the games
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module is an interface for the solving algorithms to the different types
-- of games (symbolic game and reactive program games). This allows to abstract away
-- from the concrete shape of the games.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.GameInterface
  ( -- Types
    Arena
  , Loc
  , fromRPG
  , fromSG
  , -- Accessors
    vars
  , inputL
  , stateVars
  , boundedVar
  , sortOf
  , locations
  , locationL
  , locName
  , dom
  , succs
  , preds
  , predSet
  , usedSymbols
  , -- Symbolic state
    emptySt
  , domSymSt
  , strSt
  , extendSt
  , backmapSt
  , -- Players
    Player(..)
  , opponent
  , -- Enforcement
    cpre
  , cpreEnv
  , cpreSys
  , cpreS
  , removeAttrEnv
  , removeAttrSys
  , -- Special Things
    pre
  , cyclicIn
  , loopArena
  , independentProgVars
  , inducedSubArena
  , addConstants
  , syntCPre
  , -- Visit counting
    VisitCounter
  , noVisits
  , visit
  , visits
  , totalVisits
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.ReactiveProgramArena as RPG
import qualified Issy.Games.SymbolicArena as Sym
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- Data Structure
---------------------------------------------------------------------------------------------------
-- | Encapsulated representation of arenas for different games.
data Arena
  = RPG RPG.RPArena
  | Sym Sym.Arena
  deriving (Eq, Ord, Show)

-- | Transform an reactive program arena to an encapsulated arena.
fromRPG :: (RPG.RPArena, a) -> (Arena, a)
fromRPG = first RPG

-- | Transform an symbolic arena to an encapsulated arena.
fromSG :: (Sym.Arena, a) -> (Arena, a)
fromSG = first Sym

liftG :: (RPG.RPArena -> a) -> (Sym.Arena -> a) -> Arena -> a
liftG f _ (RPG g) = f g
liftG _ h (Sym a) = h a

liftV :: (Vars.Variables -> a) -> Arena -> a
liftV f = f . liftG RPG.variables Sym.variables

---------------------------------------------------------------------------------------------------
-- Accessors
---------------------------------------------------------------------------------------------------
-- | The variable context of an arena.
vars :: Arena -> Vars.Variables
vars = liftV id

-- | The input variables of an arena as a list.
inputL :: Arena -> [Symbol]
inputL = liftV Vars.inputL

-- | The state variables of an arena.
stateVars :: Arena -> Set Symbol
stateVars = liftV Vars.stateVars

-- | Check if an variable is bounded (warning: this is just for heuristics).
boundedVar :: Arena -> Symbol -> Bool
boundedVar = liftV Vars.isBounded

-- | The sort of an variable in an arena.
sortOf :: Arena -> Symbol -> Sort
sortOf = liftV Vars.sortOf

-- | The locations of an arena.
locations :: Arena -> Set Loc
locations = liftG RPG.locations Sym.locSet

-- | The locations of an arena as a list.
locationL :: Arena -> [Loc]
locationL = Set.toList . locations

-- | The name of a location.
locName :: Arena -> Loc -> String
locName = liftG RPG.locName Sym.locName

-- | The domain of a location. The domain restricts (symbolically) what state variable
-- values are allowed in a location.
dom :: Arena -> Loc -> Term
dom = liftG RPG.inv Sym.domain

-- | Compute all the successors of a location.
succs :: Arena -> Loc -> Set Loc
succs = liftG RPG.succs Sym.succs

-- | Compute all the predecessors of a location.
preds :: Arena -> Loc -> Set Loc
preds = liftG RPG.preds Sym.preds

-- | Compute all the predecessors of a set of locations.
predSet :: Arena -> Set Loc -> Set Loc
predSet = liftG RPG.predSet Sym.predSet

-- | All symbols, including variables, function names, and location names, that are used
-- in the arena. This can be used to generate fresh symbols, e.g. for auxiliary variables,
-- such that they are really fresh.
usedSymbols :: Arena -> Set Symbol
usedSymbols = liftG RPG.usedSymbols Sym.usedSymbols

---------------------------------------------------------------------------------------------------
-- Arena related symbolic state handling
---------------------------------------------------------------------------------------------------
-- | An empty symbolic state in the context of the locations of an arena.
emptySt :: Arena -> SymSt
emptySt g = SymSt.symSt (locations g) (const FOL.false)

-- | The symbolic state that represents the locations domain, i.e. the
-- full set of states in this arena.
domSymSt :: Arena -> SymSt
domSymSt g = SymSt.symSt (locations g) (dom g)

-- | Pretty print a symbolic state.
strSt :: Arena -> SymSt -> String
strSt = SymSt.toString . locName

-- | Map an state in some old location set, to a symbolic state of
-- a given arena (given the appropriate mapping). The set of locations of the
-- new arena can be smaller than the old one, i.e. the value for those old location
-- are discarded. Conversely, there might be locations in the new arena, that have
-- now corresponding old value. Those default to false.
extendSt :: SymSt -> (Loc -> Maybe Loc) -> Arena -> SymSt
extendSt old oldToNew newArena =
  foldr
    (\locOld st ->
       case oldToNew locOld of
         Nothing -> st
         Just locNew -> SymSt.set st locNew (SymSt.get old locOld))
    (emptySt newArena)
    (SymSt.locations old)

-- | Given some new state, a mapping from old to new, and the old arena, back transform
-- the new symbolic state to one matching the location set of the old arena.
backmapSt :: SymSt -> (Loc -> Maybe Loc) -> Arena -> SymSt
backmapSt new oldToNew oldArena =
  SymSt.symSt (locations oldArena) $ maybe FOL.false (SymSt.get new) . oldToNew

---------------------------------------------------------------------------------------------------
-- Player
---------------------------------------------------------------------------------------------------
-- | Representation of a player in the game.
data Player
  = Sys
  -- ^ The system player.
  | Env
  -- ^ The environment player.
  deriving (Eq, Ord, Show)

-- | Return the other player of a given player, i.e. its opponent.
opponent :: Player -> Player
opponent =
  \case
    Sys -> Env
    Env -> Sys

---------------------------------------------------------------------------------------------------
-- Enforcement
---------------------------------------------------------------------------------------------------
-- | Compute the enforceable predecessors, i.e. the possible states in a single location
-- from which the player can always enforce to reach the given symbolic state.
cpre :: Player -> Arena -> SymSt -> Loc -> Term
cpre p =
  case p of
    Sys -> cpreSys
    Env -> cpreEnv

-- | 'pre' for the environment player;
cpreEnv :: Arena -> SymSt -> Loc -> Term
cpreEnv = liftG RPG.cpreEnv Sym.cpreEnv

-- | 'pre' for the system player;
cpreSys :: Arena -> SymSt -> Loc -> Term
cpreSys = liftG RPG.cpreSys Sym.cpreSys

-- | 'pre' applied to all locations, resulting in a symbolic state.
cpreS :: Player -> Arena -> SymSt -> SymSt
cpreS p g = SymSt.symSt (locations g) . cpre p g

-- | Remove the result of an system attractor computation, i.e. the fixpoint
-- of applying the system enforceable predecessors, from states of the arena
-- by modifying the domain. This is usually used for parity game solving.
-- Note that this method might try to simplify the arena with an SMT-solver.
removeAttrSys :: Config -> SymSt -> Arena -> IO Arena
removeAttrSys conf st (RPG g) = RPG <$> RPG.removeAttrSys conf st g
removeAttrSys conf st (Sym a) = Sym <$> Sym.removeAttrSys conf st a

-- | As 'removeAttrSys' but for the system player.
removeAttrEnv :: Config -> SymSt -> Arena -> IO Arena
removeAttrEnv conf st (RPG g) = RPG <$> RPG.removeAttrEnv conf st g
removeAttrEnv conf st (Sym a) = Sym <$> Sym.removeAttrEnv conf st a

-- | Synthesize assignments to the variables that mirror the step of an enforceable
-- predecessors. Since the locations are modeled as an integer program counter,
-- this method gets the name of the location variable as well as the constants for the
-- locations.
syntCPre ::
     Config -> Arena -> Symbol -> (Loc -> Integer) -> Loc -> Term -> SymSt -> IO [(Symbol, Term)]
syntCPre conf = liftG (RPG.syntCPre conf) (Sym.syntCPre conf)

---------------------------------------------------------------------------------------------------
-- Special Things
---------------------------------------------------------------------------------------------------
-- | The possible predecessor of a symbolic state in a location.
pre :: Arena -> SymSt -> Loc -> Term
pre = liftG RPG.pre Sym.pre

-- | Check if the arena is cyclic in a location, i.e. the location might
-- be reachable from itself.
cyclicIn :: Arena -> Loc -> Bool
cyclicIn = liftG RPG.cyclicIn Sym.cyclicIn

-- | Compute the loop arena (see POPL'24 and TACAS'26 papers for more details) in
-- a given location. The returned location is the copy location of the aforementioned one.
loopArena :: Arena -> Loc -> (Arena, Loc)
loopArena (RPG g) = first RPG . RPG.loopArena g
loopArena (Sym a) = first Sym . Sym.loopArena a

-- | Compute the so induced sub-arena which results from restricting the arena to
-- a given set of location (without border locations).
-- Return a mapping from the original locations to the new ones, as well as
-- the set of old locations (!) with the border locations that the arena
-- has been restricted too.
inducedSubArena :: Arena -> Set Loc -> (Arena, (Loc -> Loc, Set Loc))
inducedSubArena (RPG g) = first RPG . RPG.inducedSubArena g
inducedSubArena (Sym a) = first Sym . Sym.inducedSubArena a

-- | Compute the independent program variables, i.e. the program variables that
-- remain constant or do not matter otherwise.
independentProgVars :: Config -> Arena -> IO (Set Symbol)
independentProgVars cfg (RPG g) = RPG.independentProgVars cfg g
independentProgVars cfg (Sym a) = Sym.independentProgVars cfg a

-- | Add state variables that are guaranteed not to change
-- to the arena. This is undefined if a variable already exists.
addConstants :: [(Symbol, Sort)] -> Arena -> Arena
addConstants cvars (RPG g) = RPG $ RPG.addConstants cvars g
addConstants cvars (Sym a) = Sym $ Sym.addConstants cvars a

---------------------------------------------------------------------------------------------------
-- Visit Counting
---------------------------------------------------------------------------------------------------
-- | Data structure to count "visits" a location. A visit could be, e.g., how
-- often the attractor computation computed the enforceable predecessor operator.
-- This is used for heuristics.
newtype VisitCounter =
  VC (Map Loc Int)

-- | Initial visit counter for an arena with no visits.
noVisits :: Arena -> VisitCounter
noVisits = VC . Map.fromSet (const 0) . locations

-- | Mark a visit to a location, i.e. increment the counter.
visit :: Loc -> VisitCounter -> VisitCounter
visit l (VC vc) = VC $ Map.insertWith (+) l 1 vc

-- | Return the visits to a location.
visits :: Loc -> VisitCounter -> Int
visits l (VC vc) = Map.findWithDefault 0 l vc

-- | Return the total number of visits.
totalVisits :: VisitCounter -> Int
totalVisits (VC vc) = sum $ Map.elems vc
---------------------------------------------------------------------------------------------------
