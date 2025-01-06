{-# LANGUAGE LambdaCase #-}

-- TODO RENAME
--  Game -> Arena
--  inv -> domain
--  ...
module Issy.Solver.GameInterface
  ( Game
  , Arena
  , Loc
  , vars
  , inv
  , locations
  , preds
  , succs
  , cyclicIn
  , usedSymbols
  , predSet
  , loopGame
  , setInv
  , stateVars
  , inputL
  , boundedVar
  , locName
  , sortOf
  , fromRPG
  , fromSG
  , strSt
  , invSymSt
  , emptySt
  , Player(..)
  , opponent
  , cpre
  , cpreS
  , independentProgVars
  , inducedSubGame
  , -- Visit counting
    VisitCounter
  , noVisits
  , visit
  , visits
  ) where

import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)

import Issy.Base.Locations (Loc)
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.RPG as RPG
import qualified Issy.SymbolicArena as Sym

data Game
  = RPG RPG.Game
  | Sym Sym.Arena
  deriving (Show)

type Arena = Game

fromRPG :: (RPG.Game, a) -> (Game, a)
fromRPG = first RPG

fromSG :: (Sym.Arena, a) -> (Game, a)
fromSG = first Sym

liftG :: (RPG.Game -> a) -> (Sym.Arena -> a) -> Game -> a
liftG f _ (RPG g) = f g
liftG _ h (Sym a) = h a

liftV :: (Vars.Variables -> a) -> Game -> a
liftV f = f . liftG RPG.variables Sym.variables

vars :: Game -> Vars.Variables
vars = liftV id

inv :: Game -> Loc -> Term
inv = liftG RPG.inv Sym.domain

locations :: Game -> Set Loc
locations = liftG RPG.locations Sym.locSet

preds :: Game -> Loc -> Set Loc
preds = liftG RPG.preds Sym.preds

succs :: Game -> Loc -> Set Loc
succs = liftG RPG.succs Sym.succs

predSet :: Game -> Set Loc -> Set Loc
predSet = liftG RPG.predSet Sym.predSet

cyclicIn :: Game -> Loc -> Bool
cyclicIn = liftG RPG.cyclicIn Sym.cyclicIn

usedSymbols :: Game -> Set Symbol
usedSymbols = liftG RPG.usedSymbols Sym.usedSymbols

cpreEnv :: Game -> SymSt -> Loc -> Term
cpreEnv = liftG RPG.cpreEnv Sym.cpreEnv

cpreSys :: Game -> SymSt -> Loc -> Term
cpreSys = liftG RPG.cpreSys Sym.cpreSys

loopGame :: Game -> Loc -> (Game, Loc)
loopGame (RPG g) = first RPG . RPG.loopGame g
loopGame (Sym a) = first Sym . Sym.loopArena a

inducedSubGame :: Game -> Set Loc -> (Game, Loc -> Loc)
inducedSubGame (RPG g) = first RPG . RPG.inducedSubGame g
inducedSubGame (Sym a) = first Sym . Sym.inducedSubArena a

independentProgVars :: Config -> Game -> IO (Set Symbol)
independentProgVars cfg (RPG g) = RPG.independentProgVars cfg g
independentProgVars cfg (Sym a) = Sym.independentProgVars cfg a

setInv :: Game -> Loc -> Term -> Game
setInv (RPG g) l t = RPG $ RPG.setInv g l t
setInv (Sym a) l t = Sym $ Sym.setDomain a l t

inputL :: Game -> [Symbol]
inputL = liftV Vars.inputL

stateVars :: Game -> Set Symbol
stateVars = liftV Vars.stateVars

boundedVar :: Game -> Symbol -> Bool
boundedVar = liftV Vars.isBounded

locName :: Game -> Loc -> String
locName = liftG RPG.locName Sym.locName

sortOf :: Game -> Symbol -> Sort
sortOf = liftV Vars.sortOf

--
-- Game related symbolic state handeling
--
strSt :: Game -> SymSt -> String
strSt = SymSt.toString . locName

invSymSt :: Game -> SymSt
invSymSt g = SymSt.symSt (locations g) (inv g)

emptySt :: Game -> SymSt
emptySt g = SymSt.symSt (locations g) (const FOL.false)

--
-- Player
--
data Player
  = Sys
  | Env
  deriving (Eq, Ord, Show)

opponent :: Player -> Player
opponent =
  \case
    Sys -> Env
    Env -> Sys

--
-- Enforcement
--
cpre :: Player -> Game -> SymSt -> Loc -> Term
cpre p =
  case p of
    Sys -> cpreSys
    Env -> cpreEnv

cpreS :: Config -> Player -> Game -> SymSt -> IO SymSt
cpreS ctx p g st = SymSt.simplify ctx (SymSt.symSt (locations g) (cpre p g st))

--
-- Visit Counting
--
newtype VisitCounter =
  VC (Map Loc Int)

noVisits :: Game -> VisitCounter
noVisits = VC . Map.fromSet (const 0) . locations

visit :: Loc -> VisitCounter -> VisitCounter
visit l (VC vc) = VC $ Map.insertWith (+) l 1 vc

visits :: Loc -> VisitCounter -> Int
visits l (VC vc) = Map.findWithDefault 0 l vc
