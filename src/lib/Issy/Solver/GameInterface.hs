-- TODO RENAME
--  Game -> Arena
--  inv -> domain
--  ...
module Issy.Solver.GameInterface
  ( Game
  , Loc
  , inv
  , locations
  , preds
  , cyclicIn
  , usedSymbols
  , predSet
  , cpreEnv
  , cpreSys
  , loopGame
  , setInv
  , stateVars
  , stateVarL
  , inputL
  , boundedVar
  , locName
  , sortOf
  , fromRPG
  , fromSG
  ) where

import Data.Bifunctor (first)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Locations (Loc)
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.Variables as Vars
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.RPG as RPG
import qualified Issy.SymbolicArena as Sym

data Game
  = RPG RPG.Game
  | Sym Sym.Arena

fromRPG :: (RPG.Game, a) -> (Game, a)
fromRPG = first RPG

fromSG :: (Sym.Arena, a) -> (Game, a)
fromSG = first Sym

liftG :: (RPG.Game -> a) -> (Sym.Arena -> a) -> Game -> a
liftG f _ (RPG g) = f g
liftG _ h (Sym a) = h a

inv :: Game -> Loc -> Term
inv = liftG RPG.inv Sym.domain

locations :: Game -> Set Loc
locations = liftG RPG.locations Sym.locSet

preds :: Game -> Loc -> Set Loc
preds = liftG RPG.preds Sym.preds

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
loopGame (RPG g) l = first RPG (RPG.loopGame g l)
loopGame (Sym a) l = first Sym (Sym.loopArena a l)

setInv :: Game -> Loc -> Term -> Game
setInv (RPG g) l t = RPG $ RPG.setInv g l t
setInv (Sym a) l t = Sym $ Sym.setDomain a l t

inputL :: Game -> [Symbol]
inputL = liftG RPG.inputs (Vars.inputL . Sym.variables)

stateVarL :: Game -> [Symbol]
stateVarL = liftG RPG.outputs (Vars.stateVarL . Sym.variables)

stateVars :: Game -> Set Symbol
stateVars = liftG (Set.fromList . RPG.outputs) (Vars.stateVars . Sym.variables)

boundedVar :: Game -> Symbol -> Bool
boundedVar g var = liftG ((var `elem`) . RPG.boundedCells) (`Sym.boundedVar` var) g

locName :: Game -> Loc -> String
locName = liftG RPG.locName Sym.locName

sortOf :: Game -> Symbol -> Sort
sortOf = liftG RPG.sortOf (Vars.sortOf . Sym.variables)
