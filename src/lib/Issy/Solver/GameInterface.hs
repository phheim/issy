{-# LANGUAGE LambdaCase #-}

module Issy.Solver.GameInterface
  ( Arena
  , Loc
  , vars
  , dom
  , locations
  , locationL
  , preds
  , succs
  , cyclicIn
  , usedSymbols
  , predSet
  , loopArena
  , stateVars
  , inputL
  , boundedVar
  , locName
  , sortOf
  , fromRPG
  , fromSG
  , strSt
  , domSymSt
  , emptySt
  , Player(..)
  , opponent
  , cpre
  , cpreS
  , pre
  , extendSt
  , independentProgVars
  , inducedSubArena
  , syntCPre
  , removeAttrSys
  , removeAttrEnv
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
import qualified Data.Set as Set

import Issy.Base.Locations (Loc)
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.RPG as RPG
import qualified Issy.SymbolicArena as Sym

data Arena
  = RPG RPG.Game
  | Sym Sym.Arena
  deriving (Show)

fromRPG :: (RPG.Game, a) -> (Arena, a)
fromRPG = first RPG

fromSG :: (Sym.Arena, a) -> (Arena, a)
fromSG = first Sym

liftG :: (RPG.Game -> a) -> (Sym.Arena -> a) -> Arena -> a
liftG f _ (RPG g) = f g
liftG _ h (Sym a) = h a

liftV :: (Vars.Variables -> a) -> Arena -> a
liftV f = f . liftG RPG.variables Sym.variables

vars :: Arena -> Vars.Variables
vars = liftV id

dom :: Arena -> Loc -> Term
dom = liftG RPG.inv Sym.domain

locations :: Arena -> Set Loc
locations = liftG RPG.locations Sym.locSet

locationL :: Arena -> [Loc]
locationL = Set.toList . locations

preds :: Arena -> Loc -> Set Loc
preds = liftG RPG.preds Sym.preds

succs :: Arena -> Loc -> Set Loc
succs = liftG RPG.succs Sym.succs

predSet :: Arena -> Set Loc -> Set Loc
predSet = liftG RPG.predSet Sym.predSet

cyclicIn :: Arena -> Loc -> Bool
cyclicIn = liftG RPG.cyclicIn Sym.cyclicIn

usedSymbols :: Arena -> Set Symbol
usedSymbols = liftG RPG.usedSymbols Sym.usedSymbols

pre :: Arena -> SymSt -> Loc -> Term
pre = liftG RPG.pre Sym.pre

cpreEnv :: Arena -> SymSt -> Loc -> Term
cpreEnv = liftG RPG.cpreEnv Sym.cpreEnv

cpreSys :: Arena -> SymSt -> Loc -> Term
cpreSys = liftG RPG.cpreSys Sym.cpreSys

loopArena :: Arena -> Loc -> (Arena, Loc)
loopArena (RPG g) = first RPG . RPG.loopGame g
loopArena (Sym a) = first Sym . Sym.loopArena a

inducedSubArena :: Arena -> Set Loc -> (Arena, Loc -> Loc)
inducedSubArena (RPG g) = first RPG . RPG.inducedSubGame g
inducedSubArena (Sym a) = first Sym . Sym.inducedSubArena a

independentProgVars :: Config -> Arena -> IO (Set Symbol)
independentProgVars cfg (RPG g) = RPG.independentProgVars cfg g
independentProgVars cfg (Sym a) = Sym.independentProgVars cfg a

syntCPre ::
     Config -> Arena -> Symbol -> (Loc -> Term) -> Loc -> Term -> SymSt -> IO [(Symbol, Term)]
syntCPre conf = liftG (RPG.syntCPre conf) (Sym.syntCPre conf)

inputL :: Arena -> [Symbol]
inputL = liftV Vars.inputL

stateVars :: Arena -> Set Symbol
stateVars = liftV Vars.stateVars

boundedVar :: Arena -> Symbol -> Bool
boundedVar = liftV Vars.isBounded

locName :: Arena -> Loc -> String
locName = liftG RPG.locName Sym.locName

sortOf :: Arena -> Symbol -> Sort
sortOf = liftV Vars.sortOf

--
-- Arena related symbolic state handeling
--
strSt :: Arena -> SymSt -> String
strSt = SymSt.toString . locName

domSymSt :: Arena -> SymSt
domSymSt g = SymSt.symSt (locations g) (dom g)

emptySt :: Arena -> SymSt
emptySt g = SymSt.symSt (locations g) (const FOL.false)

extendSt :: SymSt -> (Loc -> Loc) -> Arena -> SymSt
extendSt old oldToNew arena =
  foldr
    (\locOld st -> SymSt.set st (oldToNew locOld) (SymSt.get old locOld))
    (emptySt arena)
    (SymSt.locations old)

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
cpre :: Player -> Arena -> SymSt -> Loc -> Term
cpre p =
  case p of
    Sys -> cpreSys
    Env -> cpreEnv

cpreS :: Player -> Arena -> SymSt -> SymSt
cpreS p g = SymSt.symSt (locations g) . cpre p g

removeAttrSys :: Config -> SymSt -> Arena -> IO Arena
removeAttrSys conf st (RPG g) = RPG <$> RPG.removeAttrSys conf st g
removeAttrSys conf st (Sym a) = Sym <$> Sym.removeAttrSys conf st a

removeAttrEnv :: Config -> SymSt -> Arena -> IO Arena
removeAttrEnv conf st (RPG g) = RPG <$> RPG.removeAttrEnv conf st g
removeAttrEnv conf st (Sym a) = Sym <$> Sym.removeAttrEnv conf st a

--
-- Visit Counting
--
newtype VisitCounter =
  VC (Map Loc Int)

noVisits :: Arena -> VisitCounter
noVisits = VC . Map.fromSet (const 0) . locations

visit :: Loc -> VisitCounter -> VisitCounter
visit l (VC vc) = VC $ Map.insertWith (+) l 1 vc

visits :: Loc -> VisitCounter -> Int
visits l (VC vc) = Map.findWithDefault 0 l vc
