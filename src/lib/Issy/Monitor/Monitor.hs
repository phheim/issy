{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Monitor.Monitor
  ( State(..)
  , Verdict(..)
  , Trans(..)
  , trIf
  , leafs
  , Monitor(..)
  , label
  , addLabel
  , stateName
  , revlabel
  , initial
  , verdict
  , inputs
  ) where

import qualified Data.Map.Strict as Map
import Issy.Prelude

import qualified Issy.Base.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import Issy.Monitor.Rules (GlobalS)
import Issy.Monitor.State (ExpansionState)
import qualified Issy.Monitor.State as M (State)

newtype State =
  State Int
  deriving (Eq, Ord, Show)

data Verdict
  = VALID
  | UNSAFE
  | SAFETY
  | OPEN
  deriving (Eq, Ord, Show)

data Trans a
  = TrIf Term (Trans a) (Trans a)
  | TrSucc a
  deriving (Eq, Ord, Show)

trIf :: Term -> Trans a -> Trans a -> Trans a
trIf p tt tf
  | p == FOL.true = tt
  | p == FOL.false = tf
  | otherwise = TrIf p tt tf

instance Functor Trans where
  fmap m (TrIf p tt tf) = TrIf p (fmap m tt) (fmap m tf)
  fmap m (TrSucc a) = TrSucc (m a)

leafs :: Trans a -> [a]
leafs =
  \case
    TrIf _ tt tf -> leafs tt ++ leafs tf
    TrSucc a -> [a]

data Monitor = Monitor
  { gls :: GlobalS
  , variables :: Variables
  , predicates :: Set Term
  , initState :: State
  , goodState :: State
  , badState :: State
  , safes :: Set State
  , stateLabel :: Map State M.State
  , revLabel :: Map M.State State
  , cnt :: Int
  , stateTrans :: Map (State, Set (Term, Bool)) (Trans [([(Bool, Symbol, Term)], State)])
  , expansionCache :: Map
      (ExpansionState, Set (Term, Bool))
      (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
  , hasUpdates :: Bool
  }

label :: Monitor -> State -> M.State
label mon st =
  case stateLabel mon !? st of
    Nothing -> error "assert: every state should have a label"
    Just st -> st

revlabel :: Monitor -> M.State -> State
revlabel mon st =
  case revLabel mon !? st of
    Nothing -> error "assert: every label should have a state"
    Just st -> st

addLabel :: Monitor -> M.State -> Monitor
addLabel mon stl
  | stl `Map.member` revLabel mon = mon
  | otherwise =
    mon
      { cnt = cnt mon + 1
      , stateLabel = Map.insert (State (cnt mon)) stl (stateLabel mon)
      , revLabel = Map.insert stl (State (cnt mon)) (revLabel mon)
      }

stateName :: Monitor -> State -> String
stateName _ (State k) = "q" ++ show k

initial :: Monitor -> State
initial = initState

verdict :: Monitor -> State -> Verdict
verdict mon st
  | st == badState mon = UNSAFE
  | st == goodState mon = VALID
  | st `elem` safes mon = SAFETY
  | otherwise = OPEN

inputs :: Monitor -> Set Symbol
inputs = Vars.inputs . variables
-------------------------------------------------------------------------------
