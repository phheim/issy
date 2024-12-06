{-# LANGUAGE LambdaCase #-}

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
  , toString
  ) where

import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)

import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars (inputs)
import Issy.Logic.FOL (Symbol, Term, false, true)
import Issy.Monitor.Rules (Context)
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
  | p == true = tt
  | p == false = tf
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
  { ctx :: Context
  , variables :: Variables
  , predicates :: Set Term
  , initState :: State
  , goodState :: State
  , badState :: State
  , safes :: Set State
  , stateLabel :: Map State M.State
  , revLabel :: Map M.State State
  , cnt :: Int
  , stateTrans :: Map (State, [(Term, Bool)]) (Trans [([(Bool, Symbol, Term)], State)])
  , expansionCache :: Map
      (ExpansionState, [(Term, Bool)])
      (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
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
-- Pretty printing
-------------------------------------------------------------------------------
toString :: Monitor -> String
toString _ = "TODO" -- TODO IMPLEMENT
-------------------------------------------------------------------------------
