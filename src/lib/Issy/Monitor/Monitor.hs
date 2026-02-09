---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Monitor.Monitor
-- Description : Monitor data-structure
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the main data structure for representing a monitor internally.
-- It should not be used from beyond the monitor implementation. For using is using constructor
-- to construct things should be avoid if a abstract construction method exists.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Monitor.Monitor
  ( -- Perquisite
    State(..)
  , Verdict(..)
  , Trans(..)
  , trIf
  , leafs
  , -- The monitor
    Monitor(..)
  , label
  , addLabel
  , stateName
  , revlabel
  , initial
  , verdict
  , inputs
  , states
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import Issy.Prelude

import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import Issy.Monitor.Rules (GlobalS)
import Issy.Monitor.State (ExpansionState)
import qualified Issy.Monitor.State as M (State)

---------------------------------------------------------------------------------------------------
-- | Representation of a monitor state in a monitor. Note that a state has only
-- semantics in the context of a monitor.
newtype State =
  State Int
  -- ^ Internally monitor states are just encapsulated integers which are then labeled with
  -- the actual state content (i.e. the semantic/mathematically representation) of the state.
  -- States and their labels are mapped bijectively.
  deriving (Eq, Ord, Show)

-- | The verdict of a monitor in some state.
data Verdict
  = VALID
  -- ^ The valid verdict states that from now on all words will be accepted.
  | UNSAFE
  -- ^ The unsafe verdict states that from now on all words will be rejected.
  | SAFETY
  -- ^ The safety verdict state that if a word is rejected then after a finite prefix.
  | OPEN
  -- ^ The open verdict means that we do not know anything yet.
  deriving (Eq, Ord, Show)

-- | Representation of a transition if-then-else-tree in the monitor.
data Trans a
  = TrIf Term (Trans a) (Trans a)
  -- ^ The if-then-else condition.
  | TrSucc a
  -- ^  The successor leaf.
  deriving (Eq, Ord, Show)

-- | Create an if-then-else transition.
trIf :: Term -> Trans a -> Trans a -> Trans a
trIf p tt tf
  | p == FOL.true = tt
  | p == FOL.false = tf
  | otherwise = TrIf p tt tf

instance Functor Trans where
  fmap m (TrIf p tt tf) = TrIf p (fmap m tt) (fmap m tf)
  fmap m (TrSucc a) = TrSucc (m a)

-- | Return all the successors in a transition.
leafs :: Trans a -> [a]
leafs =
  \case
    TrIf _ tt tf -> leafs tt ++ leafs tf
    TrSucc a -> [a]

---------------------------------------------------------------------------------------------------
-- | The monitor data structure.
data Monitor = Monitor
  { gls :: GlobalS
    -- ^ Global rule exploration state.
  , variables :: Variables
    -- ^ The variables over which a monitor ranges.
  , predicates :: Set Term
    -- ^  The predicates used for predicate propagation.
  , initState :: State
    -- ^ The initial state.
  , goodState :: State
    -- ^ The self-looping good state with the 'VALID' verdict. All states with such a verdict
    -- should be redirect to that one.
  , badState :: State
    -- ^ The self-looping bad state with the 'UNSAFE' verdict. All states with such a verdict
    -- should be redirect to that one.
  , safes :: Set State
    -- ^ State that are known to be 'SAFETY'.
  , stateLabel :: Map State M.State
    -- ^ Mapping from the efficient monitor states, to the state label which represent the
    -- actual state.
  , revLabel :: Map M.State State
    -- ^ Back mapping of the 'stateLabel'
  , cnt :: Int
    -- ^ Total number of states.
  , stateTrans :: Map (State, Set (Term, Bool)) (Trans [([(Bool, Symbol, Term)], State)])
    -- ^ Transition from a state and a predicate assignment.
  , expansionCache :: Map
      (ExpansionState, Set (Term, Bool))
      (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
    -- ^ Cache for computing the formula expansion more efficiently.
  , hasUpdates :: Bool
    -- ^ Indication whether updates are present, i.e. the logic is TSLMT.
  }

-- | The label of a state, i.e. its actual semantic state.
label :: Monitor -> State -> M.State
label mon st =
  case stateLabel mon !? st of
    Nothing -> error "assert: every state should have a label"
    Just st -> st

-- | The state of a state label.
revlabel :: Monitor -> M.State -> State
revlabel mon st =
  case revLabel mon !? st of
    Nothing -> error "assert: every label should have a state"
    Just st -> st

-- | Add a state label to a monitor, possibly creating a new state.
addLabel :: Monitor -> M.State -> Monitor
addLabel mon stl
  | stl `Map.member` revLabel mon = mon
  | otherwise =
    mon
      { cnt = cnt mon + 1
      , stateLabel = Map.insert (State (cnt mon)) stl (stateLabel mon)
      , revLabel = Map.insert stl (State (cnt mon)) (revLabel mon)
      }

-- | Print the name of a state.
stateName :: Monitor -> State -> String
stateName _ (State k) = "q" ++ show k

-- | The initial state of a monitor.
initial :: Monitor -> State
initial = initState

-- | The verdict of a state in a monitor.
verdict :: Monitor -> State -> Verdict
verdict mon st
  | st == badState mon = UNSAFE
  | st == goodState mon = VALID
  | st `elem` safes mon = SAFETY
  | otherwise = OPEN

-- | The input variables of a monitor.
inputs :: Monitor -> Set Symbol
inputs = Vars.inputs . variables

-- | The set of states of a monitor.
states :: Monitor -> Set State
states = Map.keysSet . stateLabel
---------------------------------------------------------------------------------------------------
