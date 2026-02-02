---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Translation.DOA
-- Description : Representation of deterministic omega automata
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module contains a data-structure and basic functionalities for deterministic
-- omega automat with safety, Büchi, and parity acceptance conditions.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Translation.DOA
  ( State
  , Acceptance(..)
  , Transition
  , DOA
  , -- Printing
    stateName
  , -- Accession methods
    atoms
  , states
  , stateList
  , initial
  , trans
  , acceptance
  , -- Transition operations
    transAPs
  , branch
  , -- Construction
    initDOA
  , setInitial
  , setTrans
  , setAcceptance
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

---------------------------------------------------------------------------------------------------
-- | Represents a state in a 'DOA'. Note that equality of a 'State' is always only in the
-- context of a single 'DOA'. Two states of different 'DOA's can be equal in the program without
-- being related by semantics.
newtype State =
  State Int
  deriving (Eq, Ord, Show)

-- | A 'Transition' is a sort of DNF. It contains a disjunction of all
-- possible successors, where a successors is a state and a transition
-- condition, which itself is a conjunction of atomic proposition literals
type Transition a = Set (Set (a, Bool), State)

-- | 'String' representation of a 'State'
stateName :: State -> String
stateName (State n) = "q" ++ show n

-- | These are the different acceptance conditions available for 'DOA'
data Acceptance
  = Safety (Set State)
  -- ^ safety acceptance with safe set,
  -- a run is accepted if all states in the run always stays safe set
  | Buechi (Set State)
  -- ^ Büchi acceptance with a recurrence set,
  -- a run is accepted if some state in the recurrence set is passed through
  -- infinitely often in the run
  | ParityMaxOdd (Map State Word)
  -- ^ parity acceptance condition with colors (max odd),
  -- a run is accepted if the maximum color of all state that the run visits
  -- infinitely often is odd, note that all state in the respective 'DOA'
  -- are assumed to have a color
  deriving (Eq, Ord, Show)

-- | Representation of a deterministic omega automaton over an arbitrary set of atomic
-- propositions. Note that the atomic propositions must implement 'Ord'.
data DOA a = DOA
  { doaStates :: Set State
  , doaAtoms :: Set a
  , doaInitial :: State
  , doaTrans :: Map State (Transition a)
  , doaAccept :: Acceptance
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- | the set of states of a 'DOA'
states :: Ord a => DOA a -> Set State
states = doaStates

-- | list of all state of a 'DOA'
stateList :: Ord a => DOA a -> [State]
stateList = Set.toList . states

-- | the initial state of a 'DOA'
initial :: Ord a => DOA a -> State
initial = doaInitial

-- | the atomic propositions of a 'DOA'
atoms :: Ord a => DOA a -> Set a
atoms = doaAtoms

-- | the outgoing transition relation from a given 'State'
trans :: Ord a => DOA a -> State -> Transition a
trans doa state =
  case doaTrans doa !? state of
    Just trans -> trans
    Nothing -> error "DOA.trans was applied to non-matching state"

-- | the acceptance condition of of 'DOA'
acceptance :: Ord a => DOA a -> Acceptance
acceptance = doaAccept

---------------------------------------------------------------------------------------------------
-- | the atomic proposition that appear on a given transition relation
transAPs :: Ord a => Transition a -> Set a
transAPs = Set.unions . map (Set.map fst . fst) . Set.toList

-- | computes the successor transition upon branching of a given atomic proposition.
-- The first returned transition is the "remaining" transition if the atom is true,
-- the second one if it is false.
branch :: Ord a => Transition a -> a -> (Transition a, Transition a)
branch t ap =
  let tt = Set.filter (notElem (ap, False) . fst) t
      tf = Set.filter (notElem (ap, True) . fst) t
      clean (conj, q) = (Set.filter ((/= ap) . fst) conj, q)
   in (Set.map clean tt, Set.map clean tf)

---------------------------------------------------------------------------------------------------
-- | Initializes a deterministic Omega Automaton with atomic propositions and a given
-- number of states. All states will be self looping and the automaton will reject everything.
initDOA :: Ord a => Set a -> Int -> DOA a
initDOA atoms stateCnt =
  let states = Set.fromList $ map State [1 .. max stateCnt 1]
   in DOA
        { doaStates = states
        , doaInitial = State 1
        , doaAtoms = atoms
        , doaTrans = Map.fromSet (\q -> Set.singleton (Set.empty, q)) states
        , doaAccept = Safety Set.empty
        }

-- | Sets the initial state to a give state. Might return an error if the state is not
-- a state of the 'DOA'.
setInitial :: Ord a => State -> DOA a -> DOA a
setInitial state doa
  | state `elem` states doa = doa {doaInitial = state}
  | otherwise = error "try to set non-exisiting inital state"

-- | Sets the transition from an state. Might return an error of the state or atomic
-- propositions are not in the 'DOA'.
--  Warning: The transition is assumed to be deterministic!
setTrans :: Ord a => State -> Transition a -> DOA a -> DOA a
setTrans state trans doa
  | not (transAPs trans `Set.isSubsetOf` atoms doa) =
    error "try to set transistion with non-existent atomic proposition"
  | not (Set.map snd trans `Set.isSubsetOf` states doa) =
    error "try to set transistion with non-existent states"
  | otherwise = doa {doaTrans = Map.insert state trans (doaTrans doa)}

-- | Sets the acceptance condition. Might return an error if the states in the
-- condition are not in the 'DOA'
setAcceptance :: Ord a => Acceptance -> DOA a -> DOA a
setAcceptance accept doa =
  let occurs =
        case accept of
          Safety safe -> safe
          Buechi reps -> reps
          ParityMaxOdd colors -> Map.keysSet colors
   in if occurs `Set.isSubsetOf` states doa
        then toSafety $ doa {doaAccept = accept}
        else error "try to set acceptance with non-existent states"

---------------------------------------------------------------------------------------------------
-- | Tries to transform the 'Acceptance' of a 'DOA' into safety if this does not change the
-- language accepted by the 'DOA'. If this is not possible, the 'DOA' remains unchanged.
toSafety :: Ord a => DOA a -> DOA a
toSafety doa =
  case doaAccept doa of
    Safety _ -> doa
    ParityMaxOdd _ -> doa
    Buechi reps ->
      let nonReps = doaStates doa `Set.difference` reps
       in if all (isSelfLoop doa) nonReps
            then doa {doaAccept = Safety reps}
            else doa

isSelfLoop :: Ord a => DOA a -> State -> Bool
isSelfLoop doa state = trans doa state == Set.singleton (Set.empty, state)
---------------------------------------------------------------------------------------------------
