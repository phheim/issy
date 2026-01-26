---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Translation.DOA
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

module Issy.Translation.DOA
  ( State
  , Acceptance(..)
  , Transition
  , DOA
  , -- Printing
    stateName
  , -- Accession methods
    alphabet
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

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

-- Deterministic Omega Automaton
newtype State =
  State Int
  deriving (Eq, Ord, Show)

-- A Transition is a sort of DNF. It contains a disjunction of all
-- possible successors, where a successors is a state and a transition
-- condition, which itself is a conjunction of atomic proposition literals
type Transition a = Set (Set (a, Bool), State)

stateName :: State -> String
stateName (State n) = "q" ++ show n

data Acceptance
  = Safety (Set State)
  | Buechi (Set State)
  | Parity (Map State Word)
  deriving (Eq, Ord, Show)

data DOA a = DOA
  { doaStates :: Set State
  , doaAlphabet :: Set a
  , doaInitial :: State
  , doaTrans :: Map State (Transition a)
  , doaAccept :: Acceptance
  } deriving (Eq, Ord, Show)

------------------------------------------------------------------------------
states :: Ord a => DOA a -> Set State
states = doaStates

stateList :: Ord a => DOA a -> [State]
stateList = Set.toList . states

initial :: Ord a => DOA a -> State
initial = doaInitial

alphabet :: Ord a => DOA a -> Set a
alphabet = doaAlphabet

trans :: Ord a => DOA a -> State -> Transition a
trans doa state =
  case doaTrans doa !? state of
    Just trans -> trans
    Nothing -> error "DOA.trans was applied to non-matching state"

acceptance :: Ord a => DOA a -> Acceptance
acceptance = doaAccept

transAPs :: Ord a => Transition a -> Set a
transAPs = Set.unions . map (Set.map fst . fst) . Set.toList

branch :: Ord a => Transition a -> a -> (Transition a, Transition a)
branch t ap =
  let tt = Set.filter (notElem (ap, False) . fst) t
      tf = Set.filter (notElem (ap, True) . fst) t
      clean (conj, q) = (Set.filter ((/= ap) . fst) conj, q)
   in (Set.map clean tt, Set.map clean tf)

------------------------------------------------------------------------------
-- | 'initDOA' inialized a deterministic Omega Automaton with an alphabet and
-- a given number of states. All states will be self looping and the
-- automaton will reject everything.
initDOA :: Ord a => Set a -> Int -> DOA a
initDOA alphabet stateCnt =
  let states = Set.fromList $ map State [1 .. max stateCnt 1]
   in DOA
        { doaStates = states
        , doaInitial = State 1
        , doaAlphabet = alphabet
        , doaTrans = Map.fromSet (\q -> Set.singleton (Set.empty, q)) states
        , doaAccept = Safety Set.empty
        }

setInitial :: Ord a => State -> DOA a -> DOA a
setInitial state doa
  | state `elem` states doa = doa {doaInitial = state}
  | otherwise = error "try to set non-exisiting inital state"

setTrans :: Ord a => State -> Transition a -> DOA a -> DOA a
setTrans state trans doa
  | not (transAPs trans `Set.isSubsetOf` alphabet doa) =
    error "try to set transistion with non-existent atomic proposition"
  | not (Set.map snd trans `Set.isSubsetOf` states doa) =
    error "try to set transistion with non-existent states"
  | otherwise = doa {doaTrans = Map.insert state trans (doaTrans doa)}

setAcceptance :: Ord a => Acceptance -> DOA a -> DOA a
setAcceptance accept doa =
  let occurs =
        case accept of
          Safety safe -> safe
          Buechi reps -> reps
          Parity colors -> Map.keysSet colors
   in if occurs `Set.isSubsetOf` states doa
        then toSafety $ doa {doaAccept = accept}
        else error "try to set acceptance with non-existent states"

------------------------------------------------------------------------------
toSafety :: Ord a => DOA a -> DOA a
toSafety doa =
  case doaAccept doa of
    Safety _ -> doa
    Parity _ -> doa
    Buechi reps ->
      let nonReps = doaStates doa `Set.difference` reps
       in if all (isSelfLoop doa) nonReps
            then doa {doaAccept = Safety reps}
            else doa

isSelfLoop :: Ord a => DOA a -> State -> Bool
isSelfLoop doa state = trans doa state == Set.singleton (Set.empty, state)
------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
