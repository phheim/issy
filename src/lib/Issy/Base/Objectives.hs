{-# LANGUAGE LambdaCase #-}

module Issy.Base.Objectives
  ( Objective(..)
  , WinningCondition(..)
  , mapWC
  , isSafety
  ) where

import Data.Map.Strict (Map)
import Data.Set (Set)

import Issy.Base.Locations (Loc)

data Objective = Objective
  { initialLoc :: Loc
  , winningCond :: WinningCondition
  } deriving (Eq, Ord, Show)

data WinningCondition
  = Safety (Set Loc)
  -- ^ safety winning condition with locations that should not be left
  | Reachability (Set Loc)
  -- ^ reachability winning condition with location that should be reached
  | Buechi (Set Loc)
  -- ^ Büchi winning condition with location that should be reached 
  -- infinitely often (i.e. G F set)
  | CoBuechi (Set Loc)
   -- ^ coBüchi winning condition with location that form some point on should
   -- never be left (i.e. F G set)
  | Parity (Map Loc Word)
   -- ^ Parity winning condition with coloring Omega. The system wins if the 
   -- maximal color visited infinitely often is even
  deriving (Eq, Ord, Show)

mapWC ::
     (Set Loc -> Set Loc) -> (Map Loc Word -> Map Loc Word) -> WinningCondition -> WinningCondition
mapWC mapSet mapMap =
  \case
    Safety ls -> Safety $ mapSet ls
    Reachability ls -> Reachability $ mapSet ls
    Buechi ls -> Buechi $ mapSet ls
    CoBuechi ls -> CoBuechi $ mapSet ls
    Parity rank -> Parity $ mapMap rank

isSafety :: Objective -> Bool
isSafety obj =
  case winningCond obj of
    Safety _ -> True
    _ -> False
