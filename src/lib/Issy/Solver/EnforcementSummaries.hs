---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.EnforcementSummaries
-- Description : Implementaion of Enforcement Summaries
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.EnforcementSummaries
  ( EnforcementSum
  , EnforceStore
  , emptyESStore
  , applyIn
  , computeIn
  ) where

---------------------------------------------------------------------------------------------------
import Data.Set (Set)

import Issy.Base.SymbolicState (SymSt)
import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)

---------------------------------------------------------------------------------------------------
-- Definition
---------------------------------------------------------------------------------------------------
data EnforcementSum = EnforcementSum
  { arena :: Arena
  , location :: Loc
  , metaVars :: Set Symbol
  , enforcable :: Term
  -- ^ 'enforcable' is the main formula part!
  , target :: [(Loc, Term)] -- ALTERNATIVE SymbolicState?
  , sybo :: SyBo
  , player :: Player
  -- ^ 'sybo' is the book-kept strategy with meta variables
  }

newtype EnforceStore = EnforceStore
  { summaries :: [EnforcementSum]
  }

emptyESStore :: EnforceStore
emptyESStore = EnforceStore {summaries = []}

triedSummary :: EnforceStore -> Arena -> Loc -> Player -> Bool
triedSummary = error "TODO IMPLEMENT?, need equality check on arena"

findSummary :: EnforceStore -> Arena -> Loc -> Player -> Maybe EnforcementSum
findSummary = error "TODO IMPLEMENT"

isSubgameFrom :: (Loc, Arena) -> (Loc, Arena) -> Bool
isSubgameFrom (lSub, arenaSub) (l, arena) = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Application
---------------------------------------------------------------------------------------------------
-- TODO: Add correspondence of locations!
-- Maybe have no-io verision for accleration attractor
-- make applicability a DOCUMENTED precondition!!!
applyIn :: Config -> EnforcementSum -> Arena -> SymSt -> IO (Maybe (Loc, Term))
applyIn = error "TODO IMPLEMENT -> QELIM should go somewhere else"

applySummary :: EnforcementSum -> SymSt -> Term
applySummary = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------------------------- 
computeIn :: Config -> Arena -> Loc -> IO (Maybe EnforcementSum)
computeIn =
  error
    "TODO IMPLEMENT: build sub-game with additional variables, and equality contraints! attractor computation + acceleration with new computation (cyclic dependency!)"
---------------------------------------------------------------------------------------------------
