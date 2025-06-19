---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.EnforcementSummaries
-- Description : Implementaion of Enforcement Summaries
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.EnforcementSummaries
  ( EnfSt
  , empty
  , trySummary
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

-- Entries for tried things:
--  -> player + arena + location (isomorphy reachability!)
--  -> result state: failed/summary entry (meta vars, trarget, prog, result formula)
newtype EnfSt = EnfSt
  { summaries :: [EnforcementSum]
  }

empty :: EnfSt
empty = EnfSt {summaries = []}

--------------------------------------------------------------------------------------------------- 
-- Application & Computation
--------------------------------------------------------------------------------------------------- 
-- TODO: document, do not QELIM result, that is resposibility of caller
trySummary :: Config -> Player -> Arena -> Loc -> EnfSt -> SymSt -> IO (EnfSt, Maybe (Term, SyBo))
trySummary = error "TODO IMPLEMENT, check if already computed"
    -- What this does:
    -- -> check if summary has been tried to computed and if matching exists
    --      -> if tried but no matching, give up
    --      -> if matching exits apply it
    -- -> if no matching exits try to compute
    -- --> give up

--------------------------------------------------------------------------------------------------- 
-- Detection
--------------------------------------------------------------------------------------------------- 
isSubgameFrom :: (Loc, Arena) -> (Loc, Arena) -> Maybe (Loc -> Loc)
isSubgameFrom (lSub, arenaSub) (l, arena) = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Application
---------------------------------------------------------------------------------------------------
-- TODO: Add correspondence of locations!
-- Maybe have no-io verision for accleration attractor
-- make applicability a DOCUMENTED precondition!!!
applyIn :: Config -> EnforcementSum -> Arena -> SymSt -> IO (Maybe (Loc, Term))
applyIn = error "TODO IMPLEMENT -> QELIM should go somewhere else"

-- TODO: Be sure that location match!!!
-- TODO: idea, summaries are computed based on getting them
applySummary :: EnforcementSum -> SymSt -> (Term, SyBo)
applySummary = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------------------------- 
computeSumIn :: Config -> Arena -> Loc -> IO (Maybe EnforcementSum)
computeSumIn =
  error
    "TODO IMPLEMENT: build sub-game with additional variables, and equality contraints! attractor computation + acceleration with new computation (cyclic dependency!)"
---------------------------------------------------------------------------------------------------
