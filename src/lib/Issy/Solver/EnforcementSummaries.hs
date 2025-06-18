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

-- TODO: Add enforcement summary store to ease mapping!!
---------------------------------------------------------------------------------------------------
-- Application
---------------------------------------------------------------------------------------------------
-- TODO: Add correspondence of locations!
applyIn :: Config -> EnforcementSum -> Arena -> SymSt -> IO (Maybe (Loc, Term))
applyIn = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------------------------- 
computeIn :: Config -> Arena -> Loc -> IO (Maybe EnforcementSum)
computeIn = error "TODO IMPLEMENT"
---------------------------------------------------------------------------------------------------
