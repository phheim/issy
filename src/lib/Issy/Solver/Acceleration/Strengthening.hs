---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.Strengthening
-- Description : Alogorithms for strengtening invariants for acceleration
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.Strengthening
  ( strengthenConstr
  , strengthenSimple
  ) where

import Issy.Config (Config)
---------------------------------------------------------------------------------------------------
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- | 'strengthenConstr' constraints tries to compute a as weak a possible realizations for
-- the uninterpreted predicate symbol such that it satisfies the given contraint.
strengthenConstr :: Config -> Symbol -> [Sort] -> Term -> [IO Term]
strengthenConstr _ _ _ _ = [] -- TODO IMPLEMENT

---------------------------------------------------------------------------------------------------
-- | 'strengthenSimple' strengthens the given 'Term' in different easy syntactic ways
strengthenSimple :: Config -> Term -> [IO Term]
strengthenSimple _ _ = [] -- TODO IMPLEMENT
---------------------------------------------------------------------------------------------------
