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

---------------------------------------------------------------------------------------------------
import Issy.Config (Config)
import Issy.Logic.FOL (Function(PredefF), Sort, Symbol, Term(Func))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT

---------------------------------------------------------------------------------------------------
-- | 'strengthenConstr' constraints tries to compute a as weak a possible realizations for
-- the uninterpreted predicate symbol such that it satisfies the given contraint.
strengthenConstr :: Config -> Symbol -> [Sort] -> Term -> [IO Term]
strengthenConstr _ _ _ _ = [] -- TODO IMPLEMENT

---------------------------------------------------------------------------------------------------
-- | 'strengthenSimple' strengthens the given 'Term' in different easy syntactic ways
strengthenSimple :: Config -> Term -> [IO Term]
strengthenSimple conf = map (SMT.simplify conf) . go
  where
    go t =
      case t of
        Func (PredefF "or") args -> t : concatMap go args
        Func (PredefF "and") [] -> [FOL.true]
        Func (PredefF "and") (a:ar) ->
          let r1 = go a
              r2 = go $ FOL.andf ar
           in [FOL.andf [e1, e2] | e1 <- r1, e2 <- r2]
        Func (PredefF "not") [Func (PredefF "=") [a1, a2]] ->
          [t, FOL.func "<" [a1, a2], FOL.func ">" [a1, a2]]
        t -> [t]
---------------------------------------------------------------------------------------------------
