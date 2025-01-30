---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.Strengthening
-- Description : Alogorithms for strengtening invariants for acceleration
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.Strengthening
  ( strengthenBool
  , strengthenSimple
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad ((<=<))
import Data.Bifunctor (first)

import Issy.Config (Config)
import Issy.Logic.FOL (Function(PredefF), Symbol, Term(Func))
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.SMT as SMT

---------------------------------------------------------------------------------------------------
-- | 'strengthenSimple' strengthens the given 'Term' in different easy syntactic ways
strengthenSimple :: Term -> [Term]
strengthenSimple = go
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
          [FOL.func "<" [a1, a2], FOL.func ">" [a1, a2]]
        t -> [t]

---------------------------------------------------------------------------------------------------
-- | 'strengthenBool' strengthens the given 'Term' in different easy syntactic ways but instead
-- of explicitly listinge them builds an SMT query
strengthenBool :: Config -> Symbol -> Term -> IO Term
strengthenBool conf prefix =
  (SMT.simplify conf . fst . label (0 :: Int)) <=< (SMT.simplify conf . expand)
  where
    expand t =
      case t of
        Func (PredefF "not") [Func (PredefF "=") [a1, a2]] ->
          FOL.orf [FOL.func "<" [a1, a2], FOL.func ">" [a1, a2]]
        Func f args -> Func f $ map expand args
        t -> t
    label cnt t =
      case t of
        Func (PredefF "or") args ->
          first (FOL.orf . reverse)
            $ foldl
                (\(args, cnt) -> first ((: args) . addSelector cnt) . label (cnt + 1))
                ([], cnt)
                args
        Func f args ->
          first (Func f . reverse)
            $ foldl (\(args, cnt) -> first (: args) . label cnt) ([], cnt) args
        t -> (t, cnt)
    addSelector cnt t = FOL.andf [t, FOL.bvarT (prefix ++ show cnt)]
---------------------------------------------------------------------------------------------------
