---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.Base
-- Description : Shared data structures and algorithm for lemma based acceleration
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.Base where

---------------------------------------------------------------------------------------------------
import Issy.Prelude

import qualified Issy.Base.Variables as Vars
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- | 'AccelLemma' represents a simple acceleration lemma
data AccelLemma = AccelLemma
  { base :: Term
  -- ^ 'base' is the base starting set
  , step :: Term
  -- ^ 'step' is the step condition. Since most algorithms we use do backward 
  -- compuations and application of lemmas the target valuation is with "normal" variables 
  -- while the source valuation is "primed" (in contrast to the formal definition).
  , conc :: Term
  -- ^ 'conc' is the conclusion term
  , prime :: Symbol
  -- ^ 'prime' is the priming prefix for "prime variables" in the step relation
  } deriving (Eq, Ord, Show)

addInv :: Variables -> Term -> AccelLemma -> AccelLemma
addInv _ inv al =
  AccelLemma
    { base = FOL.andf [base al, inv]
    , conc = FOL.andf [conc al, inv]
    , step = FOL.andf [step al, inv]
    , prime = prime al
    }

unprime :: AccelLemma -> Term -> Term
unprime = FOL.removePref . prime

primeT :: Variables -> Symbol -> Term -> Term
primeT vars prim =
  FOL.mapSymbol
    (\s ->
       if Vars.isStateVar vars s
         then prim ++ s
         else s)
---------------------------------------------------------------------------------------------------
