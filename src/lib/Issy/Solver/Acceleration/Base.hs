---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.Base
-- Description : Shared data structures and algorithm for lemma based acceleration
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.Base
  ( AccelLemma(..)
  , unprime
  , primeT
  , addInvar
  , chain
  , lexiUnions
  , intersections
  , Combinator
  , toLemma
  , combToStr
  , combBase
  , combInv
  , combChain
  , combLexiUnion
  , combIntersect
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Prelude

import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Printers.SMTLib as SMTLib (toString)

---------------------------------------------------------------------------------------------------
-- | 'AccelLemma' represents a (simple or general) acceleration lemma
data AccelLemma = AccelLemma
  { base :: Term
  -- ^ 'base' is the base starting set
  , step :: Term
  -- ^ 'step' is the step condition. Since most algorithms we use do backward 
  -- compuations and application of lemmas the target valuation is with "normal"
  -- variables while the source valuation is "primed" (in contrast to the 
  -- formal definition).
  , stay :: Term
  -- ^ 'stay' is the stay condition. This mainly applies for the non-simple 
  -- version of acceleration lemmas. If stay is not needed, it can be set equal
  -- to step. The priming works similiar to the step condition.
  , conc :: Term
  -- ^ 'conc' is the conclusion term
  , prime :: Symbol
  -- ^ 'prime' is the priming prefix for "prime variables" in the step relation
  } deriving (Eq, Ord, Show)

-- | 'unprime' replaces the primed (i.e. previous step states) in a term by the
-- state variable version. This is usually done at the end of a loop game 
-- attractor computation.
unprime :: AccelLemma -> Term -> Term
unprime = FOL.removePref . prime

-- | 'primeT' replaces all state variable symbols in a term by a 
-- prefix-primed one
primeT :: Variables -> Symbol -> Term -> Term
primeT vars prim =
  FOL.mapSymbol
    (\s ->
       if Vars.isStateVar vars s
         then prim ++ s
         else s)

-- | 'addInvar' adds an invariant to an acceleration lemmas. In order for this
-- to be correct the free variables in the invariant have to be state variables
-- in the given variable set.
addInvar :: Variables -> Term -> AccelLemma -> AccelLemma
addInvar _ inv lemma =
  lemma
    { base = FOL.andf [base lemma, inv]
    , conc = FOL.andf [conc lemma, inv]
    , stay = FOL.andf [stay lemma, inv]
    , step = FOL.andf [step lemma, inv]
    }

-- | TODO condition: all priming is the same!, main first
chain :: Variables -> AccelLemma -> AccelLemma -> AccelLemma
chain vars main sub =
  AccelLemma
    { base = base main
    , conc = FOL.andf [conc main, conc sub]
    , stay = FOL.andf [stay main, stay sub]
    , step =
        FOL.orf
          [FOL.andf [step main, conc sub], FOL.andf [prm (FOL.neg (base sub)), stay main, step sub]]
    , prime = prime main
    }
  where
    prm = primeT vars (prime main)

-- | TODO condition: all priming is the same!
lexiUnion :: AccelLemma -> AccelLemma -> AccelLemma
lexiUnion lemmaA lemmaB =
  AccelLemma
    { base = FOL.orf [base lemmaA, base lemmaB]
    , conc = FOL.orf [conc lemmaA, conc lemmaB]
    , stay = FOL.andf [stay lemmaA, stay lemmaB]
    , step = FOL.orf [step lemmaA, FOL.andf [stay lemmaA, step lemmaB]]
    , prime = prime lemmaA
    }

-- TODO condition: all priming is the same!, list not empty
lexiUnions :: [AccelLemma] -> AccelLemma
lexiUnions = foldr1 lexiUnion

-- TODO condition: all priming is the same!, list not empty
intersections :: Variables -> [AccelLemma] -> AccelLemma
intersections vars lemmas =
  let newConc = FOL.andfL lemmas conc
      newStep =
        FOL.orfL (singleOut lemmas) $ \(gal, others) ->
          FOL.andf [step gal, prm (FOL.neg (base gal)), FOL.andfL others stay]
   in AccelLemma
        { base = FOL.andfL lemmas base
        , stay = FOL.andfL lemmas stay
        , step = FOL.andf [newConc, newStep]
        , conc = newConc
        , prime = prime (head lemmas)
        }
  where
    prm = primeT vars (prime (head lemmas))
    --
    singleOut :: [a] -> [(a, [a])]
    singleOut = go []
      where
        go acc =
          \case
            [] -> []
            x:xr -> (x, acc ++ xr) : go (acc ++ [x]) xr

---------------------------------------------------------------------------------------------------
-- Combinators
---------------------------------------------------------------------------------------------------
data Combinator a
  = CBase a
  | CInv Term (Combinator a)
  | CChain (Combinator a) (Combinator a)
  | CLexiUnion [Combinator a]
  | CIntersection [Combinator a]
  deriving (Eq, Ord, Show)

toLemma :: Variables -> (a -> AccelLemma) -> Combinator a -> AccelLemma
toLemma vars mkGAL = go
  where
    go =
      \case
        CBase a -> mkGAL a
        CInv inv a -> addInvar vars inv (go a)
        CChain a b -> chain vars (go a) (go b)
        CLexiUnion gs -> lexiUnions (map go gs)
        CIntersection gs -> intersections vars (map go gs)

combBase :: a -> Combinator a
combBase = CBase

combChain :: Combinator a -> Combinator a -> Combinator a
combChain = CChain

combInv :: Term -> Combinator a -> Combinator a
combInv inv
  | inv == FOL.true = id
  | otherwise =
    \case
      CInv oinv comb -> CInv (FOL.andf [inv, oinv]) comb
      comb -> CInv inv comb

combLexiUnion :: [Combinator a] -> Combinator a
combLexiUnion =
  \case
    [] -> error "assert: not allowed"
    [c] -> c
    cs -> CLexiUnion cs

combIntersect :: [Combinator a] -> Combinator a
combIntersect =
  \case
    [] -> error "assert: not allowed"
    [c] -> c
    cs -> CIntersection cs

combToStr :: (a -> String) -> Combinator a -> String
combToStr toStr = go
  where
    go =
      \case
        CBase a -> "[Base " ++ toStr a ++ "]"
        CInv inv a -> "[Inv " ++ SMTLib.toString inv ++ " on " ++ go a ++ "]"
        CChain a b -> "[Chain " ++ go a ++ " with " ++ go b ++ "]"
        CLexiUnion xs -> "[LexUnion" ++ concatMap ((' ' :) . go) xs ++ "]"
        CIntersection xs -> "[Intersect" ++ concatMap ((' ' :) . go) xs ++ "]"
---------------------------------------------------------------------------------------------------
