---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Acceleration.Base
-- Description : Simple acceleration lemma interface
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the shared data structures and algorithm for lemma based acceleration.
-- This includes generalized acceleration lemmas, as well as combinations thereof.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.Base
  ( AccelLemma(..)
  , unprime
  , primeT
  , isMeaningfull
  , -- Combinations
    addInvar
  , intersections
  , lexiUnions
  , chain
  , -- Combinator interface
    Combinator
  , toLemma
  , combToStr
  , combBase
  , combInv
  , combIntersect
  , combLexiUnion
  , combChain
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Prelude

import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)

---------------------------------------------------------------------------------------------------
-- | Representation of a (simple or general) acceleration lemma.
data AccelLemma = AccelLemma
  { base :: Term
  -- ^ The base starting set
  , step :: Term
  -- ^ The step condition. Since most algorithms we use do backward
  -- computations and application of lemmas the target valuation is with "normal"
  -- variables while the source valuation is "primed" (in contrast to the
  -- formal definition).
  , stay :: Term
  -- ^ The stay condition. This mainly applies for the non-simple
  -- version of acceleration lemmas. If stay is not needed, it can be set equal
  -- to step. The priming works similar to the step condition.
  , conc :: Term
  -- ^  The conclusion term
  , prime :: Symbol
  -- ^ The priming prefix for "prime variables" in the step relation
  } deriving (Eq, Ord, Show)

-- | Replace the primed (i.e. previous step states) in a term by the
-- state variable version. This is usually done at the end of a loop game
-- attractor computation.
unprime :: AccelLemma -> Term -> Term
unprime = FOL.removePref . prime

-- | Replace all state variable symbols in a term by a prefix-primed one
primeT :: Variables -> Symbol -> Term -> Term
primeT vars prim =
  FOL.mapSymbol
    (\s ->
       if Vars.isStateVar vars s
         then prim ++ s
         else s)

-- | Check if a lemma is somewhat meaningful, i.e. it actually represents 
-- something to be added.
isMeaningfull :: Config -> AccelLemma -> IO Bool
isMeaningfull conf lemma = SMT.sat conf $ FOL.andf [conc lemma, FOL.neg (base lemma)]

---------------------------------------------------------------------------------------------------
-- Combinations
---------------------------------------------------------------------------------------------------
-- | Add an invariant to an acceleration lemmas (Lemma 4 in TACAS'26). In order for this
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

-- | Compute the intersection of several acceleration lemmas (Lemma 1 in TACAS'26).
-- If the priming symbol of the lemmas do not match, this methods is undefined.
intersections :: Variables -> [AccelLemma] -> AccelLemma
intersections vars =
  \case
    [] -> error "assert: list of lemmas cannot be empty"
    lem:lemr
      | any ((/= prime lem) . prime) lemr -> error "assert: prime has to be the same"
      | otherwise ->
        let lemmas = lem : lemr
            prm = primeT vars (prime lem)
         in AccelLemma
              { prime = prime lem
              , base = FOL.andfL lemmas base
              , conc = FOL.andfL lemmas conc
              , stay = FOL.andfL lemmas stay
              , step =
                  FOL.orfL (singleOut lemmas) $ \(gal, others) ->
                    FOL.andf [step gal, prm (FOL.neg (base gal)), FOL.andfL others stay]
              }
  where
    singleOut :: [a] -> [(a, [a])]
    singleOut = go []
      where
        go acc =
          \case
            [] -> []
            x:xr -> (x, acc ++ xr) : go (acc ++ [x]) xr

-- | Compute the lexicographic union of several acceleration lemmas (Lemma 2 in TACAS'26).
-- If the priming symbol of the lemmas do not match, this methods is undefined.
lexiUnions :: Variables -> [AccelLemma] -> AccelLemma
lexiUnions = foldr1 . lexiUnion

lexiUnion :: Variables -> AccelLemma -> AccelLemma -> AccelLemma
lexiUnion vars lemmaA lemmaB
  | prime lemmaA /= prime lemmaB = error "assert: prime needs to be the same"
  | otherwise =
    AccelLemma
      { base = FOL.orf [base lemmaA, base lemmaB]
      , conc = FOL.orf [conc lemmaA, conc lemmaB]
      , stay = FOL.andf [stay lemmaA, stay lemmaB]
      , step =
          FOL.orf
            [ FOL.andf [prm (conc lemmaA), step lemmaA]
            , FOL.andf [stay lemmaA, step lemmaB, prm (conc lemmaB)]
            ]
      , prime = prime lemmaA
      }
  where
    prm = primeT vars (prime lemmaA)

-- | Compute the chaining of a main lemma with a sub-lemma (Lemma 3 in TACAS'26).
-- If the priming symbol of the lemmas do not match, this methods is undefined.
chain :: Variables -> AccelLemma -> AccelLemma -> AccelLemma
chain vars main sub
  | prime main /= prime sub = error "assert: prime needs to be the same"
  | otherwise =
    AccelLemma
      { base = base main
      , conc = conc main
      , stay = FOL.andf [stay main, stay sub]
      , step =
          FOL.orf
            [step main, FOL.andf [stay main, prm (conc sub), prm (FOL.neg (base sub)), step sub]]
      , prime = prime main
      }
  where
    prm = primeT vars (prime main)

---------------------------------------------------------------------------------------------------
-- Combinators
---------------------------------------------------------------------------------------------------
-- | Abstract data-structure to represent the above combination of lemmas. This data-structure
-- is meant to first build abstract/algebraic representation of the combinations and use those
-- to then compute the actual combination. Furthermore, this allows to first build combinations
-- of other objects (e.g. target terms) that are only later instantiated to lemmas.
data Combinator a
  = CBase a
  | CInv Term (Combinator a)
  | CChain (Combinator a) (Combinator a)
  | CLexiUnion [Combinator a]
  | CIntersection [Combinator a]
  deriving (Eq, Ord, Show)

-- | Turn an abstract combination of lemmas into a concrete lemma.
toLemma :: Variables -> (a -> AccelLemma) -> Combinator a -> AccelLemma
toLemma vars mkGAL = go
  where
    go =
      \case
        CBase a -> mkGAL a
        CInv inv a -> addInvar vars inv (go a)
        CChain a b -> chain vars (go a) (go b)
        CLexiUnion gs -> lexiUnions vars (map go gs)
        CIntersection gs -> intersections vars (map go gs)

-- | Pretty print a combination.
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

-- | Construct a singleton combination.
combBase :: a -> Combinator a
combBase = CBase

-- | Construct a combination that corresponds to 'addInvar'.
combInv :: Term -> Combinator a -> Combinator a
combInv inv
  | inv == FOL.true = id
  | otherwise =
    \case
      CInv oinv comb -> CInv (FOL.andf [inv, oinv]) comb
      comb -> CInv inv comb

-- | Construct a combination that corresponds to 'intersections'.
combIntersect :: [Combinator a] -> Combinator a
combIntersect =
  \case
    [] -> error "assert: not allowed"
    [c] -> c
    cs -> CIntersection cs

-- | Construct a combination that corresponds to 'lexiUnions'.
combLexiUnion :: [Combinator a] -> Combinator a
combLexiUnion =
  \case
    [] -> error "assert: not allowed"
    [c] -> c
    cs -> CLexiUnion cs

-- | Construct a combination that corresponds to 'chain'.
combChain :: Combinator a -> Combinator a -> Combinator a
combChain = CChain
---------------------------------------------------------------------------------------------------
