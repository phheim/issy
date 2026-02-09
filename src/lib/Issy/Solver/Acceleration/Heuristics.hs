---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Acceleration.Heuristics
-- Description : Acceleration heuristic
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module collects all the heuristics used to do acceleration.
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.Heuristics
  ( -- Creation
    Heur
  , forVisits
  , simple
  , --  General
    loopArenaSize
  , loopArenaIncludeSucc
  , iterAMaxCPres
  , -- For geometric acceleration
    minEpsilon
  , invariantIterations
  , manhattenTermCount
  , boxOptSmtTO
  , invSatModelTO
  , -- For combing acceleration
    ggaIters
  , ggaDepth
  , ggaMaxIntersect
  , ggaMaxLexiUnionSize
  , ggaMaxLexiUnion
  , -- For uninterpreted functions
    lemmaResolveTO
  , templatePattern
  , nestingDepth
  ) where

---------------------------------------------------------------------------------------------------
import Data.List (genericReplicate)
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (accelerationLevel)
import Issy.Solver.GameInterface

---------------------------------------------------------------------------------------------------
-- | Abstract representation of a heuristic configuration.
data Heur = Heur
  { visitCnt :: Int
  , config :: Config
  , locCnt :: Int
  }

-- | Create a simple heurisitic setting. This is somewhat limited.
simple :: Config -> Arena -> Heur
simple conf arena = forVisits conf arena 1

-- | Create a heuristic setting for a number of location visists in the top-level
-- attractor computation. This should ususally be used.
forVisits :: Config -> Arena -> Int -> Heur
forVisits conf arena visits =
  Heur {visitCnt = visits, config = conf, locCnt = Set.size (locations arena)}

---------------------------------------------------------------------------------------------------
-- General Acceleration
---------------------------------------------------------------------------------------------------
-- | Size of the loop arena.
loopArenaSize :: Heur -> Int
loopArenaSize heur =
  case accelerationLevel (config heur) of
    0 -> 1
    1
      | locCnt heur < 10 * accelerationDist heur -> 1
      | otherwise -> 2
    _ -> 1 + (locCnt heur `div` (10 * accelerationDist heur))

-- | Size of the successors included in the loop arena.
loopArenaIncludeSucc :: Heur -> Bool
loopArenaIncludeSucc heur = visitCnt heur >= 1

-- | Number of enforcement steps in iterA.
iterAMaxCPres :: Heur -> Int
iterAMaxCPres _ = 1

accelerationDist :: Heur -> Int
accelerationDist _ = 4 -- magic value

---------------------------------------------------------------------------------------------------
-- Geometric Acceleration
---------------------------------------------------------------------------------------------------
-- | Minimum distance between to real numbers in step relation
-- (for geometric and polyhedra acceleration).
minEpsilon :: Heur -> Rational
minEpsilon _ = 1 % (10 ^ (3 :: Int))

-- | Timeout for the box optimization Max-SMT query (for geometric acceleration).
boxOptSmtTO :: Heur -> Maybe Int
boxOptSmtTO _ = Just 20

-- | Limit of invariant computation iterations (for geometric acceleration).
invariantIterations :: Heur -> Int
invariantIterations _ = 2

-- | Number of Manhattan distance terms (for geometric acceleration).
manhattenTermCount :: Heur -> Int
manhattenTermCount _ = 2

-- | Timeout to compute a model for computing invariants (for geometric acceleration).
invSatModelTO :: Heur -> Maybe Int
invSatModelTO _ = Just 20

---------------------------------------------------------------------------------------------------
-- Polyhedra Acceleration
---------------------------------------------------------------------------------------------------
-- | Number of invariant iterations (for polyhedra acceleration).
ggaIters :: Heur -> Int
ggaIters heur
  | visitCnt heur == 0 = 0
  | visitCnt heur == 1 = 0
  | visitCnt heur == 2 = 0
  | visitCnt heur == 3 = 1
  | visitCnt heur == 4 = 1
  | otherwise = 1

-- | Number of recursive nesting (for polyhedra acceleration).
ggaDepth :: Heur -> Int
ggaDepth heur
  | visitCnt heur == 0 = 0
  | visitCnt heur == 1 = 0
  | visitCnt heur == 2 = 1
  | visitCnt heur == 3 = 0
  | visitCnt heur == 4 = 1
  | otherwise = 2

-- | Limit of lemma intersection conjuncts (for polyhedra acceleration).
ggaMaxIntersect :: Heur -> Int
ggaMaxIntersect heur
  | visitCnt heur == 0 = 3
  | visitCnt heur == 1 = 2
  | visitCnt heur == 2 = 2
  | visitCnt heur == 3 = 2
  | visitCnt heur == 4 = 2
  | otherwise = 3

-- | Limit of lemma union disjuncts (for polyhedra acceleration).
ggaMaxLexiUnionSize :: Heur -> Int
ggaMaxLexiUnionSize heur
  | visitCnt heur == 0 = 2
  | visitCnt heur == 1 = 3
  | visitCnt heur == 2 = 2
  | visitCnt heur == 3 = 2
  | visitCnt heur == 4 = 2
  | otherwise = 3

-- | Limit on number of considered union lemmas (for polyhedra acceleration).
ggaMaxLexiUnion :: Heur -> Int
ggaMaxLexiUnion _ = 10

---------------------------------------------------------------------------------------------------
-- UF Acceleration
---------------------------------------------------------------------------------------------------
-- | Limit of nesting depth for iterA (uninterpreted function acceleration).
nestingDepth :: Heur -> Int
nestingDepth heur
  | visitCnt heur <= 10 * accelerationDist heur = 0 -- Try once without nesting
  | otherwise = (visitCnt heur `div` (100 * accelerationDist heur)) + 1

-- | SMT solver timeout for finding an acceleration lemma (uninterpreted function acceleration).
lemmaResolveTO :: Heur -> Maybe Int
lemmaResolveTO heur = Just $ visitCnt heur ^ (2 :: Int)

-- | Pattern for templates of (uninterpreted function acceleration).
templatePattern :: Heur -> (Integer, [Integer])
templatePattern heur =
  let dis = accelerationDist heur * accelerationDist heur
   in (3 + toInteger (visitCnt heur `div` dis), genericReplicate (visitCnt heur `div` dis) 2)
---------------------------------------------------------------------------------------------------
