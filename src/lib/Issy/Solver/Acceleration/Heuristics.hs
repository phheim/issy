module Issy.Solver.Acceleration.Heuristics
  ( Heur
  , forVisits
  , simple
  , loopArenaSize
  , loopArenaIncludeSucc
  , iterAMaxCPres
  , minEpsilon
  , invariantIterations
  , manhattenTermCount
  , boxOptSmtTO
  , ggaIters
  , ggaDepth
  , invSatModelTO
  , lemmaResolveTO
  , templatePattern
  , nestingDepth
  , ggaMaxIntersect
  , ggaMaxLexiUnionSize
  , ggaMaxLexiUnion
  ) where

import Data.List (genericReplicate)
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (accelerationLevel)
import Issy.Solver.GameInterface

data Heur = Heur
  { visitCnt :: Int
  , config :: Config
  , locCnt :: Int
  }

simple :: Config -> Arena -> Heur
simple conf arena = forVisits conf arena 1

forVisits :: Config -> Arena -> Int -> Heur
forVisits conf arena visits =
  Heur {visitCnt = visits, config = conf, locCnt = Set.size (locations arena)}

---
-- General Attractor
--- 
---
-- General Acceleration
--- 
loopArenaSize :: Heur -> Int
loopArenaSize heur =
  case accelerationLevel (config heur) of
    0 -> 1
    1
      | locCnt heur < 10 * accelerationDist heur -> 1
      | otherwise -> 2
    _ -> 1 + (locCnt heur `div` (10 * accelerationDist heur))

loopArenaIncludeSucc :: Heur -> Bool
loopArenaIncludeSucc heur = visitCnt heur `mod` (2 * accelerationDist heur) == 0

iterAMaxCPres :: Heur -> Int
iterAMaxCPres _ = 1

---
-- Geometric Acceleration
---
minEpsilon :: Heur -> Rational
minEpsilon _ = 1 % (10 ^ (3 :: Int))

boxOptSmtTO :: Heur -> Maybe Int
boxOptSmtTO _ = Just 20

invariantIterations :: Heur -> Int
invariantIterations _ = 2

manhattenTermCount :: Heur -> Int
manhattenTermCount _ = 2

invSatModelTO :: Heur -> Maybe Int
invSatModelTO _ = Just 20

---
-- Polyhedra Acceleration
---

ggaIters :: Heur -> Int
ggaIters heur
  | visitCnt heur == 0 = 0
  | visitCnt heur == 1 = 0
  | visitCnt heur == 2 = 0
  | visitCnt heur == 3 = 1
  | visitCnt heur < 10 = 1
  | otherwise = 1

ggaDepth :: Heur -> Int
ggaDepth heur
  | visitCnt heur == 0 = 0
  | visitCnt heur == 1 = 0
  | visitCnt heur == 2 = 1
  | visitCnt heur == 3 = 0
  | visitCnt heur < 10 = 1
  | otherwise = 2

ggaMaxIntersect :: Heur -> Int
ggaMaxIntersect heur
  | visitCnt heur == 0 = 3
  | visitCnt heur == 1 = 2
  | visitCnt heur == 2 = 2
  | visitCnt heur == 3 = 2
  | visitCnt heur < 10 = 2
  | otherwise = 3

ggaMaxLexiUnionSize :: Heur -> Int
ggaMaxLexiUnionSize heur
  | visitCnt heur == 0 = 2
  | visitCnt heur == 1 = 3
  | visitCnt heur == 2 = 2
  | visitCnt heur == 3 = 2
  | visitCnt heur < 10 = 2
  | otherwise = 3

ggaMaxLexiUnion :: Heur -> Int
ggaMaxLexiUnion _ = 10

---
-- UF Acceleration
---
accelerationDist :: Heur -> Int
accelerationDist _ = 4

nestingDepth :: Heur -> Int
nestingDepth heur
  | visitCnt heur <= 10 * accelerationDist heur = 0 -- Try once without nesting
  | otherwise = (visitCnt heur `div` (100 * accelerationDist heur)) + 1

---
-- UF Lemma Search
---
lemmaResolveTO :: Heur -> Maybe Int
lemmaResolveTO heur = Just $ visitCnt heur ^ (2 :: Int)

templatePattern :: Heur -> (Integer, [Integer])
templatePattern heur =
  let dis = accelerationDist heur * accelerationDist heur
   in (3 + toInteger (visitCnt heur `div` dis), genericReplicate (visitCnt heur `div` dis) 2)
