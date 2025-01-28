module Issy.Solver.Acceleration.Heuristics
  ( Heur
  , forVisits
  , loopArenaSize
  , loopArenaIncludeSucc
  , iterAMaxCPres
  , minEpsilon
  , invariantIterations
  , manhattenTermCount
  , boxOptSmtTO
  , lemmaResolveTO
  , templatePattern
  , nestingDepth
  ) where

import Data.List (genericReplicate)
import Data.Ratio ((%))
import qualified Data.Set as Set

import Issy.Config (Config, accelerationLevel)
import Issy.Solver.GameInterface

data Heur = Heur
  { visitCnt :: Int
  , config :: Config
  , locCnt :: Int
  }

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
    1 -> 1 -- TODO got to more at some point
    _ -> 2 -- TODO got to locCnt at some point

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
boxOptSmtTO _ = Nothing

invariantIterations :: Heur -> Int
invariantIterations _ = 2

manhattenTermCount :: Heur -> Int
manhattenTermCount _ = 2

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

--TODO: Add bound by number of cells!
templatePattern :: Heur -> (Integer, [Integer])
templatePattern heur =
  let dis = accelerationDist heur * accelerationDist heur
   in (3 + toInteger (visitCnt heur `div` dis), genericReplicate (visitCnt heur `div` dis) 2)
