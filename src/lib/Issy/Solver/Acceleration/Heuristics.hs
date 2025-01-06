module Issy.Solver.Acceleration.Heuristics where

import Data.List (genericReplicate)

visitingThreshold :: Int
visitingThreshold = 1

accelerationDist :: Int
accelerationDist = 4

limit2skolemNum :: Int -> Bool
limit2skolemNum k = k `mod` 8 == 0

limit2depth :: Int -> Int
limit2depth k
  | k <= 10 * accelerationDist = 0 -- Try once without nesting
  | otherwise = (k `div` (100 * accelerationDist)) + 1

limit2size :: Int -> Int
limit2size k = 1 --(k `div` accelerationDist) + 1

limit2to :: Int -> Int
limit2to k = k * k

limit2toextract :: Int -> Int
limit2toextract k = 4 * limit2to k

--TODO: Add bound by number of cells!
templateConfig :: Int -> (Integer, [Integer])
templateConfig limit =
  let dis = accelerationDist * accelerationDist
   in (3 + toInteger (limit `div` dis), genericReplicate (limit `div` dis) 2)
