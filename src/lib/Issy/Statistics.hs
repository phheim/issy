---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Statistics
-- Description : Data structure to accumulate statistics over the run of Issy
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
-- This module contains a simple data structure that can be used to accumulate statistics.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Statistics
  ( Stats
  , printStats
  , emptyStats
  , accel
  , accelSucc
  , summaryApp
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Config (Config, setName, statToStdout)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- | 'Stats' contains the accumulated statistical data.
data Stats = Stats
  { accelAttempt :: Int
  , accelSuccess :: Int
  , summaryApplications :: Int
  }

-- | The initial 'Stats' at the beggining of a run of Issy.
emptyStats :: Stats
emptyStats = Stats {accelAttempt = 0, accelSuccess = 0, summaryApplications = 0}

---------------------------------------------------------------------------------------------------
accel :: Stats -> Stats
accel stats = stats {accelAttempt = 1 + accelAttempt stats}

accelSucc :: Stats -> Stats
accelSucc stats = stats {accelSuccess = 1 + accelSuccess stats}

summaryApp :: Stats -> Stats
summaryApp stats = stats {summaryApplications = 1 + summaryApplications stats}

---------------------------------------------------------------------------------------------------
-- | Prints 'Stats' either to STDIN or STDOUT depening on the 'Config'
printStats :: Config -> Stats -> IO ()
printStats conf stats
  | statToStdout conf = putStrLn $ unlines $ statString stats
  | otherwise = do
    conf <- pure $ setName "Stats" conf
    lg conf [unlines (statString stats)]

statString :: Stats -> [String]
statString stats =
  [ "Statistics:"
  , prsh stats "Acceleration Attempts" accelAttempt
  , prsh stats "Acceleration Success" accelSuccess
  , prsh stats "Summary Applications" summaryApplications
  ]

prsh :: Show a => Stats -> String -> (Stats -> a) -> String
prsh stats name field = "- " ++ pad name ++ ": " ++ show (field stats)

pad :: String -> String
pad str = str ++ replicate (30 - length str) ' '
---------------------------------------------------------------------------------------------------
