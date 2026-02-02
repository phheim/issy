---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Statistics
-- Description : Data structure for collecting statistics
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a simple yet generic way to collect statistics over a run of Issy.
-- Statistics should be restricted to accumulated data and should not influence the behavior
-- within the run. To collect statistics to a certain aspect (e.g. number of accelerations) you
-- need to register once a respective 'String' key in the statistics. Then with this key
-- you can add some data to this aspect (e.g. report another acceleration attempt). When
-- printing, for each key the resulting value is reported (e.g. total number of accelerations).
-- At the moment counting and average statistics-types are implemented.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Statistics
  ( -- Generic parts
    Stats
  , printStats
  , emptyStats
  , -- Incremental
    registerCnt
  , statCnt
  , -- Average
    registerAvg
  , statAvg
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Issy.Config (Config, logLevel, setName, statToStdout)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- Generic Statistics
---------------------------------------------------------------------------------------------------
-- | This data structure contains the collected statistical data
data Stats
  = NoStats
  -- ^ this is a placeholder if no statistics are to be collected
  | Stats (Map String StatType)
  -- ^ maps keys (i.e. data points) to

-- | Empty statistics at the beginning of a run
emptyStats :: Config -> Stats
emptyStats config
  | logLevel config >= 1 || statToStdout config = Stats Map.empty
  | otherwise = NoStats

-- | Generic registration of a type of data given the initial value
register :: StatType -> String -> Stats -> Stats
register _ _ NoStats = NoStats
register initStat key (Stats stats)
  | key `Map.member` stats = error $ "assert: " ++ key ++ " has already been registered"
  | otherwise = Stats $ Map.insert key initStat stats

-- | Generic modification of a type of data. Assumes that the key already exist
moddify :: String -> (StatType -> StatType) -> Stats -> Stats
moddify _ _ NoStats = NoStats
moddify key moddifier (Stats stats)
  | key `Map.member` stats = Stats $ Map.adjust moddifier key stats
  | otherwise = error $ "assert: " ++ key ++ " has not been registered yet"

-- | Prints the statistics to on the normal log level to stderr or to stdout if configured
-- explicitly so
printStats :: Config -> Stats -> IO ()
printStats _ NoStats = pure ()
printStats config (Stats stats) =
  let statLines =
        unlines
          $ ("Statistics:" :)
          $ flip map (Map.toList stats)
          $ \(key, val) -> " - " ++ pad key ++ ": " ++ statTypeToString val
   in if statToStdout config
        then putStrLn statLines
        else lg (setName "Stats" config) [statLines]
  where
    pad str = str ++ replicate (30 - length str) ' '

---------------------------------------------------------------------------------------------------
-- Types of Statistics
---------------------------------------------------------------------------------------------------
-- | Different type of statistical data
data StatType
  = CntStat Integer
  -- ^ statistics over values that are just incremented
  | AvgStat Integer Rational
  -- ^ statistics over values that should be averaged

-- | Registers a counting-statistics key.
-- 'undefined' if the key already exists
registerCnt :: String -> Stats -> Stats
registerCnt = register $ CntStat 0

-- | Registers a average-statistics key.
-- 'undefined' if the key already exists
registerAvg :: String -> Stats -> Stats
registerAvg = register $ AvgStat 0 0

-- | Increments the value of a counting-statistics key.
-- 'undefined' if the key does not yet exists
statCnt :: String -> Stats -> Stats
statCnt key =
  moddify key $ \case
    CntStat n -> CntStat (n + 1)
    _ -> error $ "assert: try to increment " ++ key ++ " with different registration"

-- | Adds a data-point to an average-statistics key.
-- 'undefined' if the key does not yet exists
statAvg :: String -> Rational -> Stats -> Stats
statAvg key point =
  moddify key $ \case
    AvgStat n v -> AvgStat (n + 1) (v + point)
    _ -> error $ "assert: try to average " ++ key ++ " with different registration"

statTypeToString :: StatType -> String
statTypeToString =
  \case
    CntStat n -> show n
    AvgStat n val
      | n == 0 -> "NaN"
      | otherwise -> show $ val / toRational n
---------------------------------------------------------------------------------------------------
