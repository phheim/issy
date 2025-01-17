module Issy.Statistics
  ( Stats
  , printStats
  , emptyStats
  , accel
  , accelSucc
  ) where

import Issy.Config (Config, setName, statToStdout)
import Issy.Utils.Logging

data Stats = Stats
  { accelAttempt :: Int
  , accelSuccess :: Int
  }

emptyStats :: Stats
emptyStats = Stats {accelAttempt = 0, accelSuccess = 0}

accel :: Stats -> Stats
accel stats = stats {accelAttempt = 1 + accelAttempt stats}

accelSucc :: Stats -> Stats
accelSucc stats = stats {accelSuccess = 1 + accelSuccess stats}

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
  ]

prsh :: Show a => Stats -> String -> (Stats -> a) -> String
prsh stats name field = "- " ++ pad name ++ ": " ++ show (field stats)

pad :: String -> String
pad str = str ++ replicate (30 - length str) ' '
