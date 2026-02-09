---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Utils.Logging
-- Description : Logging of runtime information
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module provides Issy's logging functionality as well as pretty printing functions
-- to ease logging. The pretty printing functions are supposed to be used recursively.
-- As of now, Issy has four log levels quiet (0), normal (1), detailed (2), and  verbose (3)
-- (increasing level of detail). The log level as well as the logging prefix is determined
-- by 'Config'.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Utils.Logging
  ( -- Logging functions
    lg
  , lgd
  , lgv
  , -- Pretty printing helpers
    strS
  , strM
  , strL
  , strP
  , strT
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad (when)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO (hPutStr, stderr)

import Issy.Config (Config, logLevel, logName)
import Issy.Utils.Extra (enclose, inbetween)

---------------------------------------------------------------------------------------------------
-- Logging
---------------------------------------------------------------------------------------------------
-- | If the log level is at least normal (i.e. 'logLevel' is greater zero), 'lg' write the given
-- list of 'String's line by line to stderr prefixed by 'logName'.
lg :: Config -> [String] -> IO ()
lg = lgOn 1

-- | Works as 'lg' but only if the log level is at least verbose
lgd :: Config -> [String] -> IO ()
lgd = lgOn 2

-- | Works 'lg' but only if the log level is at least detailed
lgv :: Config -> [String] -> IO ()
lgv = lgOn 3

lgOn :: Word -> Config -> [String] -> IO ()
lgOn min cfg msgs =
  when (logLevel cfg >= min) $ do
    let msgLines = filter (not . null) $ lines $ concatMap (++ " ") msgs ++ "\n"
    hPutStr stderr $ unlines $ map ((logName cfg ++ " ") ++) msgLines

---------------------------------------------------------------------------------------------------
-- Pretty Printing
---------------------------------------------------------------------------------------------------
-- | Pretty prints a tuple
strP :: (a -> String) -> (b -> String) -> (a, b) -> String
strP stra strb (a, b) = enclose '(' $ stra a ++ "," ++ strb b

-- | Pretty prints a triple
strT :: (a -> String) -> (b -> String) -> (c -> String) -> (a, b, c) -> String
strT stra strb strc (a, b, c) = enclose '(' $ stra a ++ "," ++ strb b ++ "," ++ strc c

-- | Pretty prints a list
strL :: (a -> String) -> [a] -> String
strL str list = enclose '[' $ inbetween ", " (str <$> list)

-- | Pretty prints a 'Set'
strS :: Ord a => (a -> String) -> Set a -> String
strS str set = enclose '{' $ inbetween ", " (str <$> Set.toList set)

-- | Pretty prints a 'Map'
strM :: Ord k => (k -> String) -> (a -> String) -> Map k a -> String
strM strk stra mp =
  enclose '{' $ inbetween ", " ((\(k, a) -> strk k ++ "->" ++ stra a) <$> Map.toList mp)
---------------------------------------------------------------------------------------------------
