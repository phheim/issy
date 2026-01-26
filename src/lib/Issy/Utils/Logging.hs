---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Utils.Logging
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Utils.Logging
  ( lg
  , lgd
  , lgv
  , strS
  , strM
  , strL
  , strP
  , strT
  ) where

import Control.Monad (when)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO (hPutStr, stderr)

import Issy.Config (Config, logLevel, logName)

inbetween :: a -> [a] -> [a]
inbetween sep =
  \case
    [] -> []
    [x] -> [x]
    x:xs -> x : sep : inbetween sep xs

strP :: (a -> String) -> (b -> String) -> (a, b) -> String
strP stra strb (a, b) = "(" ++ stra a ++ "," ++ strb b ++ ")"

strT :: (a -> String) -> (b -> String) -> (c -> String) -> (a, b, c) -> String
strT stra strb strc (a, b, c) = "(" ++ stra a ++ "," ++ strb b ++ "," ++ strc c ++ ")"

strL :: (a -> String) -> [a] -> String
strL str list = "[" ++ concat (inbetween ", " (str <$> list)) ++ "]"

strS :: Ord a => (a -> String) -> Set a -> String
strS str set = "{" ++ concat (inbetween ", " (str <$> Set.toList set)) ++ "}"

strM :: Ord k => (k -> String) -> (a -> String) -> Map k a -> String
strM strk stra mp =
  "{" ++ concat (inbetween ", " ((\(k, a) -> strk k ++ "->" ++ stra a) <$> Map.toList mp)) ++ "}"

lgOn :: Word -> Config -> [String] -> IO ()
lgOn min cfg msgs =
  when (logLevel cfg >= min) $ do
    let msgLines = filter (not . null) $ lines $ concatMap (++ " ") msgs ++ "\n"
    hPutStr stderr $ unlines $ map ((logName cfg ++ " ") ++) msgLines

lg :: Config -> [String] -> IO ()
lg = lgOn 1

lgd :: Config -> [String] -> IO ()
lgd = lgOn 2

lgv :: Config -> [String] -> IO ()
lgv = lgOn 3
---------------------------------------------------------------------------------------------------
