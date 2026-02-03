---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Utils.Extra
-- Description : Common extra functions that are useful but would require more dependencies
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements common extra functions (e.g. for monads) that are however
-- not part of the base standard library and would therefore increase the dependencies. It also
-- has a few useful other generic extra functions.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Utils.Extra
  ( -- Maybes, Either, and Monads
    justOn
  , ifM
  , ifMC
  , ifMD
  , ifQuery
  , allM
  , orM
  , andM
  , rightToMaybe
  , firstJustsM
  , -- String related operations
    firstLine
  , paraInbetween
  , inbetween
  , enclose
  , -- Running external processes
    runTO
  , noTimeout
  , -- Set, Map, and Graph operations
    predecessorRelation
  , reachables
  , intmapSet
  , invertMap
  , mapFromSet
  , mapFromSetWith
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Process (readProcessWithExitCode)
import qualified System.Timeout as Sys (timeout)

import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- Maybe, Either, Monads
---------------------------------------------------------------------------------------------------
-- | 'Just' of the given element if the condition is 'True'
justOn :: Bool -> a -> Maybe a
justOn p
  | p = Just
  | otherwise = const Nothing

-- | Turns a 'Right' value to 'Just', and 'Left' to 'Nothing' discarding the value
rightToMaybe :: Either a b -> Maybe b
rightToMaybe =
  \case
    Right b -> Just b
    Left _ -> Nothing

-- | Evaluates the boolean condition and base on the result returns the first (if true) or
-- second value (if false)
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do
  b <- b
  if b
    then t
    else f

-- | Like 'ifM' but the "then-branch" is a pure value
ifMC :: Monad m => m Bool -> a -> m a -> m a
ifMC b t = ifM b $ pure t

-- | Like 'ifM' but the "else-branch" is a pure value
ifMD :: Monad m => m Bool -> m a -> a -> m a
ifMD b t = ifM b t . pure

-- | Like 'ifM' but the condition returns an additional value that is returned and
-- both branches are pure.
ifQuery :: Monad m => m (Bool, a) -> b -> b -> m (b, a)
ifQuery c t f = do
  (res, a) <- c
  if res
    then pure (t, a)
    else pure (f, a)

-- | Check if the given predicate holds on all elements. Stops early is 'False'
-- is encountered and evaluates in the order of 'foldl'
allM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
allM pred = foldl (\acc elem -> ifM acc (pred elem) (pure False)) (pure True)

-- | Monadic version of 'or'. Evaluates the second part only if necessary.
orM :: Monad m => m Bool -> m Bool -> m Bool
orM m1 = ifM m1 (pure True)

-- | Monadic version of 'and'. Evaluates the second part only if necessary.
andM :: Monad m => m Bool -> m Bool -> m Bool
andM m1 m2 = ifM m1 m2 (pure False)

-- | Moandic version of firstJusts
firstJustsM :: Monad m => [m (Maybe a)] -> m (Maybe a)
firstJustsM [] = pure Nothing
firstJustsM (m:mr) = do
  r <- m
  case r of
    Just r -> pure (Just r)
    Nothing -> firstJustsM mr

---------------------------------------------------------------------------------------------------
-- String related
---------------------------------------------------------------------------------------------------
-- | The first line of a string. Returns the empty string if the input string is empty.
firstLine :: String -> String
firstLine str =
  case lines str of
    [] -> []
    s:_ -> s

-- | Concatenates a list of 'String's with adding a separator between each of them. For example,
-- 'inbetween "," ["a", "b", "c"] == "a,b,c"'
inbetween :: String -> [String] -> String
inbetween sep =
  \case
    [] -> []
    [s] -> s
    s:sr -> s ++ sep ++ inbetween sep sr

-- | Encloses a string into some kind of brackets specified by the 'Char'. Currently
-- '()[]{}' are supported for proper enclosure. If the 'Char' is not in this list,
-- then it will be appended and prepended to the String.
enclose :: Char -> String -> String
enclose c str =
  case c of
    '(' -> "(" ++ str ++ ")"
    ')' -> "(" ++ str ++ ")"
    '[' -> "[" ++ str ++ "]"
    ']' -> "[" ++ str ++ "]"
    '{' -> "{" ++ str ++ "}"
    '}' -> "{" ++ str ++ "}"
    _ -> c : str ++ [c]

-- | Works like 'inbetween' and encloses the result in parenthesis.
paraInbetween :: String -> [String] -> String
paraInbetween sep elems = enclose '(' (inbetween sep elems)

---------------------------------------------------------------------------------------------------
-- Running things
---------------------------------------------------------------------------------------------------
-- | Given an (optional) timeout in seconds, runs a command with a list of command line
-- arguments, and input on stdin, discarding the error code and stderr. If a timeout occurred
-- 'runTO' will return 'Nothing', otherwise 'Just' with the content of stdout.
runTO :: Maybe Int -> String -> [String] -> String -> IO (Maybe String)
runTO to cmd args input =
  case to of
    Nothing -> do
      (_, res, _) <- readProcessWithExitCode cmd args $! input
      return (Just res)
    Just n
      | n < 0 -> do
        (_, res, _) <- readProcessWithExitCode cmd args $! input
        return (Just res)
      | otherwise -> do
        res <- Sys.timeout (n * 10 ^ (6 :: Int)) $ readProcessWithExitCode cmd args $! input
        case res of
          Just (_, res, _) -> return (Just res)
          Nothing -> pure Nothing

-- | Removes the timeout of 'runTO'. If a timeout occured this will be an error.
noTimeout :: IO (Maybe a) -> IO a
noTimeout comp = do
  res <- comp
  case res of
    Just res -> pure res
    Nothing -> error "assumed computation could not timeout!"

---------------------------------------------------------------------------------------------------
-- Sets, Maps, Graphs
---------------------------------------------------------------------------------------------------
-- | Maps the element of a set to an list with additional indices from [0 to size - 1] in the
-- ascending order of the elements of the set
intmapSet :: (Ord a, Ord b) => (Integer -> a -> b) -> Set a -> [b]
intmapSet mp = zipWith mp [0 ..] . Set.toList

-- | Inverts a 'Map' such that all elements of the input 'Map', map to all their keys in
-- the input map
invertMap :: (Ord a, Ord k) => Map k a -> Map a (Set k)
invertMap mp = Map.fromListWith Set.union $ map (\(k, a) -> (a, Set.singleton k)) $ Map.toList mp

-- | Shortcut for turning a set of tuples into a list and then into a map with 'Map.fromList'
mapFromSet :: (Ord a, Ord b) => Set (a, b) -> Map a b
mapFromSet = Map.fromList . Set.toList

-- | Shortcut for turning a set of tuples into a list and then into a map with 'Map.fromListWith'
mapFromSetWith :: (Ord k, Ord a) => (a -> a -> a) -> Set (k, a) -> Map k a
mapFromSetWith f = Map.fromListWith f . Set.toList

-- | Given a successors relation (in a directed graph) and a set of initial vertices
-- 'reachables' computes the set of reachable vertices
reachables :: Ord a => (a -> Set a) -> Set a -> Set a
reachables succ = go Set.empty . OL.fromSet
  where
    go explored ol =
      case OL.pop ol of
        Nothing -> explored
        Just (a, ol)
          | a `elem` explored -> go explored ol
          | otherwise -> go (Set.insert a explored) (OL.push (succ a `Set.difference` explored) ol)

-- | Given a successor relation (in a directed graph) and a set of vertices, compute the
-- predecessors relation for those vertices
predecessorRelation :: Ord a => (a -> Set a) -> Set a -> Map a (Set a)
predecessorRelation succ base =
  let init = Map.fromSet (const Set.empty) base
   in foldl
        (\m src ->
           foldl (\m targ -> Map.insertWith Set.union targ (Set.singleton src) m) m (succ src))
        init
        base
---------------------------------------------------------------------------------------------------
