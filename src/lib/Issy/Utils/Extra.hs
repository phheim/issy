{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Utils.Extra
  ( justOn
  , ifM
  , ifMC
  , ifMD
  , ifQuery
  , allM
  , orM
  , andM
  , rightToMaybe
  , predecessorRelation
  , reachables
  , firstLine
  , intmapSet
  , invertMap
  , mapFromSet
  , mapFromSetWith
  , runTO
  , noTimeout
  , paraInbetween
  , inbetween
  , enclose
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Process (readProcessWithExitCode)
import qualified System.Timeout as Sys (timeout)

import qualified Issy.Utils.OpenList as OL

justOn :: Bool -> a -> Maybe a
justOn p
  | p = Just
  | otherwise = const Nothing

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do
  b <- b
  if b
    then t
    else f

ifMC :: Monad m => m Bool -> a -> m a -> m a
ifMC b t = ifM b $ pure t

ifMD :: Monad m => m Bool -> m a -> a -> m a
ifMD b t = ifM b t . pure

ifQuery :: Monad m => m (Bool, a) -> b -> b -> m (b, a)
ifQuery c t f = do
  (res, a) <- c
  if res
    then pure (t, a)
    else pure (f, a)

allM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
allM pred = foldl (\acc elem -> ifM acc (pred elem) (pure False)) (pure True)

orM :: Monad m => m Bool -> m Bool -> m Bool
orM m1 = ifM m1 (pure True)

andM :: Monad m => m Bool -> m Bool -> m Bool
andM m1 m2 = ifM m1 m2 (pure False)

rightToMaybe :: Either a b -> Maybe b
rightToMaybe =
  \case
    Right b -> Just b
    Left _ -> Nothing

predecessorRelation :: Ord a => (a -> Set a) -> Set a -> Map a (Set a)
predecessorRelation succ base =
  let init = Map.fromSet (const Set.empty) base
   in foldl
        (\m src ->
           foldl (\m targ -> Map.insertWith Set.union targ (Set.singleton src) m) m (succ src))
        init
        base

invertMap :: (Ord a, Ord k) => Map k a -> Map a (Set k)
invertMap mp = Map.fromListWith Set.union $ map (\(k, a) -> (a, Set.singleton k)) $ Map.toList mp

reachables :: Ord a => (a -> Set a) -> Set a -> Set a
reachables succ = go Set.empty . OL.fromSet
  where
    go explored ol =
      case OL.pop ol of
        Nothing -> explored
        Just (a, ol)
          | a `elem` explored -> go explored ol
          | otherwise -> go (Set.insert a explored) (OL.push (succ a `Set.difference` explored) ol)

firstLine :: String -> String
firstLine str =
  case lines str of
    [] -> []
    s:_ -> s

intmapSet :: (Ord a, Ord b) => (Integer -> a -> b) -> Set a -> [b]
intmapSet mp = zipWith mp [0 ..] . Set.toList

mapFromSet :: (Ord a, Ord b) => Set (a, b) -> Map a b
mapFromSet = Map.fromList . Set.toList

mapFromSetWith :: (Ord k, Ord a) => (a -> a -> a) -> Set (k, a) -> Map k a
mapFromSetWith f = Map.fromListWith f . Set.toList

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

noTimeout :: IO (Maybe a) -> IO a
noTimeout comp = do
  res <- comp
  case res of
    Just res -> pure res
    Nothing -> error "assumed computation could not timeout!"

-- TODO: check usage!
paraInbetween :: String -> [String] -> String
paraInbetween sep elems = enclose '(' (inbetween sep elems)

-- TODO: check usage!
inbetween :: String -> [String] -> String
inbetween sep =
  \case
    [] -> []
    [s] -> s
    s:sr -> s ++ sep ++ inbetween sep sr

-- TODO: check usage!
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
