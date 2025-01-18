module Issy.Utils.Extra where

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

ifMP :: Monad m => m Bool -> a -> a -> m a
ifMP b t f = ifM b (pure t) (pure f)

ifMC :: Monad m => m Bool -> a -> m a -> m a
ifMC b t = ifM b $ pure t

ifQuery :: Monad m => m (Bool, a) -> b -> b -> m (b, a)
ifQuery c t f = do
  (res, a) <- c
  if res
    then pure (t, a)
    else pure (f, a)

allM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
allM pred = foldl (\acc elem -> ifM acc (pred elem) (pure False)) (pure True)

predecessorRelation :: Ord a => (a -> Set a) -> Set a -> Map a (Set a)
predecessorRelation succ base =
  let init = Map.fromSet (const Set.empty) base
   in foldl
        (\m src ->
           foldl (\m targ -> Map.insertWith Set.union targ (Set.singleton src) m) m (succ src))
        init
        base

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
      (_, res, _) <- readProcessWithExitCode cmd args input
      return (Just res)
    Just n
      | n < 0 -> do
        (_, res, _) <- readProcessWithExitCode cmd args input
        return (Just res)
      | otherwise -> do
        res <- Sys.timeout (n * 10 ^ (6 :: Int)) $ readProcessWithExitCode cmd args input
        case res of
          Just (_, res, _) -> return (Just res)
          Nothing -> pure Nothing

noTimeout :: IO (Maybe a) -> IO a
noTimeout comp = do
  res <- comp
  case res of
    Just res -> pure res
    Nothing -> error "assumed computation could not timeout!"
