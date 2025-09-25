---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Utils.PrioQueue
-- Description : Simple implementation of a priority queue.
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Utils.PrioQueue
  ( PrioQueue
  , empty
  , fromList
  , pop
  , push
  , pushs
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Issy.Utils.Queue (Queue)
import qualified Issy.Utils.Queue as Q

---------------------------------------------------------------------------------------------------
-- | 'PrioQueue p a' implements a priority queue where 'p' is the priority. The priority has to
-- be ordered. Elements with a higher priority are popped first. Elements of the same priority
-- are popped in a FIFO order.
newtype PrioQueue p a =
  PrioQueue (Map p (Queue a))
  deriving (Eq, Ord)

---------------------------------------------------------------------------------------------------
-- | 'empty' is the empty priority queue.
empty :: PrioQueue p a
empty = PrioQueue Map.empty

-- | 'fromList' create a priority queue with a single priority from a list
fromList :: p -> [a] -> PrioQueue p a
fromList p = PrioQueue . Map.singleton p . Q.fromList

-- | 'pop' returns the first element accoding to the queuing order, its priority, and the
-- reduced queue. If the queue is empty 'Nothing' is returned.
pop :: Ord p => PrioQueue p a -> Maybe (p, a, PrioQueue p a)
pop (PrioQueue q) =
  case Map.lookupMax q of
    Nothing -> Nothing
    Just (p, subq) ->
      case Q.pop subq of
        Nothing -> error "assert: this cannot happen"
        Just (a, subq)
          | Q.null subq -> Just (p, a, PrioQueue (Map.deleteMax q))
          | otherwise -> Just (p, a, PrioQueue (Map.insert p subq q))

-- | 'push' appends an element with a given priority to the queue.
push :: Ord p => p -> a -> PrioQueue p a -> PrioQueue p a
push p a (PrioQueue q) = PrioQueue $ Map.alter updQueue p q
  where
    updQueue Nothing = Just $ Q.push a Q.empty
    updQueue (Just q) = Just $ Q.push a q

-- | 'pushs' appends a list of element with a single priority to the queue.
pushs :: Ord p => p -> [a] -> PrioQueue p a -> PrioQueue p a
pushs p xs q = foldl (flip (push p)) q xs
---------------------------------------------------------------------------------------------------
