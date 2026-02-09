---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Utils.Queue
-- Description : Simple Queue with amortized runtime
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a simple queue with amortized runtime.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Utils.Queue
  ( Queue
  , null
  , empty
  , fromList
  , pop
  , push
  , pushs
  ) where

---------------------------------------------------------------------------------------------------
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as LNE
import Prelude hiding (null)

---------------------------------------------------------------------------------------------------
-- | A simple FIFO queue over arbitrary elements. In used a input stack to get an
-- amortized running time that is better than one would have by using a list.
newtype Queue a =
  Queue ([a], [a])
  deriving (Eq, Ord, Show)

instance Functor Queue where
  fmap f (Queue (outS, insS)) = Queue (fmap f outS, fmap f insS)

-- | Indicate if a queue is empty.
null :: Queue a -> Bool
null =
  \case
    Queue ([], []) -> True
    _ -> False

-- | The empty queue.
empty :: Queue a
empty = Queue ([], [])

-- | Create a queue from a list. The elements are popped in the order
-- in which they appear in the list.
fromList :: [a] -> Queue a
fromList xs = Queue (xs, [])

-- | Append an element to the queue. The runtime is O(1).
push :: a -> Queue a -> Queue a
push a =
  \case
    Queue ([], []) -> Queue ([a], [])
    Queue (outS, inpS) -> Queue (outS, a : inpS)

-- | Append elements of list to a queue in the order of the list.
-- The runtime is O(|xs|) where xs is the input list.
pushs :: [a] -> Queue a -> Queue a
pushs = flip $ foldl (flip push)

-- | Return the first element and the reduced queue if the queue is
-- not empty, otherwise it returns 'Nothing'. While in the worst case the runtime
-- is O(n) where n is the number of elements in the Queue, the average runtime is
-- better than that.
pop :: Queue a -> Maybe (a, Queue a)
pop =
  \case
    Queue ([], []) -> Nothing
    Queue (a:outR, inpS) -> Just (a, Queue (outR, inpS))
    Queue ([], a:inpS) ->
      let outS = LNE.reverse (a :| inpS)
       in Just (LNE.head outS, Queue (LNE.tail outS, []))
---------------------------------------------------------------------------------------------------
