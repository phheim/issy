---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Utils.Queue
-- Description : Simple Queue with armortized running time
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

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
import Prelude hiding (null)

---------------------------------------------------------------------------------------------------
-- | 'Queue' is a simple FIFO queue over arbitrary elements. In used a input stack to get an 
-- amortized running time that is better than one would have by using a list.
newtype Queue a =
  Queue ([a], [a])
  deriving (Eq, Ord)

instance Functor Queue where
  fmap f (Queue (outS, insS)) = Queue (fmap f outS, fmap f insS)

-- | 'null' indicates if a 'Queue' is empty. 
null :: Queue a -> Bool
null =
  \case
    Queue ([], []) -> True
    _ -> False

-- | 'empty' is the empty 'Queue'. 
empty :: Queue a
empty = Queue ([], [])

-- | 'fromList' creates 'Queue' from a list. The elements are popped in the order
-- in which they appear in the list.
fromList :: [a] -> Queue a
fromList xs = Queue (xs, [])

-- | 'push' appends an element to the 'Queue'. The runtime is O(1).
push :: a -> Queue a -> Queue a
push a =
  \case
    Queue ([], []) -> Queue ([a], [])
    Queue (outS, inpS) -> Queue (outS, a : inpS)

-- | 'pushs' appends elements of list to a 'Queue' in the order of the list. 
-- The runtime is O(|xs|) where xs is the input list.
pushs :: [a] -> Queue a -> Queue a
pushs = flip $ foldl (flip push)

-- | 'pop' returns the first element and the reduced queue if the queue is
-- not empty, otherwise it returns 'Nothing'. While in the worst case the runtime
-- is O(n) where n is the number of elements in the Queue, the average runtime is
-- better than that. 
pop :: Queue a -> Maybe (a, Queue a)
pop =
  \case
    Queue ([], []) -> Nothing
    Queue (a:outR, inpS) -> Just (a, Queue (outR, inpS))
    Queue ([], inpS) ->
      let outS = reverse inpS
       in Just (head outS, Queue (tail outS, []))
---------------------------------------------------------------------------------------------------
