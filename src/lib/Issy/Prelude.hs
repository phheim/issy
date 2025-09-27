---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Prelude
-- Description : Re-export and basic functions used through the Issy project to clean up the
--               import in most modules
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Prelude
  ( -- Configuration
    Config
  , setName
  , debug
  , -- First-order logic parts
    Symbol
  , Sort
  , Term
  , Model
  , Function
  , -- Default game parts
    Loc
  , Variables
  , Objective
  , WinningCondition
  , -- Symbolic state parts
    SymSt
  , get
  , set
  , -- Logging, and string composing operations
    lg
  , lgd
  , lgv
  , strS
  , strM
  , strL
  , strP
  , strT
  , -- Default data structures (& some operations)
    Set
  , Map
  , Queue
  , PrioQueue
  , (!?)
  , (!)
  , -- Functions from the standard library
    -- Pure functions
    first
  , second
  , bimap
  , ($>)
  , (<&>)
  , nub
  , fromJust
  , fromMaybe
  , mapMaybe
  , (%)
  , denominator
  , numerator
  , swap
  , -- Monad operations
    (<=<)
  , (>=>)
  , filterM
  , foldM
  , unless
  , when
  , -- IO operations
    die
  ) where

import Issy.Config (Config, debug, setName)

import Issy.Logic.FOL (Function, Model, Sort, Symbol, Term)

import Issy.Games.Locations (Loc)
import Issy.Games.Objectives (Objective, WinningCondition)
import Issy.Games.SymbolicState (SymSt, get, set)
import Issy.Games.Variables (Variables)

import Issy.Utils.Logging (lg, lgd, lgv, strL, strM, strP, strS, strT)

import Data.Map.Strict (Map, (!), (!?))
import Data.Set (Set)
import Issy.Utils.PrioQueue (PrioQueue)
import Issy.Utils.Queue (Queue)

import Data.Bifunctor (bimap, first, second)
import Data.Functor (($>), (<&>))
import Data.List (nub)
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Data.Ratio ((%), denominator, numerator)
import Data.Tuple (swap)

import Control.Monad ((<=<), (>=>), filterM, foldM, unless, when)

import System.Exit (die)
