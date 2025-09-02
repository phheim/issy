---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Prelude
-- Description : Re-export and basic functions used through the Issy project to clean up the
--               import in most modules
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Prelude
  ( Config
  , setName
  , Symbol
  , Sort
  , Term
  , Model
  , Function
  , Loc
  , Variables
  , Objective
  , WinningCondition
  , SymSt
  , get
  , set
  , Set
  , Map
  , (!?)
  , (!)
  , first
  , second
  , bimap
  , ($>)
  , (<&>)
  , fromMaybe
  , mapMaybe
  , (%)
  , denominator
  , numerator
  , (<=<)
  , filterM
  , foldM
  , unless
  ) where

import Issy.Config (Config, setName)

import Issy.Logic.FOL (Function, Model, Sort, Symbol, Term)

import Issy.Base.Locations (Loc)
import Issy.Base.Objectives (Objective, WinningCondition)
import Issy.Base.SymbolicState (SymSt, get, set)
import Issy.Base.Variables (Variables)

import Data.Map.Strict (Map, (!), (!?))
import Data.Set (Set)

import Data.Bifunctor (bimap, first, second)
import Data.Functor (($>), (<&>))
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Ratio ((%), denominator, numerator)

import Control.Monad ((<=<), filterM, foldM, unless)
