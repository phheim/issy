---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler.Checker
-- Description : Checker for the issy-format to llissy-format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module check whether the AST of a issy specification does conform to typing and
-- other well-form-rules. Note that for now this check is incomplete. Especially, more
-- semantic properties might only be caught later for now.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Compiler.Checker
  ( check
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Compiler.Base

---------------------------------------------------------------------------------------------------
-- | checks if an AST is a valid and compilable
check :: AstSpec -> PRes AstSpec
check = Right -- TODO IMPLEMENT
---------------------------------------------------------------------------------------------------
