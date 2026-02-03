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
import Control.Monad (unless)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Compiler.Base

---------------------------------------------------------------------------------------------------
-- | checks if an AST is a valid and compilable
check :: AstSpec -> PRes AstSpec
check defs = do
  _ <- checkVars defs
  checkGames defs
  Right defs

---------------------------------------------------------------------------------------------------
-- Variables
---------------------------------------------------------------------------------------------------
checkVars :: [AstDef] -> PRes (Set String, Set String)
checkVars = go Set.empty Set.empty
  where
    go ins outs [] = Right (ins, outs)
    go ins outs (AstVar p io _ name:dr)
      | (name `elem` ins) || (name `elem` outs) =
        perr p $ "variable " ++ name ++ " already declared"
      | otherwise =
        case io of
          AInput -> go (Set.insert name ins) outs dr
          AState -> go ins (Set.insert name outs) dr
    go ins outs (_:dr) = go ins outs dr

---------------------------------------------------------------------------------------------------
-- Games
---------------------------------------------------------------------------------------------------
checkGames :: [AstDef] -> PRes ()
checkGames = go False
  where
    go _ [] = Right ()
    go nonSafe (AstGame p wc initLoc stmts:dr) = do
      locs <- checkLocs stmts
      unless (initLoc `elem` locs) $ perr p $ "initial location not defined " ++ initLoc
      checkTrans locs stmts
      nonSafe <-
        case wc of
          ASafety -> Right nonSafe
          _
            | nonSafe -> perr p "only one non-safety game is allowed"
            | otherwise -> Right True
      go nonSafe dr
    go nonSafe (_:dr) = go nonSafe dr

checkLocs :: [AstGameStm] -> PRes (Set String)
checkLocs = go Set.empty
  where
    go names [] = Right names
    go names (ALoc p name _ _:sr)
      | name `elem` names = perr p $ "found duplicate location " ++ name
      | otherwise = go (Set.insert name names) sr
    go names (_:sr) = go names sr

checkTrans :: Set String -> [AstGameStm] -> PRes ()
checkTrans locs = go Set.empty
  where
    go _ [] = Right ()
    go pairs (ATrans p l1 l2 _:sr)
      | l1 `notElem` locs = perr p $ "found undefined location " ++ l1
      | l2 `notElem` locs = perr p $ "found undefined location " ++ l2
      | (l1, l2) `elem` pairs =
        perr p $ "transition from " ++ l1 ++ " to " ++ l2 ++ " already defined"
      | otherwise = go (Set.insert (l1, l2) pairs) sr
    go pairs (_:sr) = go pairs sr
---------------------------------------------------------------------------------------------------
