---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.EnforcementSummaries
-- Description : Implementation of Enforcement Summaries
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.EnforcementSummaries
  ( EnfSt
  , empty
  , trySummary
  ) where

---------------------------------------------------------------------------------------------------
import Data.List (find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra (allM)

---------------------------------------------------------------------------------------------------
-- Definitions
---------------------------------------------------------------------------------------------------
-- | 'EnfSt' holds a global state of the enforcement summary computation. It contains successful
-- and failed attempts for computing enforcement summaries.
data EnfSt = EnfSt
  { summaries :: [(SummaryKey, SummaryContent)]
  , failed :: [SummaryKey]
  }

-- | 'empty' is the initial 'EnfSt' state 
empty :: EnfSt
empty = EnfSt {summaries = [], failed = []}

-- | 'SummaryKey' describes the sub-arena and player for a (potential) enforcement summary
data SummaryKey = SummaryKey
  { sumPlayer :: Player
  , sumArena :: Arena
  , sumLoc :: Loc
  }

-- | 'SummaryContent' is the actual summary. To be sound a 'SummaryContent' need a matching 
-- 'SummaryKey'
data SummaryContent = SummaryContent
  { metaVars :: [(Symbol, Sort)]
  , enforcable :: Term
    -- ^ 'enforcable' is the main formula part!
  , targets :: SymSt
  , sybo :: SyBo
    -- ^ 'sybo' is the book-kept strategy with meta variables
  }

-- This is needed to get Haskell to accept the cylic dependencies
-- and makes it also easier to control the attractor computation 
-- within the attractor module.
type Attr = Config -> Player -> Arena -> SymSt -> IO (SymSt, SyBo)

--------------------------------------------------------------------------------------------------- 
-- High Level Procedure
--------------------------------------------------------------------------------------------------- 
-- TODO: streamline logging
trySummary ::
     Config -> Attr -> Player -> Arena -> Loc -> EnfSt -> SymSt -> IO (EnfSt, Maybe (Term, SyBo))
trySummary conf attr player arena loc enfst reach = do
  conf <- pure $ setName "Summaries" conf
  lgd conf ["Currently", show (length (failed enfst)), "failed"]
  lgd conf ["Currently", show (length (summaries enfst)), "suceeded"]
  lg conf ["Try to apply summary in", locName arena loc, "on", strSt arena reach]
  case find (matchKey player arena loc . fst) (summaries enfst) of
    Just (key, content) -> do
      res <- applyIn conf (vars (sumArena key)) content reach
      lg conf ["Used existing summary and got", SMTLib.toString (fst res)]
      pure (enfst, Just res)
    Nothing ->
      case find (matchKey player arena loc) (failed enfst) of
        Just _ -> do
          lgd conf ["Existence of valid summary already ruled out"]
          pure (enfst, Nothing)
        Nothing -> do
          lg conf ["Compute summary"]
          (key, content) <- computeSum conf attr player arena loc reach
          case content of
            Nothing -> do
              lg conf ["Summary computation failed"]
              pure (enfst {failed = failed enfst ++ [key]}, Nothing)
            Just content -> do
              enfst <- pure $ enfst {summaries = summaries enfst ++ [(key, content)]}
              res <- applyIn conf (vars (sumArena key)) content reach
              lg conf ["Use newly computed summary:", SMTLib.toString (fst res)]
              pure (enfst, Just res)

matchKey :: Player -> Arena -> Loc -> SummaryKey -> Bool
matchKey player arena loc key =
  player == sumPlayer key && loc == sumLoc key && arena == sumArena key

---------------------------------------------------------------------------------------------------
-- Application
---------------------------------------------------------------------------------------------------
-- make applicability a DOCUMENTED precondition!!!
applyIn :: Config -> Variables -> SummaryContent -> SymSt -> IO (Term, SyBo)
applyIn conf vars summary reach =
  let condImpl =
        FOL.andfL (SymSt.toList (targets summary)) $ \(l, next) ->
          Vars.forallX vars $ FOL.impl next (get reach l)
     -- ^ condition that the current target 'reach' is part of the symbolic target
      constr = FOL.exists (map fst (metaVars summary)) $ FOL.andf [condImpl, enforcable summary]
     -- ^ overall summary
      skolemConstr = error "TODO IMPLEMENT"
      prog = Synt.summarySyBo (metaVars summary) (constr, skolemConstr) (sybo summary)
     -- ^ programm computation
   in do
        constr <- SMT.simplify conf constr
        pure (constr, prog)

---------------------------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------------------------- 
computeSum ::
     Config -> Attr -> Player -> Arena -> Loc -> SymSt -> IO (SummaryKey, Maybe SummaryContent)
computeSum conf attr player arena loc reach = do
  conf <- pure $ setName "SummaryGen" conf
  let key = SummaryKey {sumPlayer = player, sumArena = arena, sumLoc = loc}
  let oldArena = arena
  (arena, (oldToNew, oldSubLocs)) <- pure $ inducedSubArena arena $ Set.singleton loc
  let oldToNewM l =
        if l `elem` oldSubLocs
          then Just (oldToNew l)
          else Nothing
  reach <- pure $ extendSt reach oldToNewM arena
  loc <- pure $ oldToNew loc
  template <- generalize conf player arena reach loc
  let metas =
        Map.toList
          $ Map.filterWithKey (\var _ -> var `notElem` stateVars arena)
          $ FOL.bindings
          $ FOL.orf
          $ map snd
          $ SymSt.toList template
  arena <- pure $ addConstants metas arena
  conf <- pure $ setName "AttrSumGen" conf
  (attrRes, templProg) <- attr conf player arena template
  conf <- pure $ setName "SummaryGen" conf
  enforce <- SMT.simplify conf $ attrRes `get` loc
  sat <- SMT.sat conf enforce
  if not sat
    then pure (key, Nothing)
    else do
      let content =
            SummaryContent
              { metaVars = metas
              , enforcable = enforce
              , targets = backmapSt template oldToNewM oldArena
              , sybo = templProg
              }
      lg conf ["Summary computation succeeded with:"]
      lg conf [" - meta: ", strL fst metas]
      lg conf [" - enf:  ", SMTLib.toString enforce]
      lg conf [" - temp: ", strSt arena template]
      pure (key, Just content)

generalize :: Config -> Player -> Arena -> SymSt -> Loc -> IO SymSt
generalize conf player arena reach loc = do
  lgd conf ["Generalize in", locName arena loc, "from", strSt arena reach]
  eqVars <- Set.toList <$> selectVars conf player arena
  lgd conf ["Equality variables", strL id eqVars]
  let subLocs
        | succs arena loc == Set.singleton loc = Set.singleton loc
        | otherwise = Set.delete loc $ succs arena loc
  foldM
    (\st subloc -> set st subloc <$> projectFor eqVars (reach `get` subloc) subloc)
    (emptySt arena)
    subLocs
  where
    projectFor eqVars term subloc = do
      let prefix = FOL.uniquePrefix ("meta_" ++ locName arena subloc) $ usedSymbols arena
      let eqConstr =
            FOL.andfL eqVars $ \v ->
              FOL.var v (sortOf arena v) `FOL.equal` FOL.var (prefix ++ v) (sortOf arena v)
      psi <- SMT.simplify conf $ FOL.exists eqVars term
      let next = FOL.andf [eqConstr, psi]
      check <- SMT.sat conf $ Vars.forallX (vars arena) $ next `FOL.impl` term
      if check
        then pure next
        else pure FOL.false

selectVars :: Config -> Player -> Arena -> IO (Set Symbol)
selectVars conf player arena = do
  indeps <- independentProgVars conf arena
  control <-
    filterM (\var -> allM (isControlableIn var) (locationL arena))
      $ filter (`notElem` indeps)
      $ Vars.stateVarL
      $ vars arena
  pure $ Set.fromList control `Set.union` indeps
  where
    checkVar = FOL.uniquePrefix "meta_target_value" $ usedSymbols arena
    isControlableIn var loc =
      let sort = sortOf arena var
          st =
            SymSt.symSt (locations arena) $ \l ->
              if l `elem` succs arena loc
                then FOL.var var sort `FOL.equal` FOL.var checkVar sort
                else FOL.false
          res = cpre player arena st loc
       in SMT.valid conf $ FOL.forAll [checkVar] $ Vars.existsX (vars arena) res
---------------------------------------------------------------------------------------------------
