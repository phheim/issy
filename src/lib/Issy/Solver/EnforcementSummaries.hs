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
trySummary ::
     Config -> Attr -> Player -> Arena -> Loc -> EnfSt -> SymSt -> IO (EnfSt, Maybe (Term, SyBo))
trySummary conf attr player arena loc enfst reach = do
  conf <- pure $ setName "Summaries" conf
  lg
    conf
    ["Summaries failed/success", show (length (failed enfst)), show (length (summaries enfst))]
  lg conf ["Try to apply summary in", locName arena loc, "on", strSt arena reach]
  case find (matchKey player arena loc . fst) (summaries enfst) of
    Just (key, content) -> do
      lg conf ["Use existing summary"] -- TODO: details
      res <- applyIn conf (vars (sumArena key)) content reach
      lg conf ["Applied summary:", SMTLib.toString (fst res)]
      pure (enfst, Just res)
    Nothing ->
      case find (matchKey player arena loc) (failed enfst) of
        Just _ -> do
          lg conf ["Existence of valid summary already ruled out"]
          pure (enfst, Nothing)
        Nothing -> do
          lg conf ["Compute summary"]
          (key, content) <- computeSum conf attr player arena loc reach
          case content of
            Nothing -> do
              lg conf ["Summary computation failed"]
              pure (enfst {failed = failed enfst ++ [key]}, Nothing)
            Just content -> do
              lg conf ["Summary computation succeeded"] -- TODO: details
              enfst <- pure $ enfst {summaries = summaries enfst ++ [(key, content)]}
              res <- applyIn conf (vars (sumArena key)) content reach
              lg conf ["Applied summary:", SMTLib.toString (fst res)]
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
      skolemConstr = error "TODO"
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
  let oldSubLocs = Set.insert loc $ succs oldArena loc --TODO: make nicer!
  (arena, oldToNew) <- pure $ inducedSubArena arena $ Set.singleton loc
  let oldToNewM l =
        if l `elem` oldSubLocs
          then Just (oldToNew l)
          else Nothing
  reach <- pure $ extendSt reach oldToNewM arena
  loc <- pure $ oldToNew loc
  template <- generalize conf arena reach loc
  let metas =
        Map.toList
          $ Map.filterWithKey (\var _ -> var `notElem` stateVars arena)
          $ FOL.bindings
          $ FOL.orf
          $ map snd
          $ SymSt.toList template
  arena <- pure $ addConstants metas arena
    -- TODO: add underapproximation restriction!!!
  (attrRes, templProg) <- attr conf player arena template
    -- This program somehow needs the backmapping as wall as the summary content, no?
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
      lg conf ["Computed summary:"]
      lg conf [" - meta: ", strL fst metas]
      lg conf [" - enf:  ", SMTLib.toString enforce]
      lg conf [" - temp: ", strSt arena template]
      pure (key, Just content)

generalize :: Config -> Arena -> SymSt -> Loc -> IO SymSt
generalize conf arena reach loc = do
  lgd conf ["Generalize in", locName arena loc, "from", strSt arena reach]
  indeps <- independentProgVars conf arena -- TODO: use better heuristic with other variables!
  lgd conf ["Indepedents", strS id indeps]
  let eqVars = Set.toList indeps
  let subLocs = Set.delete loc $ succs arena loc -- TODO: remove loc except if singelton loc?
  foldM
    (\st subloc -> set st subloc <$> projectFor eqVars (reach `get` subloc) subloc)
    (emptySt arena)
    subLocs
  where
    projectFor eqVars term subloc = do
      let prefix = FOL.uniquePrefix ("meta_" ++ locName arena subloc) $ usedSymbols arena
      let metas = map (prefix ++) eqVars
      let eqConstr =
            FOL.andfL eqVars $ \v ->
              FOL.var v (sortOf arena v) `FOL.equal` FOL.var (prefix ++ v) (sortOf arena v)
      psi <- SMT.simplify conf $ FOL.exists metas $ FOL.forAll eqVars $ eqConstr `FOL.impl` term
      let next = FOL.andf [eqConstr, psi]
      check <- SMT.sat conf $ Vars.forallX (vars arena) $ next `FOL.impl` term
      unless check $ error "assert: this should always be true"
      pure next
---------------------------------------------------------------------------------------------------
