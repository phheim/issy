---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.EnforcementSummaries
-- Description : Implementation of Enforcement Summaries
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Solver.EnforcementSummaries
  ( EnfSt
  , empty
  , trySummary
  ) where

---------------------------------------------------------------------------------------------------
import Data.List (find)
import qualified Data.Map.Strict as Map

import Issy.Base.SymbolicState (SymSt, get)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Base.Variables (Variables)
import Issy.Config (Config, setName)
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import Issy.Utils.Logging

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
-- TODO: type Attr = Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt, SyBo) lift SolSt
-- TODO: preliminary version
type Attr = Config -> Player -> Arena -> SymSt -> IO (SymSt, SyBo)

--------------------------------------------------------------------------------------------------- 
-- High Level Procedure
--------------------------------------------------------------------------------------------------- 
-- TODO: document, do not QELIM result, that is resposibility of caller
trySummary ::
     Config -> Attr -> Player -> Arena -> Loc -> EnfSt -> SymSt -> IO (EnfSt, Maybe (Term, SyBo))
trySummary conf attr player arena loc enfst reach = do
  conf <- pure $ setName "Summaries" conf
  lgd conf ["Try to apply summary"] -- TODO: details
  case find (matchKey player arena loc . fst) (summaries enfst) of
    Just (key, content) -> do
      lgd conf ["Apply summary"] -- TODO: details
      res <- applyIn conf (vars (sumArena key)) content reach
      lgd conf ["Summary"] -- TODO: details
      pure (enfst, Just res)
    Nothing ->
      case find (matchKey player arena loc) (failed enfst) of
        Just _ -> do
          lgd conf ["No valid summary exists"]
          pure (enfst, Nothing)
        Nothing -> do
          lg conf ["Compute summary"] -- TODO: details
          (key, content) <- computeSum conf attr player arena loc
          case content of
            Nothing -> do
              lg conf ["Summary computation failed"]
              pure (enfst {failed = failed enfst ++ [key]}, Nothing)
            Just content -> do
              lg conf ["Summary computation succeeded"] -- TODO: details
              enfst <- pure $ enfst {summaries = summaries enfst ++ [(key, content)]}
              lgd conf ["Apply summary"] -- TODO: details
              res <- applyIn conf (vars (sumArena key)) content reach
              lgd conf ["Summary"] -- TODO: details
              pure (enfst, Just res)

matchKey :: Player -> Arena -> Loc -> SummaryKey -> Bool
matchKey player arena loc key
  | player == sumPlayer key =
    case isSubarenaFrom (sumLoc key, sumArena key) (loc, arena) of
      Nothing -> False -- TODO: this has to be used!!!
      Just _ -> True
  | otherwise = False

---------------------------------------------------------------------------------------------------
-- Application
---------------------------------------------------------------------------------------------------
-- TODO: Add correspondence of locations!!!
-- Maybe have no-io verision for accleration attractor
-- make applicability a DOCUMENTED precondition!!!
applyIn :: Config -> Variables -> SummaryContent -> SymSt -> IO (Term, SyBo)
applyIn conf vars summary reach =
  let condImpl =
        FOL.andfL (SymSt.toList (targets summary)) $ \(l, next) ->
          Vars.forallX vars $ FOL.impl (get reach l) next
     -- ^ condition that the current target 'reach' is part of the symbolic target
      constr = FOL.exists (map fst (metaVars summary)) $ FOL.andf [condImpl, enforcable summary]
     -- ^ overall summary
      prog = error "TODO IMPLEMENT: needs Skolem function computation :("
     -- ^ programm computation
   in pure (constr, prog)

---------------------------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------------------------- 
computeSum :: Config -> Attr -> Player -> Arena -> Loc -> IO (SummaryKey, Maybe SummaryContent)
computeSum conf attr player arena loc = do
  conf <- pure $ setName "SummaryGen" conf
    -- TODO: check with dublicates in loop game
  let subs = error "TODO: induced substutff" loc
  (arena, oldToNew) <- pure $ inducedSubArena arena subs
  loc <- pure $ oldToNew loc
  let key = SummaryKey {sumPlayer = player, sumArena = arena, sumLoc = loc}
  template <- computeTemplate conf arena subs
  let metas =
        Map.toList
          $ Map.filterWithKey (\var _ -> var `notElem` stateVars arena)
          $ FOL.bindings
          $ FOL.orf
          $ map snd
          $ SymSt.toList template
  arena <- pure $ addConstants metas arena
    -- TODO: underapproximation restriction?
  (attrRes, templProg) <- attr conf player arena template
    -- This program somehow needs the backmapping as wall as the summary content, no?
  enforce <- SMT.simplify conf $ attrRes `get` loc
  sat <- SMT.sat conf enforce
  if not sat
    then pure (key, Nothing)
    else do
      let content =
            SummaryContent
              {metaVars = metas, enforcable = enforce, targets = template, sybo = templProg}
      pure (key, Just content)

computeTemplate :: Config -> Arena -> Loc -> IO SymSt
computeTemplate conf arena loc = do
  indeps <- independentProgVars conf arena
  error "TODO"

---------------------------------------------------------------------------------------------------
-- Per Game Things
---------------------------------------------------------------------------------------------------
isSubarenaFrom :: (Loc, Arena) -> (Loc, Arena) -> Maybe (Loc -> Loc)
isSubarenaFrom (lSub, arenaSub) (l, arena) = error "TODO IMPLEMENT: implement per game type"

addConstants :: [(Symbol, Sort)] -> Arena -> Arena
addConstants = error "TODO IMPLEMENT"
---------------------------------------------------------------------------------------------------
