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

import Issy.Base.SymbolicState (SymSt, get)
import qualified Issy.Base.Variables as Vars
import Issy.Base.Variables (Variables)
import Issy.Config (Config, setName)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
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
  { metaVars :: [Symbol]
  , enforcable :: Term
    -- ^ 'enforcable' is the main formula part!
  , targets :: [(Loc, Term)] -- ALTERNATIVE SymbolicState?
  , sybo :: SyBo
    -- ^ 'sybo' is the book-kept strategy with meta variables
  }

--------------------------------------------------------------------------------------------------- 
-- High Level Procedure
--------------------------------------------------------------------------------------------------- 
-- TODO: document, do not QELIM result, that is resposibility of caller
trySummary :: Config -> Player -> Arena -> Loc -> EnfSt -> SymSt -> IO (EnfSt, Maybe (Term, SyBo))
trySummary conf player arena loc enfst reach = do
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
          (key, content) <- computeSum conf player arena loc
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
        FOL.andfL (targets summary) $ \(l, next) -> Vars.forallX vars $ FOL.impl (get reach l) next
     -- ^ condition that the current target 'reach' is part of the symbolic target
      constr = FOL.exists (metaVars summary) $ FOL.andf [condImpl, enforcable summary]
     -- ^ overall summary
      prog = error "TODO IMPLEMENT: needs Skolem function computation :("
     -- ^ programm computation
   in pure (constr, prog)

---------------------------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------------------------- 
computeSum :: Config -> Player -> Arena -> Loc -> IO (SummaryKey, Maybe SummaryContent)
computeSum =
  error
    "TODO IMPLEMENT: build sub-game with additional variables, and equality contraints! attractor computation + acceleration with new computation (cyclic dependency!)"

---------------------------------------------------------------------------------------------------
-- Per Game Things
---------------------------------------------------------------------------------------------------
isSubarenaFrom :: (Loc, Arena) -> (Loc, Arena) -> Maybe (Loc -> Loc)
isSubarenaFrom (lSub, arenaSub) (l, arena) = error "TODO IMPLEMENT: implement per game type"

constructSubarena :: Arena -> Loc -> (Arena, Loc, Loc -> Loc)
constructSubarena = error "TODO IMPLEMENT: per game type"
---------------------------------------------------------------------------------------------------
