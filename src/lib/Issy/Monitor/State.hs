---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Monitor.State
-- Description : Monitor state
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the semantic monitor state, access operations, expansion operations,
-- caching and more. Note that in the data structure of the monitor itself this is called
-- the state label.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Monitor.State
  ( State
  , -- Creation and normalization
    initSt
  , trueSt
  , falseSt
  , normSt
  , simpleNormSt
  , isSafeSt
  , isTrue
  , isFalse
  , -- Expansion operations
    ExpansionState
  , toExpansionState
  , fromExpansionState
  , normESt
  , replaceSt
  , replacesSt
  , pickFreeSt
  , pickUpdSt
  , setUpdSt
  , expandSt
  , shiftSt
  , -- Rules operation
    Domain(..)
  , eset
  , fset
  , impD
  , current
  , dedInv
  , weaks
  , reorganise
  , invalidate
  , addImp
  , addFacts
  , newImps
  , mapFs
  , filterDom
  , -- Pretty printing
    stateToString
  ) where

---------------------------------------------------------------------------------------------------
import Data.List (partition)
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Monitor.Formula (Formula)
import qualified Issy.Monitor.Formula as MF

---------------------------------------------------------------------------------------------------
-- | Opaque implementation of the semantic monitor state. The implementation mainly follows
-- the description in the paper. However, this data structure is opaque to ensure proper
-- handling and normalisation.
data State = State
  { ea :: [Formula]
  , fa :: [Formula]
  , eg :: [Formula]
  , fg :: [Formula]
  , impA :: Set (Formula, Formula)
  , impG :: Set (Formula, Formula)
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Initialization and normalisation
---------------------------------------------------------------------------------------------------
-- | Create a monitor state from a list of assumptions and guarantees.
initSt :: [Formula] -> [Formula] -> State
initSt assume guarantee =
  normSt $ State {ea = [], fa = assume, eg = [], fg = guarantee, impA = Set.empty, impG = Set.empty}

-- | The state that represents false. It always has an unsafe verdict.
falseSt :: State
falseSt =
  State {ea = [], fa = [], eg = [MF.FFalse], fg = [MF.FFalse], impA = Set.empty, impG = Set.empty}

-- | The state that represents true. It always has a valid verdict.
trueSt :: State
trueSt =
  State {ea = [MF.FFalse], fa = [MF.FFalse], eg = [], fg = [], impA = Set.empty, impG = Set.empty}

-- | Apply normalization operations to a state.
normSt :: State -> State
normSt = genericNormSt $ MF.normAnd . map MF.toplevelCNF

-- | Apply simple normalization operations to a state. This is computational less
-- costly than 'normSt' but also less through. 'normSt' should be applied to a state once
-- in a while.
simpleNormSt :: State -> State
simpleNormSt = genericNormSt MF.normAndLight

genericNormSt :: ([Formula] -> [Formula]) -> State -> State
genericNormSt norm st =
  let ea' = norm (ea st)
      fa' = norm (fa st)
      eg' = norm (eg st)
      fg' = norm (fg st)
   in if ea' == [MF.FFalse] || fa' == [MF.FFalse] || null (fg' ++ eg')
        then trueSt
        else if fg' == [MF.FFalse] || eg' == [MF.FFalse]
               then if null (fa' ++ ea')
                      then falseSt
                      else falseSt {ea = ea', fa = fa', impA = impA st}
               else st {ea = ea', fa = fa', eg = eg', fg = fg'}

-- | Check if a state represent a safety formula.
isSafeSt :: State -> Bool
isSafeSt st =
  all MF.notTemporal (ea st)
    && all MF.notTemporal (fa st)
    && all MF.isSafe (eg st)
    && all MF.isSafe (fg st)

-- | Check if a state represents false.
isFalse :: State -> Bool
isFalse st = null (ea st ++ fa st) && (MF.FFalse `elem` (eg st ++ fg st))

-- | Check if a state represents true.
isTrue :: State -> Bool
isTrue st = null (eg st ++ fg st) || (MF.FFalse `elem` ea st) || (MF.FFalse `elem` fa st)

---------------------------------------------------------------------------------------------------
-- Expansions
---------------------------------------------------------------------------------------------------
-- | Representation of an intermediate state during expansion.
newtype ExpansionState =
  ExpansionState State
  -- ^ This is just a normal state. The point of this interface is to increase type safety
  -- to avoid that a half expanded state is used somewhere else. That allows us also to make
  -- optimization to avoid passing impG and impA around and doing operations on those
  -- as this is not needed during expansion.
  deriving (Eq, Ord, Show)

-- | Make a state read for expansion.
toExpansionState :: State -> ExpansionState
toExpansionState st = ExpansionState $ st {impA = Set.empty, impG = Set.empty}

-- | Next-expand the expansion state.
expandSt :: ExpansionState -> ExpansionState
expandSt = mapES $ mapFormulas MF.expand

-- | Find an pick a free current-time predicate for expansion.
pickFreeSt :: ExpansionState -> Maybe Term
pickFreeSt (ExpansionState st) =
  case concatMap MF.currentTerms (stateFormulas st) of
    [] -> Nothing
    (term, _):_ -> Just term

-- | Replace a free current-time predicate by a boolean value.
replaceSt :: (Term, Bool) -> ExpansionState -> ExpansionState
replaceSt asg = mapES $ simpleNormSt . mapFormulas (MF.replaceT asg)

-- | Replace multiple free current-time predicates by a boolean values.
replacesSt :: Set (Term, Bool) -> ExpansionState -> ExpansionState
replacesSt asgs =
  mapES $ \st -> simpleNormSt $ foldl (\st asg -> mapFormulas (MF.replaceT asg) st) st asgs

-- | Find and pick a free current-time update for expansion.
pickUpdSt :: ExpansionState -> Maybe (Symbol, Term)
pickUpdSt (ExpansionState st) =
  case concatMap MF.currentUpdates (stateFormulas st) of
    [] -> Nothing
    upd:_ -> Just upd

-- | Replace a free current-time update by a boolean value.
setUpdSt :: (Symbol, Term) -> Bool -> ExpansionState -> ExpansionState
setUpdSt upd pol = mapES $ simpleNormSt . mapFormulas (MF.replaceU upd pol)

-- | Normalize an expansion state.
normESt :: ExpansionState -> ExpansionState
normESt = mapES normSt

-- | Shift the expansion state removing the top level next operators. This is only
-- sound and defined if no free current-time literals or updates are present.
shiftSt :: ExpansionState -> ExpansionState
shiftSt = mapES $ mapFormulas MF.shift

-- | Create the new state after expansion. This needs the old state before expansion.
fromExpansionState :: State -> ExpansionState -> State
fromExpansionState oldSt (ExpansionState expSt) = expSt {impA = impA oldSt, impG = impG oldSt}

mapES :: (State -> State) -> ExpansionState -> ExpansionState
mapES mp (ExpansionState st) = ExpansionState (mp st)

mapFormulas :: (Formula -> Formula) -> State -> State
mapFormulas fm st =
  State
    { ea = fm <$> ea st
    , fa = fm <$> fa st
    , eg = fm <$> eg st
    , fg = fm <$> fg st
    , impA = impA st
    , impG = impG st
    }

stateFormulas :: State -> [Formula]
stateFormulas st = concat [ea st, fa st, eg st, fg st]

---------------------------------------------------------------------------------------------------
-- Rule access and modification operations
---------------------------------------------------------------------------------------------------
-- | States have assumptions and guarantees parts, i.e. different domains.
data Domain
  = Assumptions
  -- ^ Indicates the assumption domain.
  | Guarantees
  -- ^ Indicates the domain of guarantees.
  deriving (Eq, Ord, Show)

-- | "E" part of the state, i.e. formulas that have been designated to be used to derive thing
-- from "Imp". They will usually contain globallies and time bound things that fell out
-- from the formula.
eset :: Domain -> State -> [Formula]
eset Assumptions = ea
eset Guarantees = eg

-- | The "F" part of the state, i.e. formulas that have been derived or simplified from "Imp" parts.
fset :: Domain -> State -> [Formula]
fset Assumptions = fa
fset Guarantees = fg

-- | The "Imp" part of the state, i.e. the precondition-postconditions pairs that
-- have been derived to always hold in a state (i.e. now and in the future).
-- They are derived from the "E" part and existing "Imp" parts.
impD :: Domain -> State -> Set (Formula, Formula)
impD Assumptions = impA
impD Guarantees = impG

-- | Return what in a given domain is currently assumed to hold and derivable from.
current :: Domain -> State -> [Formula]
current dom st =
  case dom of
    Assumptions -> go $ eset Assumptions st
    Guarantees -> go $ eset Assumptions st ++ eset Guarantees st
  where
    go =
      \case
        [] -> []
        MF.FGlobally f:fr
          | MF.notTemporal f -> f : go fr
          | otherwise -> go fr
        f:fr
          | MF.notTemporal f -> f : go fr
          | otherwise -> go fr

-- | Return what is currently be derivable as an invariant without temporal behavior.
dedInv :: Domain -> State -> [Formula]
dedInv dom =
  filter MF.notTemporal . map (\(prem, conc) -> MF.for [MF.fnot prem, conc]) . Set.toList . impD dom

-- | Return the weak until statements in the current "F".
weaks :: Domain -> State -> [(Formula, Formula)]
weaks dom = go . fset dom
  where
    go =
      \case
        [] -> []
        MF.FWeak f g:fr
          | MF.notTemporal f && MF.notTemporal g -> (f, g) : go fr
          | otherwise -> go fr
        _:fr -> go fr

-- | Rearrange the state moving things from the "F" to "G" if soundly possible and
-- potentially useful.
reorganise :: State -> State
reorganise st =
  let (conA, fa') = partition consolidate (fa st)
      (conG, fg') = partition consolidate (fg st)
   in st {ea = ea st ++ conA, fa = fa', eg = eg st ++ conG, fg = fg'}

consolidate :: Formula -> Bool
consolidate =
  \case
    MF.FGlobally f -> MF.notTemporal f
    MF.FWeak f g -> MF.notTemporal f && MF.notTemporal g
    f -> MF.notTemporal f

-- | Reduce a part of the state to false. For the assumption, this means that the states
-- semantic formula becomes true. For the guarantees that means that now the assumptions
-- mus be violated.
invalidate :: Domain -> State -> State
invalidate Assumptions _ = trueSt
invalidate Guarantees st = st {eg = [MF.FFalse], fg = [MF.FFalse], impG = Set.empty}

-- | Add an rule-derived "Imp" part to a state. This "Imp" part has to hold globally.
addImp :: Config -> String -> Domain -> State -> (Formula, Formula) -> IO State
addImp _ _ _ st (_, MF.FTrue) = pure st
addImp _ _ _ st (MF.FFalse, _) = pure st
addImp cfg ruleName dom st impC =
  let imp = norm impC
   in case dom of
        Assumptions
          | imp `elem` impA st -> pure st
          | otherwise -> do
            lg cfg [ruleName, "add to impA", strImp imp]
            let impA' = Set.insert imp (impA st)
            let impG' = Set.insert imp (impG st)
            pure $ st {impA = impA', impG = impG'}
        Guarantees
          | imp `elem` impG st -> pure st
          | otherwise -> do
            lg cfg [ruleName, "add to impG", strImp imp]
            let impG' = Set.insert imp (impG st)
            pure $ st {impG = impG'}
  where
    strImp = strP MF.toString MF.toString
    --
    norm =
      \case
        (MF.FTrue, MF.FOr [a, b])
          | MF.notTemporal a -> (MF.fnot a, b)
          | MF.notTemporal b -> (MF.fnot b, a)
          | otherwise -> (MF.FTrue, MF.FOr [a, b])
        imp -> imp

-- | Map the formulas in the "F" part of a state.
mapFs :: Domain -> State -> (Formula -> Formula) -> State
mapFs dom st mp =
  case dom of
    Assumptions -> st {fa = map mp (fa st)}
    Guarantees -> st {fg = map mp (fg st)}

-- | Add simple one-time facts to a state. Those might come from predicate propagation.
addFacts :: [Term] -> State -> State
addFacts facts st = st {fg = map (MF.fpred True) facts ++ fg st}

-- | Compute the difference between two state to get newly computed "Imp" parts.
-- This is used for the derivation search.
newImps :: State -> State -> Set (Domain, Formula, Formula)
newImps stOld stNew =
  let diffD dom = Set.map (\(f, g) -> (dom, f, g)) $ impD dom stNew `Set.difference` impD dom stOld
   in diffD Assumptions `Set.union` diffD Guarantees

-- | Filtering function to filter for formulas of a specific domain.
filterDom :: Domain -> Set (Domain, Formula, Formula) -> Set (Formula, Formula)
filterDom dom = Set.map (\(_, f, g) -> (f, g)) . Set.filter (\(d, _, _) -> d == dom)

---------------------------------------------------------------------------------------------------
-- Pretty printing
---------------------------------------------------------------------------------------------------
-- | Pretty print a state.
stateToString :: State -> String
stateToString st =
  "State {"
    ++ partL ea "ea"
    ++ partL fa "fa"
    ++ partL eg "eg"
    ++ partL fg "fg"
    ++ partS (impD Assumptions) "impA"
    ++ partS (impD Guarantees) "impG"
    ++ " }"
  where
    partL op opname = " " ++ opname ++ " = " ++ strL MF.toString (op st)
    partS op opname = " " ++ opname ++ " = " ++ strS (strP MF.toString MF.toString) (op st)
---------------------------------------------------------------------------------------------------
