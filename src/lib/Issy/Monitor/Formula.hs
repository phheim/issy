---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Monitor.Formula
-- Description : Formula representation for monitor internals
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a temporal logic formula representation for computing
-- monitors. Note that we intentionally do no use other representation to decouple changes
-- there from the workings of the monitor which are quite specific and sensitive to
-- syntactic changes. In addition, while some constructor parts of the formula representation
-- are exposed for matching, in many cases the abstract construction methods should be used,
-- to create a formula.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Monitor.Formula
  ( -- Data structure
    Formula(FTrue, FOr, FAnd, FWeak, FNext, FFalse, FGlobally, FEventually)
  , toString
  , -- Construction
    ftrue
  , ffalse
  , fpred
  , fupdate
  , fand
  , for
  , fnext
  , fglobally
  , feventually
  , fweak
  , fnot
  , -- Query and check
    currentTerms
  , currentUpdates
  , notTemporal
  , staticFormula
  , stateOnly
  , findTerms
  , isSafe
  , notNestedSubForms
  , -- Expansion
    expand
  , shift
  , replaceT
  , replaceU
  , subst
  , substT
  , substNotNested
  , staticFormulaToTerm
  , encodeFormula
  , -- Substitution
    normAnd
  , normAndLight
  , toplevelCNF
  , -- Normalization
    fromTSL
  , fromRPLTL
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Set as Set

import Issy.Prelude

import qualified Issy.Games.Variables as Vars
import Issy.Logic.FOL (Constant(..), Term(..))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.Logic.TSLMT as TSL
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Printers.SMTLib as SMTLib

---------------------------------------------------------------------------------------------------
-- Data Structures
---------------------------------------------------------------------------------------------------
-- | Representation of either an RPLTL or TSLMT temporal logic formula in negation normal from.
data Formula
  = FTrue
  -- ^ Boolean true constant.
  | FFalse
  -- ^ Boolean false constant.
  | FPred Bool Term
  -- ^ Predicate with polarity. 'True' means positive polarity and 'False' means negative
  -- polarity, i.e. the term is negated.
  | FUpdate Bool Symbol Term
  -- ^ Update term with polarity. Those should only appear in TSLMT base formulas.
  | FAnd [Formula]
  -- ^ Boolean conjunction.
  | FOr [Formula]
  -- ^ Boolean disjunction.
  | FNext Formula
  -- ^ Temporal next operator.
  | FGlobally Formula
  -- ^ Temporal globally operator.
  | FEventually Formula
  -- ^ Temporal eventually operator.
  | FWeak Formula Formula
  -- ^ Temporal weak until operator.
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Pretty Printer
---------------------------------------------------------------------------------------------------
-- | Pretty print a formula.
toString :: Formula -> String
toString = go
  where
    go =
      \case
        FTrue -> "true"
        FFalse -> "false"
        FPred pol pred
          | pol -> SMTLib.toString pred
          | otherwise -> "!" ++ SMTLib.toString pred
        FUpdate pol var upd
          | pol -> "(" ++ var ++ ":=" ++ SMTLib.toString upd ++ ")"
          | otherwise -> "!(" ++ var ++ ":=" ++ SMTLib.toString upd ++ ")"
        FAnd fs -> "(AND" ++ concatMap ((' ' :) . go) fs ++ ")"
        FOr fs -> "(OR" ++ concatMap ((' ' :) . go) fs ++ ")"
        FNext f -> "(X " ++ go f ++ ")"
        FGlobally f -> "(G " ++ go f ++ ")"
        FEventually f -> "(F " ++ go f ++ ")"
        FWeak f g -> "(" ++ go f ++ " W " ++ go g ++ ")"

---------------------------------------------------------------------------------------------------
-- Construction
---------------------------------------------------------------------------------------------------
-- | Construct "true" as a formula.
ftrue :: Formula
ftrue = FTrue

-- | Construct "false" as a formula.
ffalse :: Formula
ffalse = FFalse

-- | Construct a predicate (boolean term) as a formula. The 'Bool' represent the
-- predicates polarity, i.e. if it is 'False' the predicate is negated.
fpred :: Bool -> Term -> Formula
fpred pol =
  \case
    Const (CBool True)
      | pol -> ftrue
      | otherwise -> ffalse
    Const (CBool False)
      | pol -> ffalse
      | otherwise -> ftrue
    Func FOL.FNot [term] -> FPred (not pol) term
    Func FOL.FAnd terms
      | pol -> fand (map (fpred pol) terms)
      | otherwise -> for (map (fpred pol) terms)
    Func FOL.FOr terms
      | pol -> for (map (fpred pol) terms)
      | otherwise -> fand (map (fpred pol) terms)
    term -> FPred pol term

-- | Construct a TSLMT update as a formula, with an additional polarity.
fupdate :: Bool -> Symbol -> Term -> Formula
fupdate = FUpdate

uniqueInsert :: Ord a => a -> [a] -> [a]
uniqueInsert x =
  \case
    [] -> [x]
    y:yr
      | x < y -> x : y : yr
      | x == y -> y : yr
      | otherwise -> y : uniqueInsert x yr

-- | Normalize a conjunction of formulas.
normAnd :: [Formula] -> [Formula]
normAnd = go []
  where
    go acc =
      \case
        [] -> acc
        FFalse:_ -> [FFalse]
        FTrue:fs -> go acc fs
        (FAnd fs):gs -> go acc (fs ++ gs)
        f:fr -> go (uniqueInsert f acc) fr

-- | Normalize a conjunction of formulas. This normalization is a
-- lighter (less computation, smaller effect) of 'normAnd'.
normAndLight :: [Formula] -> [Formula]
normAndLight = go []
  where
    go acc =
      \case
        [] -> acc
        FFalse:_ -> [FFalse]
        FTrue:fs -> go acc fs
        (FAnd fs):gs -> go acc (fs ++ gs)
        f:fr -> go (f : acc) fr

-- | Conjunctions of formulas.
fand :: [Formula] -> Formula
fand fs =
  case normAnd fs of
    [] -> FTrue
    [f] -> f
    fs -> FAnd fs

normOr :: [Formula] -> [Formula]
normOr = go []
  where
    go acc =
      \case
        [] -> acc
        FTrue:_ -> [FTrue]
        FFalse:fs -> go acc fs
        (FOr fs):gs -> go acc (fs ++ gs)
        f:fr -> go (uniqueInsert f acc) fr

-- | Disjunctions of formulas.
for :: [Formula] -> Formula
for fs =
  case normOr fs of
    [] -> FFalse
    [f] -> f
    fs -> FOr fs

-- | Apply the next operator to a formula.
fnext :: Formula -> Formula
fnext =
  \case
    FTrue -> FTrue
    FFalse -> FFalse
    f -> FNext f

-- | Apply the globally operator to a formula.
fglobally :: Formula -> Formula
fglobally =
  \case
    FTrue -> FTrue
    FFalse -> FFalse
    FGlobally f -> FGlobally f
    FNext f -> fnext (fglobally f)
    FAnd fs -> fand (map fglobally fs)
    f -> FGlobally f

-- | Apply the eventually operator to a formula.
feventually :: Formula -> Formula
feventually =
  \case
    FTrue -> FTrue
    FFalse -> FFalse
    FEventually f -> FEventually f
    FNext f -> fnext (feventually f)
    FOr fs -> for (map feventually fs)
    FWeak f g -> for [feventually (fglobally f), feventually g]
    f -> FEventually f

-- | Apply the weak until operator to formulas.
fweak :: Formula -> Formula -> Formula
fweak f g =
  case (f, g) of
    (FTrue, _) -> FTrue
    (_, FTrue) -> FTrue
    (FFalse, _) -> g
    (_, FFalse) -> fglobally f
    (FNext f, FNext g) -> fnext (fweak f g)
    (f, FEventually g) -> for [fglobally f, feventually g]
    _ -> FWeak f g

-- | Apply boolean negation to a formula. As the formulas are represented in
-- negation normal form, this might involve traversing the whole existing formula.
fnot :: Formula -> Formula
fnot =
  \case
    FTrue -> FFalse
    FFalse -> FTrue
    FPred pol term -> FPred (not pol) term
    FUpdate pol var term -> FUpdate (not pol) var term
    FAnd fs -> for (map fnot fs)
    FOr fs -> fand (map fnot fs)
    FNext f -> fnext (fnot f)
    FGlobally f -> feventually (fnot f)
    FEventually f -> fglobally (fnot f)
    FWeak f g ->
      let h = fand [fnot f, fnot g]
       in fand [fweak (fnot g) h, feventually h]

---------------------------------------------------------------------------------------------------
-- Queries
---------------------------------------------------------------------------------------------------
-- | Return the all predicates that are not under a temporal operator. This also does not include
-- predicates that are under a temporal that also holds in the current step (like globally).
currentTerms :: Formula -> [(Term, Bool)]
currentTerms =
  \case
    FTrue -> []
    FFalse -> []
    FPred pol pred -> [(pred, pol)]
    FUpdate {} -> []
    FAnd fs -> concatMap currentTerms fs
    FOr fs -> concatMap currentTerms fs
    FNext _ -> []
    FGlobally _ -> []
    FEventually _ -> []
    FWeak _ _ -> []

-- | Like 'currentTerms' but for updates.
currentUpdates :: Formula -> [(Symbol, Term)]
currentUpdates =
  \case
    FTrue -> []
    FFalse -> []
    FPred _ _ -> []
    FUpdate _ var term -> [(var, term)]
    FAnd fs -> concatMap currentUpdates fs
    FOr fs -> concatMap currentUpdates fs
    FNext _ -> []
    FGlobally _ -> []
    FEventually _ -> []
    FWeak _ _ -> []

-- | Check if a formula is not temporal, i.e. has now temporal operator. Next-state
-- relation predicates or updates are fine.
notTemporal :: Formula -> Bool
notTemporal =
  \case
    FTrue -> True
    FFalse -> True
    FPred _ _ -> True
    FUpdate {} -> True
    FAnd fs -> all notTemporal fs
    FOr fs -> all notTemporal fs
    FNext _ -> False
    FGlobally _ -> False
    FEventually _ -> False
    FWeak _ _ -> False

-- | Check if a formula is static, i.e. is not temporal and does not include
-- next-state relation predicates or updates. This condition is stronger than
-- the one of 'notTemporal'.
staticFormula :: Variables -> Formula -> Bool
staticFormula vars = go
  where
    go =
      \case
        FTrue -> True
        FFalse -> True
        FPred _ pred ->
          FOL.symbols pred `Set.isSubsetOf` (Vars.inputs vars `Set.union` Vars.stateVars vars)
        FAnd fs -> all go fs
        FOr fs -> all go fs
        _ -> False

-- | Check if a formula is not temporal, has no updates, and all free variables in the predicates
-- satisfy the given condition.
stateOnly :: (Symbol -> Bool) -> Formula -> Bool
stateOnly stateVar =
  \case
    FTrue -> True
    FFalse -> True
    FPred _ terms -> all stateVar $ FOL.frees terms
    FAnd fs -> all (stateOnly stateVar) fs
    FOr fs -> all (stateOnly stateVar) fs
    _ -> False

-- | Extract all predicate terms in a formula, independent of their "temporal location".
findTerms :: Formula -> Set Term
findTerms =
  \case
    FTrue -> Set.empty
    FFalse -> Set.empty
    FPred _ term -> Set.singleton term
    FUpdate {} -> Set.empty
    FAnd fs -> Set.unions $ map findTerms fs
    FOr fs -> Set.unions $ map findTerms fs
    FNext f -> findTerms f
    FGlobally f -> findTerms f
    FEventually f -> findTerms f
    FWeak f g -> findTerms f `Set.union` findTerms g

-- | Check if a formula is in the syntactic safety formula fragment.
isSafe :: Formula -> Bool
isSafe =
  \case
    FTrue -> True
    FFalse -> True
    FPred _ _ -> True
    FUpdate {} -> True
    FAnd fs -> all isSafe fs
    FOr fs -> all isSafe fs
    FNext f -> isSafe f
    FGlobally f -> isSafe f
    FWeak f g -> isSafe f && isSafe g
    FEventually _ -> False

-- | Extract all formulas that are sub-formulas of the given one, on the boolean
-- top level. For example on "(G a) || (F b)", this would include "G a", "F b", and
-- "(G a) || (F b)" but not "a" or "b".
notNestedSubForms :: Formula -> Set Formula
notNestedSubForms f =
  Set.insert f
    $ case f of
        FAnd fs -> Set.unions (map notNestedSubForms fs)
        FOr fs -> Set.unions (map notNestedSubForms fs)
        _ -> Set.empty

---------------------------------------------------------------------------------------------------
-- Expansion
---------------------------------------------------------------------------------------------------
-- | Expand the formula with the expansion rules.
expand :: Formula -> Formula
expand =
  \case
    FTrue -> FTrue
    FFalse -> FFalse
    FPred pol pred -> FPred pol pred
    FUpdate pol var term -> FUpdate pol var term
    FAnd fs -> FAnd $ map expand fs
    FOr fs -> FOr $ map expand fs
    FNext f -> FNext f
    FGlobally f -> FAnd [expand f, FNext (FGlobally f)]
    FEventually f -> FOr [expand f, FNext (FEventually f)]
    FWeak f g -> FOr [expand g, FAnd [expand f, FNext (FWeak f g)]]

-- | Move a formula one step in the future. This is undefined if the formula still contains
-- parts that are relevant for the current time step.
shift :: Formula -> Formula
shift =
  \case
    FTrue -> ftrue
    FFalse -> ffalse
    FPred _ _ -> error "assert: cannot shift predicate"
    FUpdate {} -> error "assert: cannot shift update"
    FAnd fs -> fand $ map shift fs
    FOr fs -> for $ map shift fs
    FNext f -> f
    FGlobally _ -> error "assert: cannot shift globally"
    FEventually _ -> error "assert: cannot shift eventually"
    FWeak _ _ -> error "assert: cannot shift weak until"

---------------------------------------------------------------------------------------------------
-- Substitution
---------------------------------------------------------------------------------------------------
-- | Replace a predicate term by a boolean constant everywhere where it is not under a temporal
-- operator.
replaceT :: (Term, Bool) -> Formula -> Formula
replaceT (term, pol) = go
  where
    go =
      \case
        FTrue -> ftrue
        FFalse -> ffalse
        FPred p t
          | t == term && p == pol -> ftrue
          | t == term && p /= pol -> ffalse
          | otherwise -> fpred p t
        FUpdate pol var term -> fupdate pol var term
        FAnd fs -> fand $ map go fs
        FOr fs -> for $ map go fs
        FNext f -> FNext f
        FGlobally f -> FGlobally f
        FEventually f -> FEventually f
        FWeak f g -> FWeak f g

-- | Replace an update by a boolean constant everywhere where it is not under a temporal operator.
replaceU :: (Symbol, Term) -> Bool -> Formula -> Formula
replaceU (var, term) pol = go
  where
    go =
      \case
        FTrue -> ftrue
        FFalse -> ffalse
        FPred p t -> fpred p t
        FUpdate p v t
          | v == var && t == term && pol == p -> ftrue
          | v == var && t == term && pol /= p -> ffalse
          | v == var && t /= term && pol && p -> ffalse
          | otherwise -> fupdate p v t
        FAnd fs -> fand $ map go fs
        FOr fs -> for $ map go fs
        FNext f -> FNext f
        FGlobally f -> FGlobally f
        FEventually f -> FEventually f
        FWeak f g -> FWeak f g

-- | Replace a predicate term by a boolean constant (including under temporal operators).
substT :: (Term, Bool) -> Formula -> Formula
substT (term, pol) = go
  where
    go =
      \case
        FTrue -> ftrue
        FFalse -> ffalse
        FPred p t
          | t == term && p == pol -> ftrue
          | t == term && p /= pol -> ffalse
          | otherwise -> fpred p t
        FUpdate pol var term -> fupdate pol var term
        FAnd fs -> fand $ map go fs
        FOr fs -> for $ map go fs
        FNext f -> fnext (go f)
        FGlobally f -> fglobally (go f)
        FEventually f -> feventually (go f)
        FWeak f g -> fweak (go f) (go g)

-- | Replace a sub-formula by another formula in a formula.
subst :: Formula -> Formula -> Formula -> Formula
subst old new = go
  where
    go f
      | f == old = new
      | otherwise =
        case f of
          FTrue -> ftrue
          FFalse -> ffalse
          FPred pol term -> fpred pol term
          FUpdate pol var term -> fupdate pol var term
          FAnd fs -> fand (map go fs)
          FOr fs -> for (map go fs)
          FNext f -> fnext (go f)
          FGlobally f -> fglobally (go f)
          FEventually f -> feventually (go f)
          FWeak f g -> fweak (go f) (go g)

-- | Replace a sub-formula if its not under a temporal operator by another formula in a formula.
substNotNested :: Formula -> Formula -> Formula -> Formula
substNotNested old new = go
  where
    go f
      | f == old = new
      | otherwise =
        case f of
          FAnd fs -> fand (map go fs)
          FOr fs -> for (map go fs)
          other -> other

-- | Turn a formula on which 'staticFormula' holds into a semantically equivalent term.
staticFormulaToTerm :: Formula -> Term
staticFormulaToTerm = go
  where
    go =
      \case
        FTrue -> FOL.true
        FFalse -> FOL.false
        FPred True p -> p
        FPred False p -> FOL.neg p
        FAnd fs -> FOL.andf $ map go fs
        FOr fs -> FOL.orf $ map go fs
        _ -> error "Formula not update free"

-- | Turn a formula on which 'notTemporal' holds into a semantically equivalent term.
encodeFormula :: ((Symbol, Term) -> Symbol) -> Formula -> Term
encodeFormula updateEncode =
  \case
    FTrue -> FOL.true
    FFalse -> FOL.false
    FPred True term -> term
    FPred False term -> FOL.neg term
    FUpdate True var term -> FOL.bvarT $ updateEncode (var, term)
    FUpdate False var term -> FOL.neg $ encodeFormula updateEncode (FUpdate True var term)
    FAnd fs -> FOL.andf $ map (encodeFormula updateEncode) fs
    FOr fs -> FOL.orf $ map (encodeFormula updateEncode) fs
    _ -> error "assert: temporal formula not allowed"

---------------------------------------------------------------------------------------------------
-- Normalization
---------------------------------------------------------------------------------------------------
-- | Normalize a formula by converting the boolean top-level to CNF.
toplevelCNF :: Formula -> Formula
toplevelCNF = fand . map for . toCNF

toCNF :: Formula -> [[Formula]]
toCNF =
  \case
    FTrue -> []
    FFalse -> [[]]
    FAnd fs -> concatMap toCNF fs
    FOr fs -> distr (++) (map toCNF fs)
    atom -> [[atom]]

distr :: (a -> a -> a) -> [[a]] -> [a]
distr comb =
  \case
    [] -> []
    [x] -> x
    x:xr -> [comb a b | a <- x, b <- distr comb xr]

---------------------------------------------------------------------------------------------------
-- Conversion
---------------------------------------------------------------------------------------------------
-- | Create a monitor formula from a TSLMT formula.
fromTSL :: TL.Formula TSL.Atom -> Formula
fromTSL =
  fromTL $ \case
    TSL.Update var term -> fupdate True var term
    TSL.Predicate term -> fpred True term

-- | Create a monitor formula from a RPLTL formula.
fromRPLTL :: TL.Formula RPLTL.Atom -> Formula
fromRPLTL = fromTL (fpred True)

fromTL :: (a -> Formula) -> TL.Formula a -> Formula
fromTL fromAtomic = go
  where
    go =
      \case
        TL.Atom a -> fromAtomic a
        TL.And fs -> fand $ map go fs
        TL.Or fs -> for $ map go fs
        TL.Not f -> fnot $ go f
        TL.UExp TL.Next f -> fnext $ go f
        TL.UExp TL.Globally f -> fglobally $ go f
        TL.UExp TL.Eventually f -> feventually $ go f
        TL.BExp op f g ->
          let (ff, fg) = (go f, go g)
           in case op of
                TL.WeakUntil -> fweak ff fg
                TL.Until -> fand [fweak ff fg, feventually fg]
                TL.Release -> fweak fg (fand [ff, fg])
---------------------------------------------------------------------------------------------------
