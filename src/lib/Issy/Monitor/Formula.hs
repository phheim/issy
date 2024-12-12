{-# LANGUAGE LambdaCase #-}

module Issy.Monitor.Formula
  ( Formula(FTrue, FOr, FAnd, FWeak, FNext, FFalse, FGlobally,
        FEventually)
  , formulaToString
  , ftrue
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
  , currentTerms
  , currentUpdates
  , notTemporal
  , staticFormula
  , stateOnly
  , findTerms
  , isSafe
  , notNestedSubForms
  , expand
  , shift
  , replaceT
  , replaceU
  , normAnd
  , normAndLight
  , toplevelCNF
  , fromTSL
  , fromRPLTL
  , staticFormulaToTerm
  , subst
  , substT
  , substNotNested
  , encodeFormula
  ) where

-------------------------------------------------------------------------------
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Logic.FOL
import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.Logic.TSLMT as TSL
import Issy.Logic.Temporal

import Issy.Printers.SMTLib (smtLib2)

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
data Formula
  = FTrue
  | FFalse
  | FPred Bool Term
  | FUpdate Bool Symbol Term
  | FAnd [Formula]
  | FOr [Formula]
  | FNext Formula
  | FGlobally Formula
  | FEventually Formula
  | FWeak Formula Formula
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Pretty Printer
-------------------------------------------------------------------------------
formulaToString :: Formula -> String
formulaToString = go
  where
    go =
      \case
        FTrue -> "true"
        FFalse -> "false"
        FPred pol pred
          | pol -> smtLib2 pred
          | otherwise -> "!" ++ smtLib2 pred
        FUpdate pol var upd
          | pol -> "(" ++ var ++ ":=" ++ smtLib2 upd ++ ")"
          | otherwise -> "!(" ++ var ++ ":=" ++ smtLib2 upd ++ ")"
        FAnd fs -> "(AND" ++ concatMap ((' ' :) . go) fs ++ ")"
        FOr fs -> "(OR" ++ concatMap ((' ' :) . go) fs ++ ")"
        FNext f -> "(X " ++ go f ++ ")"
        FGlobally f -> "(G " ++ go f ++ ")"
        FEventually f -> "(F " ++ go f ++ ")"
        FWeak f g -> "(" ++ go f ++ " W " ++ go g ++ ")"

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------
ftrue :: Formula
ftrue = FTrue

ffalse :: Formula
ffalse = FFalse

fpred :: Bool -> Term -> Formula
fpred pol =
  \case
    Const (CBool True)
      | pol -> ftrue
      | otherwise -> ffalse
    Const (CBool False)
      | pol -> ffalse
      | otherwise -> ftrue
    Func (PredefF "not") [term] -> FPred (not pol) term
    Func (PredefF "and") terms
      | pol -> fand (map (fpred pol) terms)
      | otherwise -> for (map (fpred pol) terms)
    Func (PredefF "or") terms
      | pol -> for (map (fpred pol) terms)
      | otherwise -> fand (map (fpred pol) terms)
    term -> FPred pol term

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

for :: [Formula] -> Formula
for fs =
  case normOr fs of
    [] -> FFalse
    [f] -> f
    fs -> FOr fs

fnext :: Formula -> Formula
fnext =
  \case
    FTrue -> FTrue
    FFalse -> FFalse
    f -> FNext f

fglobally :: Formula -> Formula
fglobally =
  \case
    FTrue -> FTrue
    FFalse -> FFalse
    FGlobally f -> FGlobally f
    FNext f -> fnext (fglobally f)
    FAnd fs -> fand (map fglobally fs)
    f -> FGlobally f

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

-------------------------------------------------------------------------------
-- Queries
-------------------------------------------------------------------------------
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

staticFormula :: Variables -> Formula -> Bool
staticFormula vars = go
  where
    go =
      \case
        FTrue -> True
        FFalse -> True
        FPred _ pred ->
          symbols pred `Set.isSubsetOf` (Vars.inputs vars `Set.union` Vars.stateVars vars)
        FAnd fs -> all go fs
        FOr fs -> all go fs
        _ -> False

stateOnly :: (Symbol -> Bool) -> Formula -> Bool
stateOnly stateVar =
  \case
    FTrue -> True
    FFalse -> True
    FPred _ terms -> all stateVar (frees terms)
    FAnd fs -> all (stateOnly stateVar) fs
    FOr fs -> all (stateOnly stateVar) fs
    _ -> False

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

notNestedSubForms :: Formula -> Set Formula
notNestedSubForms f =
  Set.insert f
    $ case f of
        FAnd fs -> Set.unions (map notNestedSubForms fs)
        FOr fs -> Set.unions (map notNestedSubForms fs)
        _ -> Set.empty

-------------------------------------------------------------------------------
-- Transformation
-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
-- Substituion
-------------------------------------------------------------------------------
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

replaceU :: (Symbol, Term) -> Bool -> Formula -> Formula
replaceU (var, term) pol = go
  where
    go =
      \case
        FTrue -> ftrue
        FFalse -> ffalse
        FPred p t -> fpred p t
        FUpdate p v t
            -- TODO: Check a second time!
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

staticFormulaToTerm :: Formula -> Term
staticFormulaToTerm = go
  where
    go =
      \case
        FTrue -> true
        FFalse -> false
        FPred True p -> p
        FPred False p -> neg p
        FAnd fs -> andf $ map go fs
        FOr fs -> orf $ map go fs
        _ -> error "Formula not update free"

-------------------------------------------------------------------------------
-- Normalization
-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
-- Encoding
-------------------------------------------------------------------------------
encodeFormula :: ((Symbol, Term) -> Symbol) -> Formula -> Term
encodeFormula updateEncode =
  \case
    FTrue -> true
    FFalse -> false
    FPred True term -> term
    FPred False term -> neg term
    FUpdate True var term -> bvarT $ updateEncode (var, term)
    FUpdate False var term -> neg $ encodeFormula updateEncode (FUpdate True var term)
    FAnd fs -> andf $ map (encodeFormula updateEncode) fs
    FOr fs -> orf $ map (encodeFormula updateEncode) fs
    _ -> error "assert: temporal formula not allowed"

-------------------------------------------------------------------------------
-- Conversion
-------------------------------------------------------------------------------
fromTL :: (a -> Formula) -> TL a -> Formula
fromTL fromAtomic = go
  where
    go =
      \case
        TLAtomic a -> fromAtomic a
        TLAnd fs -> fand $ map go fs
        TLOr fs -> for $ map go fs
        TLNot f -> fnot $ go f
        TLUnaryOp TLNext f -> fnext $ go f
        TLUnaryOp TLGlobally f -> fglobally $ go f
        TLUnaryOp TLEventually f -> feventually $ go f
        TLBinaryOp op f g ->
          let (ff, fg) = (go f, go g)
           in case op of
                TLWeakUntil -> fweak ff fg
                TLUntil -> fand [fweak ff fg, feventually fg]
                TLRelease -> fweak fg (fand [ff, fg])

fromTSL :: TSL.TSL -> Formula
fromTSL =
  fromTL $ \case
    TSL.TSLUpdate var term -> fupdate True var term
    TSL.TSLPredicate term -> fpred True term

fromRPLTL :: RPLTL.Formula -> Formula
fromRPLTL = fromTL (fpred True)
-------------------------------------------------------------------------------
