---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.FOL
-- Description : Data structures and methods to work with first-order terms and logic
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module provides an interface to work with first-order logic and terms. This includes
-- things like symbol handling and normalization. Inside Issy this module should be used to
-- handle those terms. Note that since almost everything depends on this changes that e.g.
-- change how certain terms are represented should be done with uttermost care, as some
-- methods work on the syntactic level. Beyond that, methods should --if possible-- avoid using
-- the data structure of 'Term's directly and should (e.g. for construction) use the abstract
-- interface.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.FOL
  ( -- Data structures
    Symbol
  , Function(..)
  , Term(..)
  , Sort(..)
  , Quantifier(..)
  , Constant(..)
  , -- Functions lists
    predefined
  , booleanFunctions
  , comparisionFunctions
  , -- Term construction (generic)
    constT
  , var
  , func
  , equal
  , forAll
  , exists
  , lambda
  , unintFunc
  , -- Term construction (booleans)
    true
  , false
  , boolConst
  , bvarT
  , andf
  , andfL
  , orf
  , orfL
  , neg
  , impl
  , implyT
  , iff
  , xor
  , exactlyOne
  , atMostOne
  , ite
  , distinct
  , -- Term construction (arithmetic)
    intConst
  , realConst
  , numberT
  , zeroT
  , oneT
  , ivarT
  , rvarT
  , toRealT
  , leqT
  , ltT
  , geqT
  , gtT
  , addT
  , invT
  , subT
  , minusT
  , multT
  , intdivT
  , modT
  , realdivT
  , absT
  , invertC
  , -- Query methods
    isNumber
  , isInteger
  , isNumericT
  , bindings
  , frees
  , sorts
  , decls
  , quantifierFree
  , ufFree
  , symbols
  , nonBoolTerms
  , -- Symbol handling
    uniqueName
  , uniquePrefix
  , unusedName
  , unusedPrefix
  , -- Model handling
    Model
  , modelToMap
  , emptyModel
  , modelAddT
  , sanitizeModel
  , setModel
  , mapTerm
  , mapTermFor
  , mapTermM
  , mapSymbol
  , setTerm
  , replaceUF
  , removePref
  , -- Transformations
    pushdownQE
  , removeDangling
  , -- Cheap SMT
    underapproxSAT
  ) where

---------------------------------------------------------------------------------------------------
import Data.Bifunctor (bimap, first, second)
import Data.List (isPrefixOf)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Data.Ratio ((%), denominator, numerator)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.Propositional

---------------------------------------------------------------------------------------------------
-- Data Structures
---------------------------------------------------------------------------------------------------
-- | A 'Symbol' is a variable symbol or a function name. Currently this is implemented by
-- a 'String'.
type Symbol = String

-- | 'Sort' represents Sorts, i.e. types in the SMT world
data Sort
  = SBool
  -- ^ values of this sort are booleans, i.e. true and false
  | SInt
  -- ^ values of this sort are integers, as in LIA
  | SReal
  -- ^ values of this sort are reals, as in LRA
  | SFunc [Sort] Sort
  -- ^ values of this sort are functions that map arguments from
  -- the given sorts to values of the single resulting sort, note
  -- that while this data structure allows to represent higher-order
  -- functions other parts of the implementation will probably not
  -- support those
  deriving (Eq, Ord, Show)

-- | Enum representation of function symbols
data Function
  = CustomF Symbol [Sort] Sort
  -- ^ this should be used to represent uninterpreted functions which
  -- have to be annotated by their type
  | FAnd
  -- ^ boolean conjunction, (SMTLib "and")
  | FOr
  -- ^ boolean disjunction, (SMTLib "and")
  | FNot
  -- ^ boolean negations, (SMTLib "and")
  | FDistinct
  -- ^ boolean mutual exclusion, (SMTLib "distinct")
  | FImply
  -- ^ boolean implication, (SMTLib "=>")
  | FIte
  -- ^ three-value if-then-else function (SMTLib "ite")
  | FAdd
  -- ^ arithmetic addition (SMTLib "+")
  | FMul
  -- ^ arithmetic multiplication (SMTLib "*")
  | FDivReal
  -- ^ real-value division (SMTLib "/")
  | FEq
  -- ^ equality (SMTLib "=")
  | FLt
  -- ^ less-than comparison (SMTLib "<")
  | FLte
  -- ^ less-than-equal comparison (SMTLib "<=")
  | FAbs
  -- ^ absolute value (SMTLib "abs")
  | FToReal
  -- ^ conversion from integers to reals (SMTLib "to_real")
  | FMod
  -- ^ remainder of integer division (SMTLib "mod")
  | FDivInt
  -- ^ integer division (SMTLib "div")
  deriving (Eq, Ord, Show)

-- | List of all boolean operation 'Function's
booleanFunctions :: [Function]
booleanFunctions = [FAnd, FOr, FNot, FDistinct, FImply]

-- | List of all compression 'Function's
comparisionFunctions :: [Function]
comparisionFunctions = [FEq, FLt, FLte]

-- | List of all predefined 'Function's
predefined :: [Function]
predefined =
  booleanFunctions
    ++ comparisionFunctions
    ++ [FIte, FAdd, FMul, FDivReal, FAbs, FToReal, FMod, FDivInt]

-- | Enum representation of quantifiers
data Quantifier
  = Exists
  -- ^ existential quantifier
  | Forall
  -- ^ universal quantifier
  deriving (Eq, Ord, Show)

-- | Representation of constant values
data Constant
  = CInt Integer
  -- ^ this is an integer constant
  | CReal Rational
  -- ^ this is an real-valued constant
  | CBool Bool
  -- ^ this is a boolean constant
  deriving (Eq, Ord, Show)

-- | Representation of first-order terms. For quantifiers and lambda
-- expression a shared space of de-Bruijn indices is used. Those
-- indices start from zero to reference quantifiers/lambda terms
-- on the current level
data Term
  = Var Symbol Sort
  -- ^ This is a constant variable symbols that is quantified on top-level.
  -- If not stated otherwise, a solver might assume that it is existentially
  -- quantified.
  | Const Constant
  -- ^ This is a constant expression
  | QVar Int
  -- ^ This is a quantified variable that is index with de-Bruijn indexing
  | Func Function [Term]
  -- ^ This represents the application of a function to a list of arguments
  | Quant Quantifier Sort Term
  -- ^ This is a de-Bruijn indexed quantifier
  | Lambda Sort Term
  -- ^ This is a de-Bruijn indexed lambda-term
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Propositional Implementation
---------------------------------------------------------------------------------------------------
instance Propositional Term where
  toProp =
    \case
      Func FAnd fs -> PAnd $ map toProp fs
      Func FOr fs -> POr $ map toProp fs
      Func FNot [f] -> PNot $ toProp f
            -- TODO: multi imply?
      Func FImply [f, g] -> POr [PNot (toProp f), toProp g]
      Const (CBool c) -> PConst c
      t -> PLit t
    --
  fromProp =
    \case
      PConst c
        | c -> true
        | otherwise -> false
      PAnd fs -> andf $ map fromProp fs
      POr fs -> orf $ map fromProp fs
      PNot f -> neg (fromProp f)
      PLit f -> f

---------------------------------------------------------------------------------------------------
-- Construction
---------------------------------------------------------------------------------------------------
-- | Construct generic constant.
constT :: Constant -> Term
constT = Const

-- | Construct simple variable with given name and sort.
var :: Symbol -> Sort -> Term
var = Var

-- | Construct generic function.
func :: Function -> [Term] -> Term
func = Func

-- | Construct equality.
equal :: Term -> Term -> Term
equal (Const (CInt a)) (Const (CInt b)) = boolConst (a == b)
equal (Const (CInt a)) (Const (CReal b)) = boolConst ((a % 1) == b)
equal (Const (CReal a)) (Const (CInt b)) = boolConst (a == (b % 1))
equal (Const (CReal a)) (Const (CReal b)) = boolConst (a == b)
equal a b = func FEq [a, b]

-- | Construct universal quantification for the variables listed, if they are free.
forAll :: [Symbol] -> Term -> Term
forAll vars f = quantifyL (bindings f !?) Forall f vars

-- | Construct existential quantification for the variables listed, if they are free.
exists :: [Symbol] -> Term -> Term
exists vars f = quantifyL (bindings f !?) Exists f vars

-- | Construct lambda term.
lambda :: Symbol -> Sort -> Term -> Term
lambda v s t = Lambda s (quantify v t)

quantifyL :: (Symbol -> Maybe Sort) -> Quantifier -> Term -> [Symbol] -> Term
quantifyL types q f =
  \case
    [] -> f
    v:vr ->
      case types v of
        Nothing -> quantifyL types q f vr
        Just t -> Quant q t (quantify v (quantifyL types q f vr))

quantify :: Symbol -> Term -> Term
quantify var = quant 0
  where
    quant n =
      \case
        Var v t
          | v == var -> QVar n
          | otherwise -> Var v t
        Quant q b f -> Quant q b (quant (n + 1) f)
        Lambda t f -> Lambda t (quant (n + 1) f)
        Func f fs -> Func f (quant n <$> fs)
        QVar v -> QVar v
        Const c -> Const c

-- | Construct an uninterpreted function term with simple variables as arguments, i.e.
-- terms of the from "foo (a, b, c)" where "a" , "b", "c" are variable names.
unintFunc :: String -> Sort -> [(Symbol, Sort)] -> Term
unintFunc name resSort args = Func (CustomF name (map snd args) resSort) $ map (uncurry Var) args

---------------------------------------------------------------------------------------------------
-- | Construct the boolean constant true.
true :: Term
true = Const (CBool True)

-- | Construct the boolean constant false.
false :: Term
false = Const (CBool False)

-- | Construct a boolean constant.
boolConst :: Bool -> Term
boolConst = constT . CBool

-- | Construct variable with boolean sort.
bvarT :: String -> Term
bvarT name = Var name SBool

-- | Construct a boolean conjunction.
andf :: [Term] -> Term
andf xs
  | false `elem` xs = false
  | otherwise =
    case go xs of
      [] -> true
      [x] -> x
      xs -> func FAnd xs
  where
    go =
      \case
        [] -> []
        Const (CBool True):xr -> go xr
        Func FAnd xs:ys -> go $ xs ++ ys
        t:xr -> t : go xr

-- | Generator to construct a boolean conjunction.
andfL :: [a] -> (a -> Term) -> Term
andfL xs f = andf $ map f xs

-- | Construct a boolean disjunction.
orf :: [Term] -> Term
orf xs
  | true `elem` xs = true
  | otherwise =
    case filter (/= false) xs of
      [] -> false
      [x] -> x
      xs -> Func FOr xs

-- | Generator to construct a boolean disjunction.
orfL :: [a] -> (a -> Term) -> Term
orfL xs f = orf $ map f xs

-- | Construct a boolean negation.
neg :: Term -> Term
neg =
  \case
    Const (CBool True) -> false
    Const (CBool False) -> true
    Func FNot [f] -> f
    Func FLt [f, g] -> geqT f g
    Func FLte [f, g] -> gtT f g
    f -> Func FNot [f]

-- | Construct a boolean implication.
impl :: Term -> Term -> Term
impl f g = orf [neg f, g]

-- | Construct a syntactic boolean implication.
implyT :: Term -> Term -> Term
implyT a b = func FImply [a, b]

-- | Construct a boolean equivalence.
iff :: Term -> Term -> Term
iff f g = andf [impl f g, impl g f]

-- | Construct a boolean exclusive-or.
xor :: Term -> Term -> Term
xor f g = neg (iff f g)

-- | Construct an term that holds if exactly one sub-term is true.
exactlyOne :: [Term] -> Term
exactlyOne fs = andf (orf fs : map (\f -> f `impl` andf [neg g | g <- fs, g /= f]) fs)

-- | Construct a term that is true if at most one of its sub-terms are true.
atMostOne :: [Term] -> Term
atMostOne fs = geqT oneT $ func FAdd $ map (\f -> ite f oneT zeroT) fs

-- | Construct an if-then-else term.
ite :: Term -> Term -> Term -> Term
ite c t e
  | t == e = t
  | otherwise = Func FIte [c, t, e]

-- | Construct a distinct term, i.e. the term that is true if
-- all sub-terms are different.
distinct :: [Term] -> Term
distinct = Func FDistinct

---------------------------------------------------------------------------------------------------
-- | Construct an integer constant.
intConst :: Integer -> Term
intConst = constT . CInt

-- | Construct an real-valued constant.
realConst :: Rational -> Term
realConst = constT . CReal

-- | Construct an number constant in a polymorphic manner. Integer constants are
-- constructed if possible.
numberT :: Real a => a -> Term
numberT num =
  let r = toRational num
   in if denominator r == 1
        then Const (CInt (numerator r))
        else Const (CReal r)

-- | Construct the integer zero constant.
zeroT :: Term
zeroT = Const (CInt 0)

-- | Construct the integer one constant.
oneT :: Term
oneT = Const (CInt 1)

-- | Construct an integer sorted variable.
ivarT :: String -> Term
ivarT name = Var name SInt

-- | Construct an real sorted variable.
rvarT :: String -> Term
rvarT name = Var name SReal

-- | Construct a term to cast an integer sorted-term to a real-sorted term.
toRealT :: Term -> Term
toRealT a = func FToReal [a]

-- | Construct an less-or-equal-than term.
leqT :: Term -> Term -> Term
leqT (Const (CInt a)) (Const (CInt b)) = boolConst (a <= b)
leqT (Const (CInt a)) (Const (CReal b)) = boolConst ((a % 1) <= b)
leqT (Const (CReal a)) (Const (CInt b)) = boolConst (a <= (b % 1))
leqT (Const (CReal a)) (Const (CReal b)) = boolConst (a <= b)
leqT t (Const (CInt n))
  | isInteger t = func FLt [t, Const (CInt (n + 1))]
  | otherwise = func FLte [t, Const (CInt n)]
leqT a b = func FLte [a, b]

-- | Construct an less-than term.
ltT :: Term -> Term -> Term
ltT (Const (CInt a)) (Const (CInt b)) = boolConst (a < b)
ltT (Const (CInt a)) (Const (CReal b)) = boolConst ((a % 1) < b)
ltT (Const (CReal a)) (Const (CInt b)) = boolConst (a < (b % 1))
ltT (Const (CReal a)) (Const (CReal b)) = boolConst (a < b)
ltT (Const (CInt n)) t
  | isInteger t = func FLte [Const (CInt (n + 1)), t]
  | otherwise = func FLt [Const (CInt n), t]
ltT a b = func FLt [a, b]

-- | Construct an greater-or-equal-than term.
geqT :: Term -> Term -> Term
geqT a b = leqT b a

-- | Construct an greater-than term.
gtT :: Term -> Term -> Term
gtT a b = ltT b a

-- | Construct a sum of terms with the neutral element zero.
addT :: [Term] -> Term
addT =
  \case
    [] -> zeroT
    [t] -> t
    ts ->
      case first sumC (filterC (flatten ts)) of
        (c, []) -> Const c
        (CInt 0, [t]) -> t
        (CReal 0, [t]) -> t
        (CInt 0, ts) -> Func FAdd ts
        (CReal 0, ts) -> Func FAdd ts
        (c, ts) -> Func FAdd $ Const c : ts
  where
    flatten [] = []
    flatten (Func FAdd sts:tr) = flatten $ sts ++ tr
    flatten (t:tr) = t : flatten tr

-- | Construct the inversion of a term, where the inversion of t is -t.
invT :: Term -> Term
invT =
  \case
    Const (CInt n) -> Const $ CInt (-n)
    Const (CReal n) -> Const $ CReal (-n)
    Func FAdd ts -> addT $ map invT ts
    Func FMul (t:tr) -> multT $ invT t : tr
    t -> Func FMul [Const (CInt (-1)), t]

-- | Construct the difference of two terms.
subT :: Term -> Term -> Term
subT a b = minusT [a, b]

-- | Construct a generic difference of terms, where all the remaining terms
-- are subtracted from the first one. 'undefined' if the list is empty.
minusT :: [Term] -> Term
minusT =
  \case
    [] -> error "assert: empty minus"
    [x] -> invT x
    x:xr -> addT (x : map invT xr)

-- | Construct the product of terms with the neutral element one.
multT :: [Term] -> Term
multT =
  \case
    [] -> oneT
    [t] -> t
    ts ->
      case first multC (filterC (flatten ts)) of
        (c, []) -> Const c
        (CInt 1, [t]) -> t
        (CReal 1, [t]) -> t
        (CInt 1, ts) -> Func FMul ts
        (CReal 1, ts) -> Func FMul ts
        (CInt 0, _) -> zeroT
        (CReal 0, _) -> zeroT
        (c, ts) -> Func FMul $ Const c : ts
  where
    flatten [] = []
    flatten (Func FMul sts:tr) = flatten $ sts ++ tr
    flatten (t:tr) = t : flatten tr

filterC :: [Term] -> ([Constant], [Term])
filterC =
  \case
    [] -> ([], [])
    Const c:ts -> first (c :) $ filterC ts
    t:ts -> second (t :) $ filterC ts

sumC :: [Constant] -> Constant
sumC = foldl go (CInt 0)
  where
    go (CInt m) (CInt n) = CInt $ m + n
    go (CReal m) (CReal n) = CReal $ m + n
    go (CInt m) (CReal n) = CReal $ (m % 1) + n
    go (CReal m) (CInt n) = CReal $ m + (n % 1)
    go _ _ = error "assert: can only sum integers and reals"

multC :: [Constant] -> Constant
multC = foldl go (CInt 1)
  where
    go (CInt m) (CInt n) = CInt $ m * n
    go (CReal m) (CReal n) = CReal $ m * n
    go (CInt m) (CReal n) = CReal $ (m % 1) * n
    go (CReal m) (CInt n) = CReal $ m * (n % 1)
    go _ _ = error "assert: can only sum integers and reals"

-- | Construct the integer-division of two terms.
intdivT :: Term -> Term -> Term
intdivT a b = func FDivInt [a, b]

-- | Construct the modulo of the integer-division of two terms.
modT :: Term -> Term -> Term
modT a b = func FMod [a, b]

-- | Construct the real-value division of two terms.
realdivT :: Term -> Term -> Term
realdivT (Const (CReal a)) (Const (CReal b)) = Const $ CReal (a / b)
realdivT a b = func FDivReal [a, b]

-- | Construct the absolute value of a term.
absT :: Term -> Term
absT a = func FAbs [a]

-- | Invert a constant by taking the boolean negation or 1 / k for an number k.
-- Is undefined if k is zero.
invertC :: Constant -> Constant
invertC =
  \case
    CBool b -> CBool $ not b
    CReal r -> CReal $ 1 / r
    CInt n
      | n == 1 || n == -1 -> CInt n
      | otherwise -> CReal $ 1 % n

---------------------------------------------------------------------------------------------------
-- Query Methods
---------------------------------------------------------------------------------------------------
isNumericT :: Term -> Bool
isNumericT =
  \case
    Var _ sort -> isNumber sort
    Const (CInt _) -> True
    Const (CReal _) -> True
    Func FIte [_, t, e] -> isNumericT t && isNumericT e
    Func func fs
      | func `elem` [FAdd, FMul, FAbs, FMod, FDivInt, FDivReal, FToReal] -> all isNumericT fs
      | otherwise -> False
    _ -> False

isInteger :: Term -> Bool
isInteger =
  \case
    Var _ SInt -> True
    Const (CInt _) -> True
    Func FAdd fs -> all isInteger fs
    Func FMul fs -> all isInteger fs
    Func FAbs _ -> True
    Func FMod _ -> True
    Func FDivInt _ -> True
    _ -> False

isFuncSort :: Sort -> Bool
isFuncSort =
  \case
    SFunc _ _ -> True
    _ -> False

isNumber :: Sort -> Bool
isNumber = (`elem` [SInt, SReal])

quantifierFree :: Term -> Bool
quantifierFree =
  \case
    Func _ fs -> all quantifierFree fs
    Quant {} -> False
    Lambda _ _ -> False
    _ -> True

ufFree :: Term -> Bool
ufFree =
  \case
    Var _ _ -> True
    Const _ -> True
    QVar _ -> True
    Func (CustomF {}) _ -> False
    Func _ fs -> all ufFree fs
    Quant _ _ f -> ufFree f
    Lambda _ f -> ufFree f

bindingsS :: Term -> Set (Symbol, Sort)
bindingsS =
  \case
    Var v s -> Set.singleton (v, s)
    Func f args ->
      case f of
        CustomF f sarg starg ->
          Set.unions (Set.singleton (f, SFunc sarg starg) : map bindingsS args)
        _ -> Set.unions (map bindingsS args)
    Quant _ _ f -> bindingsS f
    Lambda _ f -> bindingsS f
    _ -> Set.empty

sorts :: Term -> Set Sort
sorts =
  \case
    Var _ s -> Set.singleton s
    Func f args ->
      case f of
        CustomF _ sarg starg -> Set.fromList (starg : sarg) `Set.union` Set.unions (map sorts args)
        _ -> Set.unions $ map sorts args
    Quant _ s f -> Set.singleton s `Set.union` sorts f
    Lambda _ f -> sorts f
    _ -> Set.empty

frees :: Term -> Set Symbol
frees = Set.map fst . Set.filter (not . isFuncSort . snd) . bindingsS

decls :: Term -> Set Symbol
decls = Set.map fst . bindingsS

bindings :: Term -> Map Symbol Sort
bindings =
  Map.fromListWithKey
    (\v s s' ->
       if s == s'
         then s
         else error ("Assertion: Found variable " ++ v ++ " with different sorts"))
    . Set.toList
    . bindingsS

symbols :: Term -> Set Symbol
symbols =
  \case
    Var s _ -> Set.singleton s
    Func (CustomF f _ _) args -> Set.unions $ Set.singleton f : map symbols args
    Func _ args -> Set.unions $ map symbols args
    Quant _ _ f -> symbols f
    Lambda _ f -> symbols f
    _ -> Set.empty

nonBoolTerms :: Term -> Set Term
nonBoolTerms =
  \case
    Const (CBool _) -> Set.empty
    Func f args
      | f `elem` booleanFunctions -> Set.unions $ map nonBoolTerms args
      | otherwise -> Set.singleton $ Func f args
    f -> Set.singleton f

---------------------------------------------------------------------------------------------------
-- Models
---------------------------------------------------------------------------------------------------
-- | Representation of a model for the free variables in a 'Term'
newtype Model =
  Model (Map Symbol Term)
  deriving (Eq, Ord, Show)

modelToMap :: Model -> Map Symbol Term
modelToMap (Model m) = m

emptyModel :: Model
emptyModel = Model Map.empty

modelAddT :: Symbol -> Term -> Model -> Model
modelAddT v t (Model m) = Model $ Map.insert v t m

setModel :: Model -> Term -> Term
setModel (Model m) = mapTermM m

inlineModel :: Model -> Symbol -> Model
inlineModel (Model m) v =
  case m !? v of
    Nothing -> Model m
    Just t ->
      Model
        $ mapTerm
            (\v' _ ->
               if v == v'
                 then Just t
                 else Nothing)
            <$> Map.delete v m

sanitizeModel :: Set Symbol -> Model -> Model
sanitizeModel frees (Model m) = foldl inlineModel (Model m) (Map.keysSet m `Set.difference` frees)

---------------------------------------------------------------------------------------------------
betaReduce :: Term -> Term -> Term
betaReduce func arg =
  case func of
    Lambda _ body -> red 0 body
    _ -> error "Beta reduction only works on lambda expressions"
  where
    red :: Int -> Term -> Term
    red d =
      \case
        Var v s -> Var v s
        Const c -> Const c
        QVar k
          | d == k -> arg
          | k > d -> QVar k -- This is necessary as the lambda is removed!
          | otherwise -> QVar k
        Func f args -> Func f (map (red d) args)
        Quant q s t -> Quant q s (red (d + 1) t)
        Lambda s t -> Lambda s (red (d + 1) t)

mapTermFor :: Symbol -> Term -> Term -> Term
mapTermFor var term =
  mapTerm $ \v _ ->
    if v == var
      then Just term
      else Nothing

mapTerm :: (Symbol -> Sort -> Maybe Term) -> Term -> Term
mapTerm m =
  \case
    Var v t ->
      case m v t of
        Just term -> term
        Nothing -> Var v t
    Func f args ->
      case (f, map (mapTerm m) args) of
        (CustomF v sargs starg, args) ->
          case m v (SFunc sargs starg) of
            Nothing -> Func f args
            Just funInst -> foldl betaReduce funInst args
        (FAnd, fs) -> andf fs
        (FOr, fs) -> orf fs
        (FNot, [f]) -> neg f
        (FDistinct, fs) -> distinct fs
        (FImply, [a, b]) -> implyT a b
        (FIte, [a, b, c]) -> ite a b c
        (FAdd, fs) -> addT fs
        (FMul, fs) -> multT fs
        (FDivReal, [a, b]) -> realdivT a b
        (FEq, [a, b]) -> a `equal` b
        (FLt, [a, b]) -> a `ltT` b
        (FLte, [a, b]) -> a `leqT` b
        (FAbs, [t]) -> absT t
        (FToReal, [t]) -> toRealT t
        (FMod, [a, b]) -> modT a b
        (FDivInt, [a, b]) -> intdivT a b
        (f, args) -> Func f args
    Quant q t f -> Quant q t (mapTerm m f)
    Lambda t f -> Lambda t (mapTerm m f)
    QVar n -> QVar n
    Const c -> Const c

mapTermM :: Map Symbol Term -> Term -> Term
mapTermM m = mapTerm (\v _ -> m !? v)

mapSymbol :: (Symbol -> Symbol) -> Term -> Term
mapSymbol m = rec
  where
    rec =
      \case
        Var v t -> Var (m v) t
        Func (CustomF f sig term) args -> Func (CustomF (m f) sig term) (rec <$> args)
        Func f args -> Func f (rec <$> args)
        Quant q t f -> Quant q t (rec f)
        Lambda t f -> Lambda t (rec f)
        QVar n -> QVar n
        Const c -> Const c

setTerm :: Term -> Bool -> Term -> Term
setTerm targ val = go
  where
    go f
      | targ == f && val = true
      | targ == f && not val = false
      | otherwise =
        case f of
          Func FAnd fs -> andf (map go fs)
          Func FOr fs -> orf (map go fs)
          Func FNot [f] -> neg (go f)
          Func FImply [f, g] -> go f `impl` go g
          Func FDistinct fs -> distinct (map go fs)
          _ -> f

setSymbolTo :: Symbol -> Term -> Term -> Term
setSymbolTo var term =
  mapTerm $ \var' _ ->
    if var == var'
      then Just term
      else Nothing

replaceUF :: Symbol -> [Symbol] -> Term -> Term -> Term
replaceUF name argVars body = go
  where
    go =
      \case
        Quant q t f -> Quant q t (go f)
        Lambda t f -> Lambda t (go f)
        Func fun args ->
          case fun of
            CustomF n _ _
              | n == name -> mapTermM (Map.fromList (zip argVars args)) body
              | otherwise -> Func fun $ map go args
            _ ->
              case (fun, map go args) of
                (FAnd, fs) -> andf fs
                (FOr, fs) -> orf fs
                (FNot, [f]) -> neg f
                (FDistinct, fs) -> distinct fs
                (FImply, [a, b]) -> implyT a b
                (FIte, [a, b, c]) -> ite a b c
                (FAdd, fs) -> addT fs
                (FMul, fs) -> multT fs
                (FDivReal, [a, b]) -> realdivT a b
                (FEq, [a, b]) -> a `equal` b
                (FLt, [a, b]) -> a `ltT` b
                (FLte, [a, b]) -> a `leqT` b
                (FAbs, [t]) -> absT t
                (FToReal, [t]) -> toRealT t
                (FMod, [a, b]) -> modT a b
                (FDivInt, [a, b]) -> intdivT a b
                (f, args) -> Func f args
        QVar k -> QVar k
        Const c -> Const c
        Var v t -> Var v t

---------------------------------------------------------------------------------------------------
uniqueName :: Symbol -> Set Symbol -> Symbol
uniqueName = uniquePrefix

uniquePrefix :: Symbol -> Set Symbol -> Symbol
uniquePrefix prefix names
  | any (prefix `isPrefixOf`) names = h (0 :: Integer)
  | otherwise = prefix
  where
    h n
      | any ((prefix ++ show n) `isPrefixOf`) names = h (n + 1)
      | otherwise = prefix ++ show n

unusedName :: Symbol -> Term -> Symbol
unusedName prefix f = uniqueName prefix (symbols f)

unusedPrefix :: Symbol -> Term -> Symbol
unusedPrefix prefix f = uniquePrefix prefix (symbols f)

removePref :: Symbol -> Term -> Term
removePref pref =
  mapSymbol $ \v ->
    if pref `isPrefixOf` v
      then drop (length pref) v
      else v

---------------------------------------------------------------------------------------------------
-- Transformations
---------------------------------------------------------------------------------------------------
-- | Move down quantifiers if possible.
pushdownQE :: Term -> Term
pushdownQE = removeDangling . go
  where
    go =
      \case
        Quant q s t ->
          case (q, go t) of
            (Forall, Func FAnd args) -> andf $ map (go . Quant q s) args
            (Exists, Func FOr args) -> orf $ map (go . Quant q s) args
            (Forall, Func FNot [arg]) -> neg $ go $ Quant Exists s arg
            (Exists, Func FNot [arg]) -> neg $ go $ Quant Forall s arg
            (q, t) -> Quant q s t
        Func f args -> Func f (map go args)
        term -> term

-- | Remove dangling quantifiers.
removeDangling :: Term -> Term
removeDangling = fst . go
  where
    go =
      \case
        Var s n -> (Var s n, Set.empty)
        Const c -> (Const c, Set.empty)
        QVar k -> (QVar k, Set.singleton k)
        Func f fs -> bimap (Func f) Set.unions $ unzip $ map go fs
        Lambda s t -> bimap (Lambda s) (Set.map (\k -> k - 1)) $ go t
        Quant q s t ->
          let (t', indices) = go t
           in if 0 `elem` indices
                then (Quant q s t', Set.map (\k -> k - 1) indices)
                else (adapt 0 t', indices)
    adapt k =
      \case
        Var s n -> Var s n
        Const c -> Const c
        QVar k'
          | k == k' -> error "assert: this should not happen at all"
          | k' > k -> QVar (k' - 1)
          | otherwise -> QVar k'
        Func f fs -> Func f (map (adapt k) fs)
        Lambda s t -> Lambda s (adapt (k + 1) t)
        Quant q s t -> Quant q s (adapt (k + 1) t)

-- TODO: implement
--typeCheck :: Term -> Either String Sort
--typeCheck = go (const Nothing)
--    where
--        go varType = \case
--            Var _ sort -> Right sort -- TODO: check also consitency of type
--            Const (CInt _) -> Right SInt
--            Const (CReal _) -> Right SReal
--            Const (CBool _) -> Right SBool
--            QVar n -> case varType n of
--                            Nothing -> Left "found unmapped quantified variable"
--                            Just sort -> Right sort
--            Quant _ sort term -> go (\n -> if n == 0 then Just sort else varType (n - 1)) term
--            Lambda sort term -> error "TODO IMPLEMENT"
--            Func func args ->
--                case (func, map (go varType) args) of
--                    (CustomF _ argSort resSort, args)
--                        | argSort == args -> Right resSort
--                        | otherwise -> Left "sorts do not match function application"
--                    (FAnd, args) -> boolOp args
--                    (FOr, args) -> boolOp args
--                    (FDistinct, args) -> boolOp args
--                    (FNot, [SBool]) -> Right SBool
--                    (FNot, _) -> Left "illegal usage of 'not'"
--                    _ -> error "TODO IMPLEMENT"
--        boolOp args
--         | all (==SBool) args = Right SBool
--         | otherwise = Left "TODO: Proper error"
--
--
-- Pre-Simplification / Pre-Simplification check
--
-- TODO: move to different module
underapproxSAT :: Term -> Bool
underapproxSAT = go . normNNF
  where
    go =
      \case
        Const (CBool b) -> b
        Func FOr fs -> any go fs
        Func FAnd [] -> True
        Func FAnd (Const (CBool True):tr) -> go $ Func FAnd tr
        Func FAnd (f:fr) ->
          let rec = Func FAnd fr
           in case f of
                Func comp [Var v _, Const c]
                  | comp `elem` [FEq, FLte] -> go $ setSymbolTo v (Const c) rec
                  | comp == FLt -> go $ setSymbolTo v (minusT [Const c, Const (CInt 1)]) rec
                Func comp [Const c, Var v _]
                  | comp `elem` [FEq, FLte] -> go $ setSymbolTo v (Const c) rec
                  | comp == FLt -> go $ setSymbolTo v (addT [Const c, Const (CInt 1)]) rec
                Func FNot [Func FEq [Var v s, Const c]]
                  | isNumber s -> go $ setSymbolTo v (addT [Const c, Const (CInt 1)]) rec
                  | s == SBool -> go $ setSymbolTo v (neg (Const c)) rec
                  | otherwise -> False
                Func FNot [Func FEq [Const c, Var v s]]
                  | isNumber s -> go $ setSymbolTo v (addT [Const c, Const (CInt 1)]) rec
                  | s == SBool -> go $ setSymbolTo v (neg (Const c)) rec
                  | otherwise -> False
                _ -> False
        Func comp [Var v1 _, Var v2 _]
          | v1 == v2 -> comp == FEq
          | otherwise -> comp `elem` [FEq, FLt, FLte]
        Func FNot [Func FEq [Var v1 _, Var v2 _]] -> v1 /= v2
        f -> go $ Func FAnd [f]
---------------------------------------------------------------------------------------------------
