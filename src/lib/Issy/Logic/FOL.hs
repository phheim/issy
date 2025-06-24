-------------------------------------------------------------------------------
-- | 
-- Module       :   FOL
--
-- 'FOL' provides a simple interface for using FOL terms.
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Logic.FOL
  ( Symbol
  , Function(..)
  , Term(..)
  , Sort(..)
  , Quantifier(..)
  , Constant(..)
  , predefined
  , booleanFunctions
  , comparisionFunctions
  , --
    Model
  , modelToMap
  , emptyModel
  , modelAddT
  , sanitizeModel
  , setModel
  , mapTerm
  , mapTermM
  , mapSymbol
  , setTerm
  , replaceUF
  , removePref
  , --
    forAll
  , exists
  , lambda
  , true
  , false
  , andf
  , andfL
  , orf
  , orfL
  , neg
  , impl
  , iff
  , xor
  , ite
  , distinct
  , exactlyOne
  , atMostOne
  , var
  , constT
  , boolConst
  , intConst
  , realConst
  , bvarT
  , ivarT
  , rvarT
  , zeroT
  , oneT
  , func
  , unintFunc
  , leqT
  , geqT
  , ltT
  , gtT
  , equal
  , addT
  , subT
  , invT
  , isNumber
  , --
    bindings
  , frees
  , sorts
  , decls
  , quantifierFree
  , ufFree
  , symbols
  , nonBoolTerms
  , equalitiesFor
  , --
    uniqueName
  , uniquePrefix
  , unusedName
  , unusedPrefix
  , --
    toNNF
  , pushdownQE
  ) where

-------------------------------------------------------------------------------
import Data.List (isPrefixOf)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-------------------------------------------------------------------------------
type Symbol = String

data Sort
  = SBool
  | SInt
  | SReal
  | SFunc [Sort] Sort
  deriving (Eq, Ord, Show)

isFuncSort :: Sort -> Bool
isFuncSort =
  \case
    SFunc _ _ -> True
    _ -> False

data Function
  = CustomF Symbol [Sort] Sort
  -- Boolean functions
  | FAnd
  | FOr
  | FNot
  | FDistinct
  | FImply
  -- Arithmetic operators
  | FIte
  | FAdd
  | FSub
  | FMul
  | FDivReal
  | FEq
  | FLt
  | FGt
  | FLte
  | FGte
  | FAbs
  | FToReal
  | FMod
  | FDivInt
  deriving (Eq, Ord, Show)

booleanFunctions :: [Function]
booleanFunctions = [FAnd, FOr, FNot, FDistinct, FImply]

comparisionFunctions :: [Function]
comparisionFunctions = [FEq, FLt, FLte, FGt, FGte]

predefined :: [Function]
predefined =
  booleanFunctions
    ++ [FIte, FAdd, FSub, FMul, FDivReal, FEq, FLt, FGt, FLte, FGte, FAbs, FToReal, FMod, FDivInt]

data Quantifier
  = Exists
  | Forall
  deriving (Eq, Ord, Show)

data Constant
  = CInt Integer
  -- ^ 'IntConst' is an integer constant
  | CReal Rational
  -- ^ 'RealConst' is an real constant
  | CBool Bool
  -- ^ 'BoolConst' is a bool constant
  deriving (Eq, Ord, Show)

data Term
  = Var Symbol Sort
  -- ^ 'Var' is a constant variable symbols that is quantified on top-level. 
  -- If not stated otherwise, a solver might assume that it is existentially 
  -- quantified.
  | Const Constant
  -- ^ 'Const' is a constant expression
  | QVar Int
  -- ^ 'QVar' is a quantified variable that is index with de-Bruijn indexing
  | Func Function [Term]
  -- ^ 'Func' represents the application of a function to a list of arguments
  | Quant Quantifier Sort Term
  -- ^ 'Quant' is a de-Bruijn indexed quantifier 
  | Lambda Sort Term
  -- ^ 'Lambda' is a de-Bruijn indexed lambda-term
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
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

mapTerm :: (Symbol -> Sort -> Maybe Term) -> Term -> Term
mapTerm m =
  \case
    Var v t ->
      case m v t of
        Just term -> term
        Nothing -> Var v t
    Func f args ->
      let margs = map (mapTerm m) args
       in case f of
            CustomF v sargs starg ->
              case m v (SFunc sargs starg) of
                Nothing -> Func f margs
                Just funInst -> foldl betaReduce funInst margs
            _ -> Func f margs
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
            _ -> Func fun $ map go args
        QVar k -> QVar k
        Const c -> Const c
        Var v t -> Var v t

-------------------------------------------------------------------------------
true :: Term
true = Const (CBool True)

false :: Term
false = Const (CBool False)

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

andfL :: [a] -> (a -> Term) -> Term
andfL xs f = andf $ map f xs

orf :: [Term] -> Term
orf xs
  | true `elem` xs = true
  | otherwise =
    case filter (/= false) xs of
      [] -> false
      [x] -> x
      xs -> Func FOr xs

orfL :: [a] -> (a -> Term) -> Term
orfL xs f = orf $ map f xs

neg :: Term -> Term
neg =
  \case
    Const (CBool True) -> false
    Const (CBool False) -> true
    Func FNot [f] -> f
    f -> Func FNot [f]

ite :: Term -> Term -> Term -> Term
ite c t e
  | t == e = t
  | otherwise = Func FIte [c, t, e]

impl :: Term -> Term -> Term
impl f g = orf [neg f, g]

iff :: Term -> Term -> Term
iff f g = andf [impl f g, impl g f]

xor :: Term -> Term -> Term
xor f g = neg (iff f g)

distinct :: [Term] -> Term
distinct = Func FDistinct

exactlyOne :: [Term] -> Term
exactlyOne fs = andf (orf fs : map (\f -> f `impl` andf [neg g | g <- fs, g /= f]) fs)

atMostOne :: [Term] -> Term
atMostOne fs = geqT oneT $ func FAdd $ map (\f -> ite f oneT zeroT) fs

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

quantifyL :: (Symbol -> Maybe Sort) -> Quantifier -> Term -> [Symbol] -> Term
quantifyL types q f =
  \case
    [] -> f
    v:vr ->
      case types v of
        Nothing -> quantifyL types q f vr
        Just t -> Quant q t (quantify v (quantifyL types q f vr))

forAll :: [Symbol] -> Term -> Term
forAll vars f = quantifyL (bindings f !?) Forall f vars

exists :: [Symbol] -> Term -> Term
exists vars f = quantifyL (bindings f !?) Exists f vars

lambda :: Symbol -> Sort -> Term -> Term
lambda v s t = Lambda s (quantify v t)

-------------------------------------------------------------------------------
quantifierFree :: Term -> Bool
quantifierFree =
  \case
    Func _ fs -> all quantifierFree fs
    Quant {} -> False
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

equalitiesFor :: Symbol -> Term -> Set Term
equalitiesFor var = go
  where
    go =
      \case
        Func FEq [Var v _, t]
          | v == var -> Set.singleton t
          | otherwise -> go t
        Func FEq [t, Var v _]
          | v == var -> Set.singleton t
          | otherwise -> go t
        Func _ args -> Set.unions $ map go args
        Quant _ _ f -> go f
        Lambda _ f -> go f
        _ -> Set.empty

-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
var :: Symbol -> Sort -> Term
var = Var

constT :: Constant -> Term
constT = Const

boolConst :: Bool -> Term
boolConst = constT . CBool

intConst :: Integer -> Term
intConst = constT . CInt

realConst :: Rational -> Term
realConst = constT . CReal

-- More constructors
bvarT :: String -> Term
bvarT name = Var name SBool

ivarT :: String -> Term
ivarT name = Var name SInt

rvarT :: String -> Term
rvarT name = Var name SReal

zeroT :: Term
zeroT = Const (CInt 0)

oneT :: Term
oneT = Const (CInt 1)

func :: Function -> [Term] -> Term
func = Func

unintFunc :: String -> Sort -> [(Symbol, Sort)] -> Term
unintFunc name resSort args = Func (CustomF name (map snd args) resSort) $ map (uncurry Var) args

leqT :: Term -> Term -> Term
leqT a b = func FLte [a, b]

geqT :: Term -> Term -> Term
geqT a b = func FGte [a, b]

gtT :: Term -> Term -> Term
gtT a b = func FGt [a, b]

ltT :: Term -> Term -> Term
ltT a b = func FLt [a, b]

equal :: Term -> Term -> Term
equal a b = func FEq [a, b]

addT :: [Term] -> Term
addT =
  \case
    [] -> zeroT
    [t] -> t
    ts -> func FAdd ts

subT :: Term -> Term -> Term
subT a b = func FSub [a, b]

invT :: Term -> Term
invT a = func FSub [a]

isNumber :: Sort -> Bool
isNumber = (`elem` [SInt, SReal])

---
-- Translation to NNF
---
toNNF :: Term -> Term
toNNF =
  \case
    Func FNot [Quant Forall s t] -> Quant Exists s $ toNNF $ neg t
    Func FNot [Quant Exists s t] -> Quant Forall s $ toNNF $ neg t
    Func FNot [Func FNot [t]] -> toNNF t
    Func FNot [Func FOr args] -> andf $ map (toNNF . neg) args
    Func FNot [Func FAnd args] -> orf $ map (toNNF . neg) args
    Func f args -> Func f $ map toNNF args
    Quant q s t -> Quant q s $ toNNF t
    atom -> atom

--
-- Custom simplifications
--
-- TODO: remove dangling quantifiers after pushdown
pushdownQE :: Term -> Term
pushdownQE =
  \case
    Quant q s t ->
      case (q, pushdownQE t) of
        (Forall, Func FAnd args) -> andf $ map (Quant q s) args
        (Exists, Func FOr args) -> orf $ map (Quant q s) args
        (q, t) -> Quant q s t
    Func f args -> Func f (map pushdownQE args)
    term -> term
