---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Logic.Polyhedra
-- Description : Operations and represenations for polyhedra-like representations
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase, MultiWayIf #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Polyhedra
  ( Polyhedron
  , Ineq
  , ineqToTerm
  , sumTerm
  , toIneqs
  , normalize
  , normalizeFast
  , toTerms
  , nontrivialPolyhedra
  ) where

---------------------------------------------------------------------------------------------------
import Data.Bifunctor (first, second)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Ratio ((%), denominator, numerator)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL
  ( Constant(CInt, CReal)
  , Function(FAdd, FEq, FLt, FLte, FMul)
  , Sort
  , Symbol
  , Term(Const, Func, Var)
  )
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.Interval
import Issy.Logic.Propositional (NNF(..), toNNF)

---------------------------------------------------------------------------------------------------
-- Efficient Maps for Lists
---------------------------------------------------------------------------------------------------
-- | 'ListTree' is a prefix tree to efficiently use lists as keys of a map
data ListTree k a
  = LTLeaf
  -- ^ 'LTLeaf' is a dead end and corresponds to Map.empty  
  | LTNode (Maybe a) (Map k (ListTree k a))
  -- ^ 'LTNode' is a leaf in the prefix tree. For 'LTNode melem subs' 
  -- - if (melem == Just elem) then [] is mapped to elem
  -- - for every '(x, tree)' in 'subs', this node maps 'x:xr' to 'e' if 'tree' maps 'xr' to 'e'
  deriving (Eq, Show)

-- | TODO document
filterT :: Ord k => (a -> Bool) -> ListTree k a -> ListTree k a
filterT p = go
  where
    go =
      \case
        LTLeaf -> LTLeaf
        LTNode elem succs -> reduce $ LTNode (goElem elem) (goMP succs)
  --
    reduce (LTNode Nothing mp)
      | Map.null mp = LTLeaf
      | otherwise = LTNode Nothing mp
    reduce tree = tree
    goElem Nothing = Nothing
    goElem (Just elem)
      | p elem = Just elem
      | otherwise = Nothing
    goMP = Map.fromList . rmLeafs . map (second go) . Map.toList
  --
    rmLeafs [] = []
    rmLeafs ((_, LTLeaf):mr) = rmLeafs mr
    rmLeafs (st:mr) = st : rmLeafs mr

-- | TODO document
toListT :: ListTree k a -> [([k], a)]
toListT = go []
  where
    go _ LTLeaf = []
    go acc (LTNode val succs) =
      let rec = concatMap (\(k, succ) -> go (k : acc) succ) $ Map.toList succs
       in case val of
            Nothing -> rec
            Just val -> (reverse acc, val) : rec

-- | TODO document
insertWithT :: Ord k => (a -> a -> Maybe a) -> [k] -> a -> ListTree k a -> Maybe (ListTree k a)
insertWithT comb ks val tree = go tree ks
  where
    go LTLeaf [] = Just $ LTNode (Just val) Map.empty
    go LTLeaf (k:kr) = LTNode Nothing . Map.singleton k <$> go LTLeaf kr
    go (LTNode Nothing succs) [] = Just $ LTNode (Just val) succs
    go (LTNode (Just old) succs) [] = flip LTNode succs . Just <$> comb val old
    go (LTNode label succs) (k:kr) =
      case succs !? k of
        Nothing -> LTNode label . flip (Map.insert k) succs <$> go LTLeaf kr
        Just tree -> LTNode label . flip (Map.insert k) succs <$> go tree kr

-- | TODO
includedLT :: Ord k => (a -> a -> Bool) -> ListTree k a -> ListTree k a -> Bool
includedLT includedElems = go
  where
    go _ LTLeaf = True
    go LTLeaf _ = False
    go (LTNode l1 succ1) (LTNode l2 succ2) =
      let labelInc =
            case (l1, l2) of
              (_, Nothing) -> True
              (Nothing, _) -> False
              (Just l1, Just l2) -> includedElems l1 l2
          succInc =
            all
              (\(k, succ2) ->
                 case succ1 !? k of
                   Nothing -> False
                   Just succ1 -> go succ1 succ2)
              $ Map.toList succ2
       in labelInc && succInc

data MergeRes a
  = MergeFail
  | MergeId
  | Merged a

instance Functor MergeRes where
  fmap _ MergeFail = MergeFail
  fmap _ MergeId = MergeId
  fmap m (Merged a) = Merged (m a)

mergeOnceT ::
     (Ord k, Eq a) => (a -> a -> Maybe a) -> ListTree k a -> ListTree k a -> Maybe (ListTree k a)
mergeOnceT merge t1 t2 =
  case goT t1 t2 of
    MergeFail -> Nothing
    MergeId -> Just t1
    Merged t -> Just t
  where
    goT LTLeaf LTLeaf = MergeId
    goT (LTNode Nothing sc1) (LTNode Nothing sc2) = LTNode Nothing <$> goSM sc1 sc2
    goT (LTNode (Just l1) sc1) (LTNode (Just l2) sc2) =
      if l1 == l2
        then LTNode (Just l1) <$> goSM sc1 sc2
        else case merge l1 l2 of
               Nothing -> MergeFail
               Just lm
                 | sc1 == sc2 -> Merged $ LTNode (Just lm) sc1
                 | otherwise -> MergeFail
    goT _ _ = MergeFail
        --
    goSM s1 s2 = Map.fromList <$> goS (Map.toList s1) (Map.toList s2)
        -- 
    goS [] [] = MergeId
    goS ((k1, lt1):sr1) ((k2, lt2):sr2)
      | k1 == k2 =
        case goT lt1 lt2 of
          MergeFail -> MergeFail
          MergeId -> ((k1, lt1) :) <$> goS sr1 sr2
          Merged lt
            | sr1 == sr2 -> Merged $ (k1, lt) : sr1
            | otherwise -> MergeFail
      | otherwise = MergeFail
    goS _ _ = MergeFail

---------------------------------------------------------------------------------------------------
-- Polyhedra
---------------------------------------------------------------------------------------------------
-- | TODO document
data Polyhedron = Polyhedron
  { varOrder :: [(Symbol, Sort)]
    -- | TODO use map instead, this is more usable
  , linearConstraints :: ListTree Integer Interval
    -- | TODO: this FOR SURE needs a semantic definition
  } deriving (Show)

-- | 'fullP' generate the 'Polyhedron' that includes the entire space of
fullP :: [(Symbol, Sort)] -> Polyhedron
fullP vorder = Polyhedron {varOrder = vorder, linearConstraints = LTLeaf}

-- | TODO document
isFullP :: Polyhedron -> Bool
isFullP poly =
  case linearConstraints poly of
    LTLeaf -> True
    _ -> False

-- | TODO assumption same varOrder!
includedP :: Polyhedron -> Polyhedron -> Bool
includedP p1 p2 = includedLT included (linearConstraints p1) (linearConstraints p2)

-- | TODO document
rescale :: [Rational] -> ([Integer], Rational)
rescale [] = ([], 1)
rescale (0:xr) = first (0 :) $ rescale xr
rescale (x:xr) =
  let norm = 1 : map (/ x) xr
      (upscaled, factor) = upscale norm
   in (upscaled, toRational factor / x)
  where
    upscale :: [Rational] -> ([Integer], Integer)
    upscale rs =
      let factor = lcms (map denominator rs)
       in (map (numerator . (* toRational factor)) rs, factor)
    --
    lcms [] = 1
    lcms [x] = x
    lcms (1:xr) = lcms xr
    lcms (x:xr) = lcm x $ lcms xr

-- | TODO document
addLinearConstr :: [Rational] -> Interval -> Polyhedron -> Maybe Polyhedron
addLinearConstr coefs intv poly =
  let (scaledCoefs, factor) = rescale $ removeTrailing 0 coefs
      scaledIntv = scale factor intv
   in if | null scaledCoefs -> Just poly
         | scaledIntv == fullInterval -> Just poly
         | isEmpty scaledIntv -> Nothing
         | otherwise ->
           case insertWithT intersectAndCheck scaledCoefs scaledIntv (linearConstraints poly) of
             Just constr -> Just $ poly {linearConstraints = constr}
             Nothing -> Nothing

intersectAndCheck :: Interval -> Interval -> Maybe Interval
intersectAndCheck i1 i2
  | isEmpty (i1 `intersect` i2) = Nothing
  | otherwise = Just $ i1 `intersect` i2

-- | TODO assumption same varOrder!
intersectP :: Polyhedron -> Polyhedron -> Maybe Polyhedron
intersectP p1 p2
  | isFullP p1 = Just p2
  | isFullP p2 = Just p1
  | otherwise =
    let coeffList = toListT (linearConstraints p1)
     in go p2 coeffList
  where
    go poly [] = Just poly
    go poly ((coefs, intv):clr) =
      case insertWithT intersectAndCheck coefs intv (linearConstraints poly) of
        Just constr -> go (poly {linearConstraints = constr}) clr
        Nothing -> Nothing

-- | TODO assumption same varOrder!
tryDisjunctP :: Polyhedron -> Polyhedron -> Maybe Polyhedron
tryDisjunctP p1 p2 =
  case mergeOnceT tryDisjunct (linearConstraints p1) (linearConstraints p2) of
    Nothing -> Nothing
    Just lc ->
      Just $ Polyhedron {varOrder = varOrder p1, linearConstraints = filterT (not . isFull) lc}

---------------------------------------------------------------------------------------------------
-- (In)equalities
---------------------------------------------------------------------------------------------------
-- TODO make this to additional interface between terms and polyhedra!
type Ineq a = ([((Symbol, Sort), a)], Interval)

ineqToTerm :: Ineq Integer -> Term
ineqToTerm (linComb, intv) = isInside (sumTerm linComb) intv

toIneqs :: Polyhedron -> [Ineq Integer]
toIneqs poly = map toIneq $ toListT $ linearConstraints poly
  where
    toIneq = first (filter ((/= 0) . snd) . zip (varOrder poly))

addIneq :: Ineq Rational -> Polyhedron -> Maybe Polyhedron
addIneq (linComb, intv) poly =
  let linCombM = Map.fromList linComb
      coefList = (\v -> Map.findWithDefault 0 v linCombM) <$> varOrder poly
   in addLinearConstr coefList intv poly

sumTerm :: [((Symbol, Sort), Integer)] -> Term
sumTerm = FOL.addT . map (\((v, s), c) -> FOL.multT [FOL.numberT c, FOL.var v s])

toTerms :: Polyhedron -> [Term]
toTerms = map ineqToTerm . toIneqs

data IncPoly
  = NewPoly Polyhedron
  | NotLinear
  | Infeasible

addConstr :: Polyhedron -> Term -> IncPoly
addConstr poly term =
  case termToIneq term of
    Nothing -> NotLinear
    Just ineq -> maybe Infeasible NewPoly (addIneq ineq poly)

tryPoly :: [(Symbol, Sort)] -> Term -> IncPoly
tryPoly varOrder = addConstr (fullP varOrder)

termToIneq :: Term -> Maybe (Ineq Rational)
termToIneq =
  \case
    Func comp [a, b] ->
      let sum =
            case FOL.addT [a, FOL.invT b] of
              Func FAdd ts -> ts
              t -> [t]
       in case comp of
            FLt -> second (ltInterval . (0 -)) <$> sumToLinComb sum
            FLte -> second (lteInterval . (0 -)) <$> sumToLinComb sum
            FEq -> second (eqInterval . (0 -)) <$> sumToLinComb sum
            _ -> Nothing
    _ -> Nothing

sumToLinComb :: [Term] -> Maybe ([((Symbol, Sort), Rational)], Rational)
sumToLinComb =
  \case
    [] -> Just ([], 0)
    x:xr -> do
      (cr, r) <- sumToLinComb xr
      case x of
        Var v t -> Just (((v, t), 1) : cr, r)
        Func FMul [Var v t, Const (CInt n)] -> Just (((v, t), n % 1) : cr, r)
        Func FMul [Const (CInt n), Var v t] -> Just (((v, t), n % 1) : cr, r)
        Func FMul [Var v t, Const (CReal n)] -> Just (((v, t), n) : cr, r)
        Func FMul [Const (CReal n), Var v t] -> Just (((v, t), n) : cr, r)
        Const (CReal n) -> Just (cr, n + r)
        Const (CInt n) -> Just (cr, (n % 1) + r)
        _ -> Nothing

---------------------------------------------------------------------------------------------------
-- Linear Combinations
---------------------------------------------------------------------------------------------------
-- | TODO Condition all have same variable order!; disjunctions
newtype PTerm =
  PTerm [(Polyhedron, Set Term)]
  deriving (Show)

-- | 'unions' computes the onion of polyhedra-base terms.
-- Note for this to be correct the variable order has to be same used by ALL polyhedra
unions :: [PTerm] -> PTerm
unions = go []
  where
    go acc [] = PTerm acc
    go acc (PTerm []:tr) = go acc tr
    go acc (PTerm (d:dr):tr) = go (insertDisjunct d acc) (PTerm dr : tr)
    --
    insertDisjunct new [] = [new]
    insertDisjunct (newP, newO) ((oldP, oldO):acc)
      | Set.isSubsetOf oldO newO && includedP newP oldP = (oldP, oldO) : acc
      | Set.isSubsetOf newO oldO && includedP oldP newP = insertDisjunct (newP, newO) acc
      | newO == oldO =
        case tryDisjunctP oldP newP of
          Just disP -> insertDisjunct (disP, newO) acc
          Nothing -> (oldP, oldO) : insertDisjunct (newP, newO) acc
      | otherwise = (oldP, oldO) : insertDisjunct (newP, newO) acc

-- | 'intersections' computes the insersection of polyhedra-base terms.
-- Note for this to be correct the variable order has to be same used by ALL polyhedra
intersections :: [(Symbol, Sort)] -> [PTerm] -> PTerm
intersections varOrder =
  \case
    [] -> PTerm [(fullP varOrder, Set.empty)]
    [term] -> term
    PTerm t1:tr ->
      let PTerm t2 = intersections varOrder tr
          prod = [intersectPO p1 p2 | p1 <- t1, p2 <- t2]
       in unions $ map (\cl -> PTerm [cl]) $ catMaybes prod
  where
    intersectPO (p1, o1) (p2, o2) =
      case intersectP p1 p2 of
        Nothing -> Nothing
        Just p
          | any (\l -> FOL.neg l `elem` o1) o2 -> Nothing
          | otherwise -> Just (p, Set.union o1 o2)

-- | TODO
fromFOL :: Term -> PTerm
fromFOL term = go $ toNNF term
  where
    varOrder = filter (FOL.isNumber . snd) $ Map.toList $ FOL.bindings term
        --
    go =
      \case
        NNFLit False term -> go $ NNFLit True (FOL.neg term)
        NNFLit True term ->
          case tryPoly varOrder term of
            NewPoly p -> PTerm [(p, Set.empty)]
            NotLinear -> PTerm [(fullP varOrder, Set.singleton term)]
            Infeasible -> PTerm []
        NNFAnd fs -> intersections varOrder $ map go fs
        NNFOr fs -> unions $ map go fs

-- | TODO
toFOL :: PTerm -> Term
toFOL (PTerm disjuncts) =
  FOL.orf $ flip map disjuncts $ \(poly, others) -> FOL.andf $ toTerms poly ++ Set.toList others

-- | TODO
normalize :: Term -> Term
normalize = toFOL . fromFOL

normalizeFast :: Term -> Term
normalizeFast = go . toNNF
  where
    go :: NNF Term -> Term
    go =
      \case
        NNFLit pol term
          | pol -> term
          | otherwise -> FOL.neg term
        NNFAnd [] -> FOL.true
        NNFOr [] -> FOL.false
        NNFAnd [f] -> go f
        NNFOr [f] -> go f
        NNFAnd fs -> tryNorm $ FOL.andf $ map go fs
        NNFOr fs -> tryNorm $ FOL.orf $ map go fs
        --
    tryNorm term
      | doNorm (toNNF term) = norm3 term
      | otherwise = term
        --
    norm3 = normalize . FOL.neg . normalize . FOL.neg . normalize
        --
    doNorm :: NNF a -> Bool
    doNorm =
      \case
        NNFLit _ _ -> False
        NNFOr fs -> all isLit fs
        NNFAnd fs -> all isLit fs
        --
    isLit :: NNF a -> Bool
    isLit =
      \case
        NNFLit _ _ -> True
        _ -> False

-- | TODO get non-trivial polyhedra constraints, TODO. rename!
nontrivialPolyhedra :: Term -> [(Polyhedron, Set Term)]
nontrivialPolyhedra term =
  let PTerm constr = fromFOL term
   in filter (not . isFullP . fst) constr

--------------------------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------------------------
-- | 'removeTrailing' x xs removes all occurrences of x at the end of xs
removeTrailing :: Eq a => a -> [a] -> [a]
removeTrailing neutral = go
  where
    go =
      \case
        [] -> []
        x:xr ->
          case x : go xr of
            [x]
              | x == neutral -> []
              | otherwise -> [x]
            xs -> xs
--------------------------------------------------------------------------------------------------
