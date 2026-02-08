---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.Polyhedra
-- Description : Polyhedra-like representations
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements methods to represent terms as polyhedra and with polyhedra. Those
-- polyhedra are normalized and can therefore be used for normalization operations, as well
-- as matching on inequalities. We aim to implement this module somewhat efficiently.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase, MultiWayIf #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Polyhedra
  ( Polyhedron
  , Ineq
  , -- Representation
    ineqToTerm
  , sumTerm
  , toIneqs
  , toTerms
  , withPolyhedra
  , nontrivialPolyhedra
  , -- Normalizations
    normalize
  , normalizeFast
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
  -- ^ 'LTNode' is a leaf in the prefix tree. For LTNode melem subs
  -- - if (melem == Just elem) then [] is mapped to elem
  -- - for every (x, tree) in subs, this node maps x:xr to e if tree maps xr to e
  deriving (Eq, Show)

-- | Filter the list tree by removing all elements that do not fulfil the
-- predicate.
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

-- | Turn the list tree into a list, similar to 'Map.toList'.
toListT :: ListTree k a -> [([k], a)]
toListT = go []
  where
    go _ LTLeaf = []
    go acc (LTNode val succs) =
      let rec = concatMap (\(k, succ) -> go (k : acc) succ) $ Map.toList succs
       in case val of
            Nothing -> rec
            Just val -> (reverse acc, val) : rec

-- | Insert an element into the list tree with a given key list. If the element
-- is already present use the given merge function. If the elements are not merge-able
-- then this method returns 'Nothing'.
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

-- | Given an inclusion check for the elements, check if the second list tree is a
-- subset of the first one, i.e. all keys in the second one are also mapped in
-- the first one, with an element such that the element of the second on is included
-- in the first one. This is later useful to compare polyhedra, where the first one is
-- the suspected larger polyhedra, with less constraints.
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

-- Helper data type for merging.
data MergeRes a
  = MergeFail
  -- ^ Merging failed.
  | MergeId
  -- ^ Merged to identical elements.
  | Merged a
  -- ^ Merged with given result.

instance Functor MergeRes where
  fmap _ MergeFail = MergeFail
  fmap _ MergeId = MergeId
  fmap m (Merged a) = Merged (m a)

-- | Try to merge to list tree, by merging zero or one element with the same key by
-- the given merging function. All other keys and elements must be identical, otherwise
-- merging is not possible.
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
-- | Somewhat efficient representation of a polyhedron. A polyhedron ranges over sorted variables
-- (integer or real-valued) with a fixed order. Operations on multiple polyhedra can only be
-- done if they have the same variable order.
data Polyhedron = Polyhedron
  { varOrder :: [(Symbol, Sort)]
    -- ^ sorted variables present in the polyhedron in that order. The sorts must
    -- be integers and reals
  , linearConstraints :: ListTree Integer Interval
    -- ^ Map a list of coefficients for the variables as in order to an interval. The semantic is
    -- that resulting linear term with the coefficients is inside the interval. Zeros must
    -- be cut from the end of the coefficient list. Furthermore, the coefficient list
    -- must be normalized/scaled, in the sense that the first non-zero coefficient is the
    -- smallest positive one such that all coefficients can be integers.
    -- So for example if the variables are "[x, y, z, w]" and the coefficient list is [3, -2, 1]
    -- with the interval "(-infinity, 10]" this represent the constraint
    -- "-infinity <= 3*x - 2*y + 1*z + 0*w <= 10".
  } deriving (Show)

fullP :: [(Symbol, Sort)] -> Polyhedron
fullP vorder = Polyhedron {varOrder = vorder, linearConstraints = LTLeaf}

-- | Check if the polyhedron is full.
isFullP :: Polyhedron -> Bool
isFullP poly =
  case linearConstraints poly of
    LTLeaf -> True
    _ -> False

-- | Check if the first polyhedron is a subset of the second one.
includedP :: Polyhedron -> Polyhedron -> Bool
includedP p1 p2 = includedLT included (linearConstraints p1) (linearConstraints p2)

-- | Scale a list of rational coefficients such that they fulfill the normalisation property
-- in a polyhedron and return the scale factor.
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

-- | Add/conjunct a constraint given by coefficients and an interval to a polyhedron.
-- Return 'Nothing' if that renders the polyhedron empty.
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

-- | Intersect two polyhedra over the same order of variables (this is assumed) while
-- normalizing the constraints. Return 'Nothing' if the conjunct is empty.
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

-- | Try to disjunct two polyhedra over the same order of variables (this is assumed) while
-- normalizing the constraints. Return 'Nothing' if they are not aligned for disjunction.
tryDisjunctP :: Polyhedron -> Polyhedron -> Maybe Polyhedron
tryDisjunctP p1 p2 =
  case mergeOnceT subDisj (linearConstraints p1) (linearConstraints p2) of
    Nothing -> Nothing
    Just lc ->
      Just $ Polyhedron {varOrder = varOrder p1, linearConstraints = filterT (not . isFull) lc}
  where
    subDisj
      | isInteger p1 && isInteger p2 = tryDisjunctInt
      | otherwise = tryDisjunct

isInteger :: Polyhedron -> Bool
isInteger = all (all ((== FOL.SInt) . snd . fst) . fst) . toIneqs

---------------------------------------------------------------------------------------------------
-- (In)equalities
---------------------------------------------------------------------------------------------------
-- | Representation of a set of inequalities over a polymorphic numeric type for the coefficients.
-- The list represent a linear combination of the variables and their respective coefficients.
-- This sum must be within the interval. For example, "([((x, ..) 3), ((y, ..) -3)], (-4, 10])"
-- represent the inequality "-4 < 3x - 3y <= 10".
type Ineq a = ([((Symbol, Sort), a)], Interval)

-- | Turn an integer inequality into its respective boolean term.
ineqToTerm :: Ineq Integer -> Term
ineqToTerm (linComb, intv) = isInside (sumTerm linComb) intv

-- | Turn the linear combination part of an inequality into a numeric term.
sumTerm :: [((Symbol, Sort), Integer)] -> Term
sumTerm = FOL.addT . map (\((v, s), c) -> FOL.multT [FOL.numberT c, FOL.var v s])

-- | Turn a polyhedron into inequalities.
toIneqs :: Polyhedron -> [Ineq Integer]
toIneqs poly = map toIneq $ toListT $ linearConstraints poly
  where
    toIneq = first (filter ((/= 0) . snd) . zip (varOrder poly))

-- | Turn a polyhedron into inequality terms. Interpreted conjunctively they
-- represent the polyhedron.
toTerms :: Polyhedron -> [Term]
toTerms = map ineqToTerm . toIneqs

-- | Enum to incrementally build up a polyhedron by adding constraints.
data IncPoly
  = NewPoly Polyhedron
  -- ^ The new polyhedron.
  | NotLinear
  -- ^ The constraint is not linear.
  | Infeasible
  -- ^ The polyhedron is empty.

-- | Try to make boolean term as a polyhedron. This mainly includes syntactic
-- matching to see if the term can be coerced into the form of a linear constraints.
tryPoly :: [(Symbol, Sort)] -> Term -> IncPoly
tryPoly varOrder = addConstr (fullP varOrder)

-- | Try to add a boolean term to a polyhedron.
addConstr :: Polyhedron -> Term -> IncPoly
addConstr poly term =
  case termToIneq term of
    Nothing -> NotLinear
    Just ineq -> maybe Infeasible NewPoly (addIneq ineq poly)

addIneq :: Ineq Rational -> Polyhedron -> Maybe Polyhedron
addIneq (linComb, intv) poly =
  let linCombM = Map.fromList linComb
      coefList = (\v -> Map.findWithDefault 0 v linCombM) <$> varOrder poly
   in addLinearConstr coefList intv poly

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
-- | Representation of a disjunction of polyhedra, each conjunct with some additional
-- non-linear terms. This is a normalized representation of a term.
newtype PTerm =
  PTerm [(Polyhedron, Set Term)]
  deriving (Show)

-- | Compute the union of polyhedra-based terms. For this to be correct the variable order
-- has to be same used by all polyhedra.
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

-- | Compute the intersection of polyhedra-base terms. For this to be correct the
-- variable order has to be same used by all polyhedra.
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

-- | Turn a term into a polyhedra-base one. This includes a lot of normalization
-- operations in the subroutines.
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

-- | Turn a polyhedra-based term into a normal one.
toFOL :: PTerm -> Term
toFOL (PTerm disjuncts) =
  FOL.orf $ flip map disjuncts $ \(poly, others) -> FOL.andf $ toTerms poly ++ Set.toList others

-- | Turn a term into an equivalent list of pairs of a polyhedron and a set term.
-- The polyhedron and the set of terms in a single pair is interpreted conjunctively.
-- The overall list is interpreted disjunctively. This operation is heavily normalizing.
withPolyhedra :: Term -> [(Polyhedron, Set Term)]
withPolyhedra term =
  let PTerm constr = fromFOL term
   in constr

-- | Similar to 'withPolyhedra' but filters out all pairs with polyhedra that represent
-- the full space, i.e. disjunction that are not linear (e.g. a boolean variable).
-- The result will usually not be equivalent to the input term.
nontrivialPolyhedra :: Term -> [(Polyhedron, Set Term)]
nontrivialPolyhedra = filter (not . isFullP . fst) . withPolyhedra

-- | Normalize a term by turning the linear constraints into polyhedra (similar to 'withPolyhedra').
-- This allows to get rid of subsumed terms, detect inconsistencies, and normalize the representation.
-- However, this operation can be very costly.
normalize :: Term -> Term
normalize = toFOL . fromFOL

-- | Faster version of normalization where 'normalize' is only applied to the lower
-- levels of the boolean term tree.
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

--------------------------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------------------------
-- | Removes all occurrences of a given element at the end of the list.
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
