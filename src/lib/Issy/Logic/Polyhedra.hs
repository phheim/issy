---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Logic.Polyhedra
-- Description : Operations and represenations for polyhedra-like representations
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Polyhedra
  ( Polyhedron
  , Interval(..)
  , UBound(..)
  , LBound(..)
  , toIneqs
  , normalize
  , projectPolyhedra
  ) where

---------------------------------------------------------------------------------------------------
import Data.Bifunctor (first)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.Propositional (DNF(..), toDNF)

---------------------------------------------------------------------------------------------------
-- Interval and Bounds
---------------------------------------------------------------------------------------------------
-- 'Interval' represents an interval 
data Interval = Interval
  { upper :: UBound
  , lower :: LBound
  } deriving (Eq, Ord, Show)

fullInterval :: Interval
fullInterval = Interval {upper = PlusInfinity, lower = MinusInfinity}

ltInterval :: Real a => a -> Interval
ltInterval r = fullInterval {upper = LTVal False (toRational r)}

lteInterval :: Real a => a -> Interval
lteInterval r = fullInterval {upper = LTVal True (toRational r)}

gtInterval :: Real a => a -> Interval
gtInterval r = fullInterval {lower = GTVal False (toRational r)}

gteInterval :: Real a => a -> Interval
gteInterval r = fullInterval {lower = GTVal True (toRational r)}

-- | 'UBound' is a type for optional inclusive/exclusive upper rational bounds 
data UBound
  = PlusInfinity
 -- ^ 'PlusInfinity' means that there is no upper bound
  | LTVal Bool Rational
 -- ^ 'LTVal' is a </<= C bound. The Boolean flag indicates if is included
  deriving (Eq, Show)

-- | 'LBound' is a type for optional inclusive/exclusive lower rational bounds 
data LBound
  = MinusInfinity
 -- ^ 'MinusInfinity' means that there is no lower bound
  | GTVal Bool Rational
 -- ^ 'LTVal' is a >/>= C bound. The Boolean flag indicates if is included
  deriving (Eq, Show)

instance Ord UBound where
  compare b1 b2 =
    case (b1, b2) of
      (PlusInfinity, PlusInfinity) -> EQ
      (_, PlusInfinity) -> LT
      (PlusInfinity, _) -> GT
      (LTVal eq1 v1, LTVal eq2 v2)
        | v1 < v2 -> LT
        | v1 > v2 -> GT
        | eq1 && not eq2 -> GT
        | eq2 && not eq1 -> LT
        | otherwise -> EQ

instance Ord LBound where
  compare b1 b2 =
    case (b1, b2) of
      (MinusInfinity, MinusInfinity) -> EQ
      (_, MinusInfinity) -> GT
      (MinusInfinity, _) -> LT
      (GTVal eq1 v1, GTVal eq2 v2)
        | v1 < v2 -> GT
        | v1 > v2 -> LT
        | eq1 && not eq2 -> LT
        | eq2 && not eq1 -> GT
        | otherwise -> EQ

intersect :: Interval -> Interval -> Interval
intersect b1 b2 = Interval {upper = max (upper b1) (upper b2), lower = max (lower b1) (lower b2)}

includedI :: Interval -> Interval -> Bool
includedI b1 b2 = upper b1 >= upper b2 && lower b1 >= lower b2

isEmpty :: Interval -> Bool
isEmpty intv =
  case (lower intv, upper intv) of
    (GTVal leq lval, LTVal ueq uval) -> uval < lval || (uval == lval && (not leq || not ueq))
    _ -> False

isInside :: Term -> Interval -> Term
isInside t intv =
  let lowT =
        case lower intv of
          MinusInfinity -> FOL.true
          GTVal True r -> FOL.geqT t $ FOL.numberT r
          GTVal False r -> FOL.gtT t $ FOL.numberT r
      upT =
        case upper intv of
          PlusInfinity -> FOL.true
          LTVal True r -> FOL.leqT t $ FOL.numberT r
          LTVal False r -> FOL.ltT t $ FOL.numberT r
   in FOL.andf [lowT, upT]

---------------------------------------------------------------------------------------------------
-- Efficent Maps for Lists
---------------------------------------------------------------------------------------------------
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

data ListTree k a
  = LTLeaf
  | LTNode (Maybe a) (Map k (ListTree k a))

toListT :: ListTree k a -> [([k], a)]
toListT = go []
  where
    go _ LTLeaf = []
    go acc (LTNode val succs) =
      let rec = concatMap (\(k, succ) -> go (k : acc) succ) $ Map.toList succs
       in case val of
            Nothing -> rec
            Just val -> (reverse acc, val) : rec

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

includedLT :: Ord k => (a -> a -> Bool) -> ListTree k a -> ListTree k a -> Bool
includedLT includedElems = go
  where
    go LTLeaf _ = True
    go _ LTLeaf = False
    go (LTNode l1 succ1) (LTNode l2 succ2) =
      let labelInc =
            case (l1, l2) of
              (Nothing, _) -> True
              (_, Nothing) -> False
              (Just l1, Just l2) -> includedElems l1 l2
          succInc =
            all
              (\(k, succ1) ->
                 case succ2 !? k of
                   Nothing -> False
                   Just succ2 -> go succ1 succ2)
              $ Map.toList succ1
       in labelInc && succInc

---------------------------------------------------------------------------------------------------
-- Polyhedra
---------------------------------------------------------------------------------------------------
data Polyhedron = Polyhedron
  { varOrder :: [(Symbol, Sort)]
    -- | TODO use map instead, this is more usable
  , linearConstraints :: ListTree Rational Interval
    -- | TODO: this FOR SURE needs a semantic definition
  }

fullP :: [(Symbol, Sort)] -> Polyhedron
fullP vorder = Polyhedron {varOrder = vorder, linearConstraints = LTLeaf}

isFullP :: Polyhedron -> Bool
isFullP poly =
  case linearConstraints poly of
    LTLeaf -> True
    _ -> False

-- | TODO assumption same varOrder!
includedP :: Polyhedron -> Polyhedron -> Bool
includedP p1 p2 = includedLT includedI (linearConstraints p1) (linearConstraints p2)

addLinearConstr :: [Rational] -> Interval -> Polyhedron -> Maybe Polyhedron
addLinearConstr coefs intv poly
  | null (removeTrailing 0 coefs) = Just poly
  | intv == fullInterval = Just poly
  | isEmpty intv = Nothing
  | otherwise =
    case insertWithT intersectAndCheck (removeTrailing 0 coefs) intv (linearConstraints poly) of
      Just constr -> Just $ poly {linearConstraints = constr}
      Nothing -> Nothing
  where
    intersectAndCheck i1 i2
      | isEmpty (i1 `intersect` i2) = Nothing
      | otherwise = Just $ i1 `intersect` i2

type Ineq = ([((Symbol, Sort), Rational)], Interval)

toIneqs :: Polyhedron -> [Ineq]
toIneqs poly = map toIneq $ toListT $ linearConstraints poly
  where
    toIneq = first (filter ((/= 0) . snd) . zip (varOrder poly))

polyToTerms :: Polyhedron -> [Term]
polyToTerms = map ineqToTerm . toIneqs
  where
    ineqToTerm (linComb, intv) =
      flip isInside intv
        $ FOL.addT
        $ map (\((v, s), c) -> FOL.multT [FOL.numberT c, FOL.var v s]) linComb

data IncPoly
  = NewPoly Polyhedron
  | NotLinear
  | Infeasible

addConstr :: Polyhedron -> Term -> IncPoly
addConstr poly =
  \case
    FOL.Func FOL.FLt [t, FOL.Const (FOL.CInt _)] ->
      let (linComb, intv) = error "TODO IMPLEMENT" t
       in maybe Infeasible NewPoly (addLinearConstr linComb intv poly)
    _ -> NotLinear

---------------------------------------------------------------------------------------------------
-- Linear Combinations
---------------------------------------------------------------------------------------------------
-- | TODO Condition all have same variable order!; disjunctions
newtype PTerm =
  PTerm [(Polyhedron, Set Term)]

-- | TODO get non-trivial polyhedra
nonTrivialPolyhedra :: PTerm -> [Polyhedron]
nonTrivialPolyhedra (PTerm constrs) = filter (not . isFullP) $ map fst constrs

-- | TODO
fromFOL :: Term -> PTerm
fromFOL term =
  let DNF dnf = toDNF term
   in PTerm $ go [] dnf
  where
    varOrder = filter (FOL.isNumber . snd) $ Map.toList $ FOL.bindings term
        --
    go acc [] = reverse acc
    go acc (c:cr) =
      case fromClause (fullP varOrder, Set.empty) c of
        Just (poly, others)
          | supersumed (poly, others) acc -> go acc cr
          | otherwise -> go ((poly, others) : acc) cr
        Nothing -> go acc cr
        --
    supersumed (poly, others) = all $ \(p, o) -> o == others && includedP poly p
        --
    fromClause (poly, others) [] = Just (poly, others)
    fromClause (poly, others) (l:lr) =
      case addConstr poly (fromLit l) of
        NewPoly poly -> fromClause (poly, others) lr
        NotLinear -> fromClause (poly, Set.insert (fromLit l) others) lr
        Infeasible -> Nothing
        --
    fromLit (pol, lit)
      | pol = lit
      | otherwise = FOL.neg lit

-- | TODO
toFOL :: PTerm -> Term
toFOL (PTerm disjuncts) =
  FOL.orf $ flip map disjuncts $ \(poly, others) -> FOL.andf $ polyToTerms poly ++ Set.toList others

-- | TODO
normalize :: Term -> Term
normalize = toFOL . fromFOL

-- | TODO
projectPolyhedra :: Term -> [Polyhedron]
projectPolyhedra = nonTrivialPolyhedra . fromFOL
--------------------------------------------------------------------------------------------------
