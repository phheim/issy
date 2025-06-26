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
-- TODO export more!
module Issy.Logic.Polyhedra
  ( Polyhedron
  , normalize
  , projectPolyhedra
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Logic.FOL (Symbol, Term)
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

included :: Interval -> Interval -> Bool
included b1 b2 = upper b1 >= upper b2 && lower b1 >= lower b2

isEmpty :: Interval -> Bool
isEmpty intv =
  case (lower intv, upper intv) of
    (GTVal leq lval, LTVal ueq uval) -> uval < lval || (uval == lval && (not leq || not ueq))
    _ -> False

---------------------------------------------------------------------------------------------------
-- Efficent Maps for Lists
---------------------------------------------------------------------------------------------------
data RListMap k a = RListMap
  { neutral :: k
  , tree :: ListTree k a
  }

empty :: k -> RListMap k a
empty neut = RListMap {neutral = neut, tree = LTLeaf}

lookup :: Ord k => [k] -> RListMap k a -> Maybe a
lookup ks mp = lookupT (removeTrailing (neutral mp) ks) $ tree mp

insertWith :: Ord k => (a -> a -> a) -> [k] -> a -> RListMap k a -> RListMap k a
insertWith comb ks val mp =
  mp {tree = insertWithT comb (removeTrailing (neutral mp) ks) val (tree mp)}

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

lookupT :: Ord k => [k] -> ListTree k a -> Maybe a
lookupT ks tree =
  case (tree, ks) of
    (LTLeaf, _) -> Nothing
    (LTNode val _, []) -> val
    (LTNode _ succs, k:kr) ->
      case succs !? k of
        Nothing -> Nothing
        Just succ -> lookupT kr succ

insertWithT :: Ord k => (a -> a -> a) -> [k] -> a -> ListTree k a -> ListTree k a
insertWithT comb ks val tree = go tree ks
  where
    go LTLeaf [] = LTNode (Just val) Map.empty
    go LTLeaf (k:kr) = LTNode Nothing $ Map.singleton k $ go LTLeaf kr
    go (LTNode Nothing succs) [] = LTNode (Just val) succs
    go (LTNode (Just old) succs) [] = LTNode (Just (comb val old)) succs
    go (LTNode label succs) (k:kr) =
      case succs !? k of
        Nothing -> LTNode label $ Map.insert k (go LTLeaf kr) succs
        Just tree -> LTNode label $ Map.insert k (go tree kr) succs

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
  { varOrder :: [Symbol]
  , linearConstraints :: RListMap Rational Interval
    -- | TODO: this FOR SURE needs a semantic definition
  }

fullP :: [Symbol] -> Polyhedron
fullP = error "TODO IMPLEMENT"

isFullP :: Polyhedron -> Bool
isFullP = error "TODO IMPLEMENT"

includedP :: Polyhedron -> Polyhedron -> Bool
includedP = error "TODO IMPLEMENT"

addLinearConstr :: [Rational] -> Interval -> Polyhedron -> Polyhedron
addLinearConstr = error "TODO IMPLEMENT; ADD INFESABILITY CHECK!"

polyToTerms :: Polyhedron -> [Term]
polyToTerms = error "TODO"

addConstr :: Polyhedron -> Term -> Maybe Polyhedron
addConstr = error "TODO IMPLEMENT CONTRAINT DETECTION"

---------------------------------------------------------------------------------------------------
-- Linear Combinations
---------------------------------------------------------------------------------------------------
-- | TODO Condition all have same variable order!; disjunctions
newtype PolyhedraConstr =
  PolyhedraConstr [(Polyhedron, Set Term)]

-- | TODO get non-trivial polyhedra
nonTrivialPolyhedra :: PolyhedraConstr -> [Polyhedron]
nonTrivialPolyhedra (PolyhedraConstr constrs) = filter (not . isFullP) $ map fst constrs

-- | TODO
fromFOL :: Term -> PolyhedraConstr
fromFOL term =
  let DNF dnf = toDNF term
   in PolyhedraConstr $ go [] dnf
  where
    varOrder = map fst $ filter (FOL.isNumber . snd) $ Map.toList $ FOL.bindings term
        --
    go acc [] = reverse acc
    go acc (c:cr) =
      let (poly, others) = fromClause (fullP varOrder, Set.empty) c
       in if supersumed (poly, others) acc
            then go acc cr
            else go ((poly, others) : acc) cr
        --
    supersumed (poly, others) = all $ \(p, o) -> o == others && includedP poly p
        --
    fromClause (poly, others) [] = (poly, others)
    fromClause (poly, others) (l:lr) =
      case addConstr poly (fromLit l) of
        Just poly -> fromClause (poly, others) lr
        Nothing -> fromClause (poly, Set.insert (fromLit l) others) lr
        --
    fromLit (pol, lit)
      | pol = lit
      | otherwise = FOL.neg lit

-- | TODO
toFOL :: PolyhedraConstr -> Term
toFOL (PolyhedraConstr disjuncts) =
  FOL.orf $ flip map disjuncts $ \(poly, others) -> FOL.andf $ polyToTerms poly ++ Set.toList others

-- | TODO
normalize :: Term -> Term
normalize = toFOL . fromFOL

-- | TODO
projectPolyhedra :: Term -> [Polyhedron]
projectPolyhedra = nonTrivialPolyhedra . fromFOL
--------------------------------------------------------------------------------------------------
