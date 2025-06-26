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
module Issy.Logic.Polyhedra where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map

import Issy.Logic.FOL (Symbol, Term)

---------------------------------------------------------------------------------------------------
-- Interval and Bounds
---------------------------------------------------------------------------------------------------
-- 'Interval' represents an interval 
data Interval = Interval
  { upper :: UBound
  , lower :: LBound
  } deriving (Eq, Ord, Show)

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
isEmpty = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Efficent Maps for Lists
--      TODO: Move to own module?? => No, does not make sense
---------------------------------------------------------------------------------------------------
data RListMap k a = RListMap
  { neutral :: k
  , tree :: ListTree k a
  }

empty :: k -> RListMap k a
empty neut = RListMap {neutral = neut, tree = LTLeaf}

lookup :: Ord k => [k] -> RListMap k a -> Maybe a
lookup ks mp = lookupT (reduce (neutral mp) ks) $ tree mp

insertWith :: Ord k => (a -> a -> a) -> [k] -> a -> RListMap k a -> RListMap k a
insertWith comb ks val mp = mp {tree = insertWithT comb (reduce (neutral mp) ks) val (tree mp)}

reduce :: Eq k => k -> [k] -> [k]
reduce neutral = go
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
-- Linear Combinations
---------------------------------------------------------------------------------------------------
data WannabePolyhedron = WannabePolyhedron
  { linConstr :: RListMap Rational Interval
    -- | TODO: this FOR SURE needs a semantic definition
  , otherConstr :: [Term]
  }

addLinearConstr :: [Rational] -> Interval -> WannabePolyhedron -> WannabePolyhedron
addLinearConstr = error "TODO IMPLEMENT; ADD INFESABILITY CHECK!"

includedWP :: WannabePolyhedron -> WannabePolyhedron -> Bool
includedWP = error "TODO IMPLEMENT"

data PolyhedraContr = PolyhedraContr
  { variableOrder :: [Symbol]
  , constrs :: [WannabePolyhedron]
  }

fromFOL :: Term -> PolyhedraContr
fromFOL = error "TODO IMPLEMENT"

toFOL :: PolyhedraContr -> Term
toFOL = error "TODO IMPLEMENT"
--------------------------------------------------------------------------------------------------
