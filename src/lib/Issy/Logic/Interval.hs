---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.Polyhedra
-- Description : Interval of numbers
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a representation and operations on intervals in the integers
-- and real numbers.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Interval
  ( Interval
  , -- Basic checks
    elemOf
  , isEmpty
  , isFull
  , -- Construction
    fullInterval
  , ltInterval
  , lteInterval
  , eqInterval
  , -- Set operations
    included
  , intersect
  , tryDisjunct
  , tryDisjunctInt
  , -- Scaling
    scale
  , -- Compharison to terms
    isInside
  , inUpp
  , inLow
  , gtUpp
  , ltLow
  ) where

---------------------------------------------------------------------------------------------------
import Data.Ratio ((%), denominator)

import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- | Representation of an interval
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

-- 'Ord' on 'UBound' is defined as larger means more inclusive, i.e larger upper bound
instance Ord UBound where
  compare b1 b2 =
    case (b1, b2) of
      (PlusInfinity, PlusInfinity) -> EQ
      (_, PlusInfinity) -> LT
      (PlusInfinity, _) -> GT
      (LTVal eq1 v1, LTVal eq2 v2)
        | v1 > v2 -> GT
        | v1 < v2 -> LT
        | eq1 && not eq2 -> GT
        | eq2 && not eq1 -> LT
        | otherwise -> EQ

-- 'Ord' on 'BBound' is defined as larger means more inclusive, i.e. smaller lower bound
instance Ord LBound where
  compare b1 b2 =
    case (b1, b2) of
      (MinusInfinity, MinusInfinity) -> EQ
      (_, MinusInfinity) -> LT
      (MinusInfinity, _) -> GT
      (GTVal eq1 v1, GTVal eq2 v2)
        | v1 < v2 -> GT
        | v1 > v2 -> LT
        | eq1 && not eq2 -> GT
        | eq2 && not eq1 -> LT
        | otherwise -> EQ

-- | Check if an interval is empty in the real value space.
isEmpty :: Interval -> Bool
isEmpty intv =
  case (lower intv, upper intv) of
    (GTVal leq lval, LTVal ueq uval) -> uval < lval || (uval == lval && (not leq || not ueq))
    _ -> False

-- | Check if an interval represents the full space.
isFull :: Interval -> Bool
isFull intv =
  case (lower intv, upper intv) of
    (MinusInfinity, PlusInfinity) -> True
    _ -> False

-- | Check if a number is included in an interval.
elemOf :: Real a => a -> Interval -> Bool
elemOf = included . eqInterval

-- | The interval over the full space of number from minus to plus infinity.
fullInterval :: Interval
fullInterval = Interval {upper = PlusInfinity, lower = MinusInfinity}

-- | The interval open interval the represents all numbers smaller k, i.e. (- infinity, k).
ltInterval :: Real a => a -> Interval
ltInterval r = fullInterval {upper = LTVal False (toRational r)}

-- | The interval closed interval the represents all numbers smaller-equal k, i.e. (- infinity, k].
lteInterval :: Real a => a -> Interval
lteInterval r = fullInterval {upper = LTVal True (toRational r)}

-- | The interval that represents a single point, i.e. [k, k].
eqInterval :: Real a => a -> Interval
eqInterval r = Interval {upper = LTVal True (toRational r), lower = GTVal True (toRational r)}

-- | Check if one interval is included in the other one.
included :: Interval -> Interval -> Bool
included b1 b2 = upper b1 <= upper b2 && lower b1 <= lower b2

-- | Intersection of two intervals.
intersect :: Interval -> Interval -> Interval
intersect b1 b2 = Interval {upper = min (upper b1) (upper b2), lower = min (lower b1) (lower b2)}

-- | Try to compute the disjunction of two intervals in the real space.
tryDisjunct :: Interval -> Interval -> Maybe Interval
tryDisjunct i1 i2
  | isEmpty i1 = Just i2
  | isEmpty i2 = Just i1
  | untouchSmaller (upper i1) (lower i2) = Nothing
  | untouchSmaller (upper i2) (lower i1) = Nothing
  | otherwise =
    Just $ Interval {upper = max (upper i1) (upper i2), lower = max (lower i1) (lower i2)}
  where
    untouchSmaller :: UBound -> LBound -> Bool
    untouchSmaller PlusInfinity _ = False
    untouchSmaller _ MinusInfinity = False
    untouchSmaller (LTVal uinc ur) (GTVal linc lr)
      | ur < lr = True
      | lr == ur && not uinc && not linc = True
      | otherwise = False

-- | Try to compute the disjunction of two intervals on the integer grid. This means
-- that interval that do not touch but, do not have any integer points between them are
-- joined. For example, [-2, 0.6) and [0.8, 4) would be unified to [-2, 4].
tryDisjunctInt :: Interval -> Interval -> Maybe Interval
tryDisjunctInt i1 i2 = tryDisjunct (liftBorders i1) (liftBorders i2)
  where
    liftBorders i = Interval {upper = liftUp (upper i), lower = liftLow (lower i)}
    liftUp PlusInfinity = PlusInfinity
    liftUp (LTVal inc r)
      | denominator r /= 1 = LTVal False (ceiling r % 1)
      | inc = LTVal False (r + 1)
      | otherwise = LTVal False r
    liftLow MinusInfinity = MinusInfinity
    liftLow (GTVal inc r)
      | denominator r /= 1 = GTVal False (floor r % 1)
      | inc = GTVal False (r - 1)
      | otherwise = GTVal False r

-- | 'scale' applies to the interval, if interpreted as inequality constraint, the
-- | equivalence operation "multiply be the given factor". Note that for a negative
-- scaling factor this will "swap" the bounds.
scale :: Rational -> Interval -> Interval
scale k intv
  | k < 0 = scale (-k) $ multMinusOne intv
  | otherwise =
    let lw =
          case lower intv of
            MinusInfinity -> MinusInfinity
            GTVal incl r -> GTVal incl (k * r)
        up =
          case upper intv of
            PlusInfinity -> PlusInfinity
            LTVal incl r -> LTVal incl (k * r)
     in Interval {upper = up, lower = lw}

-- | 'multMinusOne' applies to the interval, if interpreted as inequality constraint, the
-- equivalence operation "multiply with minus one",  i.e swap upper and lower bounds
-- and multiply their value by -1
multMinusOne :: Interval -> Interval
multMinusOne intv =
  let up =
        case lower intv of
          MinusInfinity -> PlusInfinity
          GTVal incl r -> LTVal incl (-r)
      lw =
        case upper intv of
          PlusInfinity -> MinusInfinity
          LTVal incl r -> GTVal incl (-r)
   in Interval {upper = up, lower = lw}

-- | Generate the term which expresses that a given term is inside the interval.
isInside :: Term -> Interval -> Term
isInside t intv =
  case isSingleton intv of
    Just r -> t `FOL.equal` FOL.numberT r
    Nothing ->
      case isIntegerSingleton intv of
        Nothing -> FOL.andf [inLow intv t, inUpp intv t]
        Just i
          | FOL.isInteger t -> t `FOL.equal` FOL.intConst i
          | otherwise -> FOL.andf [inLow intv t, inUpp intv t]

-- | Generate the term which expresses that a given term is within (larger or equal)
-- the intervals lower bound.
inLow :: Interval -> Term -> Term
inLow intv term =
  case lower intv of
    MinusInfinity -> FOL.true
    GTVal eq bound
      | eq -> term `FOL.geqT` FOL.numberT bound
      | otherwise -> term `FOL.gtT` FOL.numberT bound

-- | Generate the term which expresses that a given term is smaller than the
-- intervals lower bound, i.e. outside of the interval.
ltLow :: Interval -> Term -> Term
ltLow intv term =
  case lower intv of
    MinusInfinity -> FOL.false
    GTVal eq bound
      | eq -> term `FOL.ltT` FOL.numberT bound
      | otherwise -> term `FOL.leqT` FOL.numberT bound

-- | Generate the term which expresses that a given term is within (smaller or equal)
-- the intervals upper bound.
inUpp :: Interval -> Term -> Term
inUpp intv term =
  case upper intv of
    PlusInfinity -> FOL.true
    LTVal eq bound
      | eq -> term `FOL.leqT` FOL.numberT bound
      | otherwise -> term `FOL.ltT` FOL.numberT bound

-- | Generate the term which expresses that a given term is greater than the
-- intervals upper bound, i.e. outside of the interval.
gtUpp :: Interval -> Term -> Term
gtUpp intv term =
  case upper intv of
    PlusInfinity -> FOL.false
    LTVal eq bound
      | eq -> term `FOL.gtT` FOL.numberT bound
      | otherwise -> term `FOL.geqT` FOL.numberT bound

isSingleton :: Interval -> Maybe Rational
isSingleton intv =
  case (lower intv, upper intv) of
    (GTVal True l, LTVal True u)
      | l == u -> Just u
      | otherwise -> Nothing
    _ -> Nothing

isIntegerSingleton :: Interval -> Maybe Integer
isIntegerSingleton intv =
  case (lower intv, upper intv) of
    (GTVal True l, LTVal True u)
      | ceiling l == (floor u :: Integer) -> Just $ floor u
      | otherwise -> Nothing
    (GTVal False l, _)
      | denominator l == 1 -> isIntegerSingleton $ intv {lower = GTVal True (l + 1)}
      | otherwise -> isIntegerSingleton $ intv {lower = GTVal True l}
    (_, LTVal False u)
      | denominator u == 1 -> isIntegerSingleton $ intv {upper = LTVal True (u - 1)}
      | otherwise -> isIntegerSingleton $ intv {upper = LTVal True u}
    _ -> Nothing
---------------------------------------------------------------------------------------------------
