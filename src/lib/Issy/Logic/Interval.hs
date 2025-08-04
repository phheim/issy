---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Logic.Polyhedra
-- Description : Operations and represenations interval of numbers
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Logic.Interval
  ( Interval
  , -- Basic operations
    elemOf
  , isEmpty
  , -- Construction
    fullInterval
  , ltInterval
  , lteInterval
  , intersect
  , eqInterval
  , -- Set operations
    included
  , tryDisjunct
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
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- | 'Interval' represents an interval 
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

eqInterval :: Real a => a -> Interval
eqInterval r = Interval {upper = LTVal True (toRational r), lower = GTVal True (toRational r)}

elemOf :: Real a => a -> Interval -> Bool
elemOf = included . eqInterval

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

intersect :: Interval -> Interval -> Interval
intersect b1 b2 = Interval {upper = min (upper b1) (upper b2), lower = min (lower b1) (lower b2)}

included :: Interval -> Interval -> Bool
included b1 b2 = upper b1 <= upper b2 && lower b1 <= lower b2

isEmpty :: Interval -> Bool
isEmpty intv =
  case (lower intv, upper intv) of
    (GTVal leq lval, LTVal ueq uval) -> uval < lval || (uval == lval && (not leq || not ueq))
    _ -> False

tryDisjunct :: Interval -> Interval -> Maybe Interval
tryDisjunct i1 i2
  | isEmpty (i1 `intersect` i2) = Nothing
  | otherwise =
    Just $ Interval {upper = max (upper i1) (upper i1), lower = max (lower i1) (lower i2)}

-- | 'scale' applies to the interval, if interpreted as inequality constraint, the
-- | equivalence operation "multiply be the given factor"
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

-- | TODO
inLow :: Interval -> Term -> Term
inLow intv term =
  case lower intv of
    MinusInfinity -> FOL.true
    GTVal eq bound
      | eq -> term `FOL.geqT` FOL.numberT bound
      | otherwise -> term `FOL.gtT` FOL.numberT bound

-- | TODO
ltLow :: Interval -> Term -> Term
ltLow intv term =
  case lower intv of
    MinusInfinity -> FOL.false
    GTVal eq bound
      | eq -> term `FOL.ltT` FOL.numberT bound
      | otherwise -> term `FOL.leqT` FOL.numberT bound

-- | TODO
inUpp :: Interval -> Term -> Term
inUpp intv term =
  case upper intv of
    PlusInfinity -> FOL.true
    LTVal eq bound
      | eq -> term `FOL.leqT` FOL.numberT bound
      | otherwise -> term `FOL.ltT` FOL.numberT bound

-- | TODO
gtUpp :: Interval -> Term -> Term
gtUpp intv term =
  case upper intv of
    PlusInfinity -> FOL.false
    LTVal eq bound
      | eq -> term `FOL.gtT` FOL.numberT bound
      | otherwise -> term `FOL.geqT` FOL.numberT bound

-- | 'isInside' generates the 'Term' that a given 'Term' is inside the 'Interval'
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
