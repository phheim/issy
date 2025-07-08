---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.PolyhedraGeometricAccel
-- Description : Implementaion of the general version of geometric acceleration based on polyhedra
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.PolyhedraGeometricAccel
  ( accelReach
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, setName)
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.Acceleration.LoopScenario (reducedLoopArena)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Logging

import Issy.Logic.Polyhedra

--TODO stuff like that is the first step to spaghettic code, move somewhere else!
import Issy.Solver.Acceleration.MDAcceleration (iterA)

---------------------------------------------------------------------------------------------------
-- Top-level acceleration
---------------------------------------------------------------------------------------------------
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GGeoA" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  let prime = FOL.uniquePrefix "init_" $ usedSymbols arena
  res <- accelGAL conf heur player arena prime loc reach FOL.true FOL.true
  case res of
    Just (conc, prog) -> do
      lg conf ["Suceeded with", SMTLib.toString conc]
      pure (conc, prog)
    Nothing -> do
      lg conf ["Failed"]
      pure (FOL.false, Synt.empty)

accelGAL ::
     Config
  -> Heur
  -> Player
  -> Arena
  -> Symbol
  -> Loc
  -> SymSt
  -> Term
  -> Term
  -> IO (Maybe (Term, SyBo))
accelGAL conf heur player arena prime loc = go 0
  where
    -- TODO: split recursion between depth and iter to be able to reuse loop-game and others!
    go depth reach maintain inv = do
      let gal = lemmaGuess heur (vars arena) prime (reach `get` loc)
      case gal of
        Nothing -> pure Nothing
        Just gal -> iter 0 inv gal
      where
        iter cnt inv gal = do
          let al = addInv (vars arena) prime inv $ addMaintain maintain $ galToAl gal
          pre <- preCond conf heur player arena loc reach prime al
          case pre of
            Right res -> pure $ Just res
            Left pre
              | pre == FOL.false -> pure Nothing
              | H.ggaIters heur > cnt -> pure Nothing
              | otherwise -> do
                pre <-
                  if depth < H.ggaDepth heur
                    then nest inv gal pre
                    else pure pre
                iter (cnt + 1) pre gal
        -- Operation called when the precondition is nested
        nest inv gal pre = do
          let subGoal = set (emptySt arena) loc pre
          let subMaintain = FOL.andf [maintain, gstay gal]
          res <- go (depth + 1) subGoal subMaintain inv
          case res of
            Nothing -> pure pre
            Just (res, subProg) -> do
              error "TODO: what do I actually do with this program?"
              pure res

---------------------------------------------------------------------------------------------------
-- Attractor through loop arena
---------------------------------------------------------------------------------------------------
-- TODO: can this be generalized module wise?
data AccelLemma = AccelLemma
  { base :: Term
  , step :: Term
  , conc :: Term
  }

--TODO: preCond does not find invariant on base, this has to be taken care of like in the loop sceneration or so, maybe we could use the additional info of the polyhera! Maybe build up new projection function?
galToAl :: GenAccelLemma -> AccelLemma
galToAl gal = AccelLemma {base = gbase gal, step = gstep gal, conc = gconc gal}

addMaintain :: Term -> AccelLemma -> AccelLemma
addMaintain maintain al = al {step = FOL.andf [step al, maintain]}

addInv :: Variables -> Symbol -> Term -> AccelLemma -> AccelLemma
addInv vars prime inv al =
  AccelLemma
    { base = FOL.andf [base al, inv]
    , conc = FOL.andf [conc al, inv]
    , step = FOL.andf [step al, primeT vars prime inv]
    }

-- TODO? use indpendent variables somewhere??? Maybe this is something that is autodicsoverd (TODO at least a detailed comment)
preCond ::
     Config
  -> Heur
  -> Player
  -> Arena
  -> Loc
  -> SymSt
  -> Symbol
  -> AccelLemma
  -> IO (Either Term (Term, SyBo))
preCond conf heur player arena loc target prime lemma = do
  (arena, loc, loc', subs, target, prog) <- pure $ reducedLoopArena conf heur arena loc target prime
  lg conf ["Loop Scenario on", strS (locName arena) subs]
  prog <- pure $ Synt.returnOn target prog
  target <-
    pure
      $ set target loc'
      $ FOL.orf [target `get` loc, error "TODO: Invert primes or not?" (step lemma)]
  (stAcc, prog) <- pure $ iterA heur player arena target loc' prog
  let res = FOL.removePref prime $ stAcc `get` loc -- TODO check prime handeling!
  res <- SMT.simplify conf res
  let accelValue = FOL.andf [dom arena loc, conc lemma]
  let stepCond = accelValue `FOL.impl` res
  let baseCond = FOL.andf [dom arena loc, base lemma] `FOL.impl` (target `get` loc)
  -- TODO maybe make smt query, or extend shortcut or so!!
  if res == FOL.false
    then pure $ Left res
    else do
      holds <- SMT.valid conf stepCond
      if holds
        then do
          holds <- SMT.valid conf baseCond
          if holds
            then pure $ Right (accelValue, prog)
            else do
              lg conf ["Base condition failed"]
              pure $ Left res
        else pure $ Left res

---------------------------------------------------------------------------------------------------
-- Lemma Guessing based on polyhedra
---------------------------------------------------------------------------------------------------
data GenAccelLemma = GenAccelLemma
  { gbase :: Term
  , gstep :: Term
  , gstay :: Term
  , gconc :: Term
  }

-- TODO use heuristic better
lemmaGuess :: Heur -> Variables -> Symbol -> Term -> Maybe GenAccelLemma
lemmaGuess heur vars prime trg = do
  case fromPolyhedron vars prime (H.minEpsilon heur) <$> projectPolyhedra trg of
    [] -> Nothing
    gals -> Just $ galUnion gals

-- condition: all priming is the same!
galUnion :: [GenAccelLemma] -> GenAccelLemma
galUnion subs =
  GenAccelLemma
    { gbase = FOL.orfL subs gbase
    , gstay = FOL.andfL subs gstay
    , gconc = FOL.orfL subs gconc
    , gstep =
        FOL.orfL (singleOut subs) $ \(poly, others) -> FOL.andf $ gstep poly : map gstay others
    }

fromPolyhedron :: Variables -> Symbol -> Rational -> Polyhedron -> GenAccelLemma
fromPolyhedron vars prime epsilon poly =
  let ineqs = toIneqs poly
   in GenAccelLemma
        { gbase = FOL.andfL ineqs ineqGoal
        , gconc = FOL.true
        , gstay = FOL.andfL ineqs $ ineqStay vars prime
        , gstep =
            FOL.orfL (singleOut ineqs) $ \(ineq, others) ->
              FOL.andf [ineqStep vars prime epsilon ineq, FOL.andfL others (ineqStay vars prime)]
        }

ineqGoal :: Ineq Integer -> Term
ineqGoal (linComb, bounds) =
  let sum = sumTerm linComb
   in FOL.andf [inLow bounds sum, inUpp bounds sum]

singleOut :: [a] -> [(a, [a])]
singleOut = go []
  where
    go acc =
      \case
        [] -> []
        x:xr -> (x, acc ++ xr) : go (acc ++ [x]) xr

ineqStay :: Variables -> Symbol -> Ineq Integer -> Term
ineqStay vars prime (linComb, bounds) =
  let sum = sumTerm linComb
      sum' = primeT vars prime sum
   in FOL.orf
        [ ineqGoal (linComb, bounds)
        , FOL.andf [ltLow bounds sum, sum' `FOL.geqT` sum, inUpp bounds sum']
        , FOL.andf [gtUpp bounds sum, sum' `FOL.leqT` sum, inLow bounds sum']
        ]

ineqStep :: Variables -> Symbol -> Rational -> Ineq Integer -> Term
ineqStep vars prime epsilon (linComb, bounds) =
  let sum = sumTerm linComb
      sum' = primeT vars prime sum
   in FOL.orf
        [ ineqGoal (linComb, bounds)
        , FOL.andf [ltLow bounds sum, sum `ltEpsilon` sum', inUpp bounds sum']
        , FOL.andf [gtUpp bounds sum, sum' `ltEpsilon` sum, inLow bounds sum']
        ]
  where
    ltEpsilon t1 t2
      | (FOL.sorts t1 `Set.union` FOL.sorts t2) == Set.singleton FOL.SInt = t1 `FOL.ltT` t2
      | otherwise = t1 `FOL.ltT` FOL.addT [FOL.numberT epsilon, t2]

-- TODO: duplicate in UFLAcceleration!
primeT :: Variables -> Symbol -> Term -> Term
primeT vars prim =
  FOL.mapSymbol
    (\s ->
       if Vars.isStateVar vars s
         then prim ++ s
         else s)

-- TODO: move to polyhedra!
sumTerm :: [((Symbol, Sort), Integer)] -> Term
sumTerm = FOL.addT . map (\((v, s), c) -> FOL.multT [FOL.numberT c, FOL.var v s])

-- TODO: move to polyhedra!
inLow :: Interval -> Term -> Term
inLow intv term =
  case lower intv of
    MinusInfinity -> FOL.true
    GTVal eq bound
      | eq -> term `FOL.geqT` FOL.numberT bound
      | otherwise -> term `FOL.gtT` FOL.numberT bound

-- TODO: move to polyhedra!
ltLow :: Interval -> Term -> Term
ltLow intv term =
  case lower intv of
    MinusInfinity -> FOL.false
    GTVal eq bound
      | eq -> term `FOL.ltT` FOL.numberT bound
      | otherwise -> term `FOL.leqT` FOL.numberT bound

-- TODO: move to polyhedra!
inUpp :: Interval -> Term -> Term
inUpp intv term =
  case upper intv of
    PlusInfinity -> FOL.true
    LTVal eq bound
      | eq -> term `FOL.leqT` FOL.numberT bound
      | otherwise -> term `FOL.ltT` FOL.numberT bound

-- TODO: move to polyhedra!
gtUpp :: Interval -> Term -> Term
gtUpp intv term =
  case upper intv of
    PlusInfinity -> FOL.false
    LTVal eq bound
      | eq -> term `FOL.gtT` FOL.numberT bound
      | otherwise -> term `FOL.geqT` FOL.numberT bound
---------------------------------------------------------------------------------------------------
