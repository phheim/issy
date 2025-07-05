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
import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, extendAcceleration, setName)
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.Acceleration.Strengthening (strengthenBool)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra (andM, orM)
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

import Issy.Logic.Polyhedra

---------------------------------------------------------------------------------------------------
-- Top-level acceleration
---------------------------------------------------------------------------------------------------
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GGeoA" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  accelGAL conf player arena loc reach FOL.true FOL.true

accelGAL :: Config -> Player -> Arena -> Loc -> SymSt -> Term -> Term -> IO (Term, SyBo)
accelGAL conf player arena loc = go (0 :: Integer)
  where
    prime = error "TODO PRIME: must be given as part of maintain!!"
    -- TODO: steamline & log & extraction!!!
    go depth reach maintain inv = do
          let gal = lemmaGuess conf (error "TODO: HEUR") (vars arena) (error "TODO: prime") (reach `get` loc)
          case gal of 
            Nothing -> pure (FOL.false, error "TODO:empty")
            Just gal -> do
                  --TODO: preCond does not find invariant on base, this has to be taken care of like in the loop sceneration or so, maybe we could use the additional info of the polyhera! Maybe build up new projection function?
                  let al = addMaintain maintain $ addInv (vars arena) prime inv $ galToAl gal
                  pre <- preCond conf player arena loc reach al
                  unsat <- SMT.unsat conf pre
                  if unsat 
                    then pure (FOL.false, error "TODO:empty")
                    else do included <- SMT.valid conf $ FOL.impl inv pre
                            if included 
                              then pure $ (FOL.andf [conc al, inv], error "TODO") -- TODO: simplify?
                              else if error "TODO: do nesting?"
                                    then go (depth + 1) (error "TODO: {l -> pre}") (FOL.andf[maintain, gstay gal]) inv
                                         -- TODO: add second limititing
                                    else go depth reach maintain pre

---------------------------------------------------------------------------------------------------
-- Attractor through loop arena
---------------------------------------------------------------------------------------------------
-- TODO: can this be generalized?
data AccelLemma = AccelLemma 
    { base :: Term
    , step :: Term
    , conc :: Term
    }

galToAl :: GenAccelLemma -> AccelLemma 
galToAl gal = AccelLemma { base = gbase gal, step = gstep gal, conc = gconc gal } 

addMaintain :: Term -> AccelLemma -> AccelLemma
addMaintain maintain al = al { step = FOL.andf[step al, maintain] }

addInv :: Variables -> Symbol -> Term -> AccelLemma -> AccelLemma
addInv vars prime inv al = 
    AccelLemma 
    { base = FOL.andf [base al, inv]
    , conc = FOL.andf [conc al, inv]
    , step = FOL.andf [step al, primeT vars prime inv]  
    }

preCond :: Config -> Player -> Arena -> Loc -> SymSt -> AccelLemma -> IO Term
preCond = error "TODO IMPLEMENT"

---------------------------------------------------------------------------------------------------
-- Lemma Guessing based on polyhedra
---------------------------------------------------------------------------------------------------
data GenAccelLemma = GenAccelLemma
  { gbase :: Term
  , gstep :: Term
  , gstay :: Term
  , gconc :: Term
  }

-- TODO use heuristic
lemmaGuess :: Config -> Heur -> Variables -> Symbol -> Term -> Maybe GenAccelLemma
lemmaGuess conf heur vars prime trg = do 
    case fromPolyhedron vars prime <$> projectPolyhedra trg of
        [] -> Nothing
        gals -> Just $ galUnion gals

-- condition: all priming is the same!
galUnion :: [GenAccelLemma] -> GenAccelLemma
galUnion subs = 
    GenAccelLemma 
    { gbase = FOL.orfL subs gbase
    , gstay = FOL.andfL subs gstay
    , gconc = FOL.orfL subs gconc 
    , gstep = FOL.orfL (singleOut subs) $ \(poly, others) -> FOL.andf $ gstep poly : map gstay others
    }

fromPolyhedron :: Variables -> Symbol -> Polyhedron -> GenAccelLemma
fromPolyhedron vars prime poly = 
 let ineqs = toIneqs poly
  in GenAccelLemma 
        { gbase = FOL.andfL ineqs ineqGoal
        , gconc = FOL.true
        , gstay = FOL.andfL ineqs $ ineqStay vars prime
        , gstep = FOL.orfL (singleOut ineqs) $ \(ineq, others) -> FOL.andf [ineqStep vars prime ineq, FOL.andfL others (ineqStay vars prime)]
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
                x:xr -> [(x,  acc ++ xr)] ++ go (acc ++ [x]) xr

-- TODO: merge step and stay and add more readable construction methods
ineqStay :: Variables -> Symbol -> Ineq Integer -> Term
ineqStay vars prime (linComb, bounds) =
    let sum = sumTerm linComb
        sum' = primeT vars prime sum
     in FOL.orf [ ineqGoal (linComb, bounds)
                , FOL.andf [ltLow bounds sum, sum' `FOL.geqT` sum, inUpp bounds sum']
                , FOL.andf [gtUpp bounds sum, sum' `FOL.leqT` sum, inLow bounds sum']
                ] 

ineqStep :: Variables -> Symbol -> Ineq Integer -> Term
ineqStep vars prime (linComb, bounds) =
    let sum = sumTerm linComb
        sum' = primeT vars prime sum
     in FOL.orf [ ineqGoal (linComb, bounds)
                -- TODO: add epsilon
                , FOL.andf [ltLow bounds sum, sum' `FOL.gtT` sum, inUpp bounds sum']
                , FOL.andf [gtUpp bounds sum, sum' `FOL.ltT` sum, inLow bounds sum']
                ] 

epsilonDiff :: Term -> Term -> Term
epsilonDiff = error "TODO"

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
