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

import qualified Data.List as List

---------------------------------------------------------------------------------------------------
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.Interval (gtUpp, inLow, inUpp, ltLow)
import Issy.Logic.Polyhedra
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Base
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H
import Issy.Solver.Acceleration.LoopScenario (reducedLoopArena)
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra (justOn)
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- Top-level acceleration
---------------------------------------------------------------------------------------------------
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GGeoA" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  let prime = FOL.uniquePrefix "init_" $ usedSymbols arena
  res <- accelGAL conf heur player arena prime loc reach FOL.true
  case res of
    Just (conc, prog) -> lg conf ["Suceeded with", SMTLib.toString conc] $> (conc, prog)
    Nothing -> lg conf ["Failed"] $> (FOL.false, Synt.empty)

-- TODO: can this and accelReach be merged?
accelGAL ::
     Config -> Heur -> Player -> Arena -> Symbol -> Loc -> SymSt -> Term -> IO (Maybe (Term, SyBo))
accelGAL conf heur player arena prime loc reach inv = do
  (indeps, preComb) <- preCompGen conf heur player arena loc reach prime
  let gal = guessLemma heur (vars arena) indeps prime (reach `get` loc)
  case gal of
    [] -> lg conf ["Could not guess any lemma"] $> Nothing
    gals -> go preComb indeps gals
  where
    go _ _ [] = lg conf ["All lemma-tries failed"] $> Nothing
    go preComb indeps (gal:galr) = do
      lgGAL conf "Lemma try" gal
      res <- iter 0 inv gal
      case res of
        Just res -> lg conf ["Lemma try suceeded"] $> Just res
        Nothing -> do
          lg conf ["Lemma try failed"]
          go preComb indeps galr
        --
      where
        iter cnt inv gal
          | cnt > H.ggaIters heur = pure Nothing
          | otherwise = do
            lg conf ["Use invariant", SMTLib.toString inv, show cnt]
            let al = addInv (vars arena) inv $ galToAl gal
            (pre, preProg) <- preComb al
            check <- lemmaCond conf arena loc reach al pre
            case check of
              NotApplicable -> pure Nothing
              Applicable -> pure $ Just (pre, preProg) --TODO: add conclusion and so?
              Refine
                | cnt == H.ggaIters heur -> iter (cnt + 1) pre gal
                | otherwise -> do
                  lg conf ["Guess sublemma for", SMTLib.toString pre]
                  case guessLemmaSimple heur (vars arena) indeps prime pre of
                    [] -> iter (cnt + 1) pre gal
                    subGal:subGalR --TODO use more than one!
                     -> do
                      gal <- pure $ galChain (vars arena) gal subGal
                      lgGAL conf "Enhanced" gal
                                -- TODO: maybe some emptiness check??
                      iter (cnt + 1) inv gal

---------------------------------------------------------------------------------------------------
-- Attractor through loop arena
---------------------------------------------------------------------------------------------------
-- TODO: document!!
preCompGen ::
     Config
  -> Heur
  -> Player
  -> Arena
  -> Loc
  -> SymSt
  -> Symbol
  -> IO (Set Symbol, AccelLemma -> IO (Term, SyBo))
preCompGen conf heur player arena loc target prime = do
  (arena, loc, loc', subs, target, prog) <- pure $ reducedLoopArena conf heur arena loc target prime
  lg conf ["Loop Scenario on", strS (locName arena) subs]
  prog <- pure $ Synt.returnOn target prog
  indeps <- independentProgVars conf arena
  lg conf ["Independent state variables", strS id indeps]
  -- TODO deuglify
  pure
    ( indeps
    , \lemma -> do
        target <- pure $ set target loc' $ FOL.orf [target `get` loc, step lemma]
    -- Remark: we do not use independent variables, as their constrains are expected to be 
    -- found otherwise in the invariant generation iteration. This is beneficial as
    -- otherwise we usually do an underapproximating projection
        (stAcc, prog) <- iterA conf heur player arena target loc' prog
        let res = unprime lemma $ stAcc `get` loc
        res <- SMT.simplify conf res
        pure (res, prog))

-- | small three-valued data structure to indicate the resulf of checking the
-- conditions for acceleration lemma
data LemmaStatus
  = Applicable
 -- ^ all conditions hold
  | Refine
 -- ^ the step condtion failed but maybe a better invariant could do it
  | NotApplicable
 -- ^ the loop game result is false, or the base condition not applicable

-- | 'lemmaCond' check if the condition of a lemma holds.
lemmaCond :: Config -> Arena -> Loc -> SymSt -> AccelLemma -> Term -> IO LemmaStatus
lemmaCond conf arena loc target lemma loopGameResult = do
  let accelValue = FOL.andf [dom arena loc, conc lemma]
  let stepCond = accelValue `FOL.impl` loopGameResult
  let baseCond = FOL.andf [dom arena loc, base lemma] `FOL.impl` (target `get` loc)
  lg conf ["Loop game result", SMTLib.toString loopGameResult]
  holds <- SMT.sat conf loopGameResult
  if not holds
    then lg conf ["Precondition trivially false"] $> NotApplicable
    else do
      holds <- SMT.valid conf baseCond
      if not holds
        then lg conf ["Base condition failed"] $> NotApplicable
        else do
          holds <- SMT.valid conf stepCond
          if not holds
            then lg conf ["Step condition failed"] $> Refine
            else lg conf ["Lemma conditions hold"] $> Applicable

-- IO version of iterA, the organisation of those might be done 'a bit' better
-- TODO integrate summaries in a better way!
iterA :: Config -> Heur -> Player -> Arena -> SymSt -> Loc -> SyBo -> IO (SymSt, SyBo)
iterA conf heur player arena attr shadow =
  go (noVisits arena) (OL.fromSet (preds arena shadow)) attr
  where
    go vcnt open attr prog =
      case OL.pop open of
        Nothing -> pure (attr, prog)
        Just (l, open)
          | visits l vcnt < H.iterAMaxCPres heur -> do
            let new = cpre player arena attr l
            go
              (visit l vcnt)
              (preds arena l `OL.push` open)
              (SymSt.disj attr l new)
              (Synt.enforceTo l new attr prog)
          | otherwise -> go vcnt open attr prog

---------------------------------------------------------------------------------------------------
-- Lemma Guessing based on polyhedra
---------------------------------------------------------------------------------------------------
data GenAccelLemma = GenAccelLemma
  { gbase :: Term
  , gstep :: Term
  , gstay :: Term
  , gconc :: Term
  , gprime :: Symbol
  }

lgGAL :: Config -> String -> GenAccelLemma -> IO ()
lgGAL conf name gal = do
  lg conf ["GAL:", name]
  lg conf ["- base:", SMTLib.toString (gbase gal)]
  lg conf ["- stay:", SMTLib.toString (gstay gal)]
  lg conf ["- step:", SMTLib.toString (gstep gal)]
  lg conf ["- conc:", SMTLib.toString (gconc gal)]

-- TODO: can this be generalized module wise?
galToAl :: GenAccelLemma -> AccelLemma
galToAl gal = AccelLemma {base = gbase gal, step = gstep gal, conc = gconc gal, prime = gprime gal}

guessLemmaSimple :: Heur -> Variables -> Set Symbol -> Symbol -> Term -> [GenAccelLemma]
guessLemmaSimple heur vars indeps prime = mapMaybe gen . nontrivialPolyhedra
  where
    gen = fromPolyhedron vars indeps prime (H.minEpsilon heur)

-- TODO use heuristic better
guessLemma :: Heur -> Variables -> Set Symbol -> Symbol -> Term -> [GenAccelLemma]
guessLemma heur vars indeps prime trg =
  case mapMaybe gen (nontrivialPolyhedra trg) of
    [] -> []
    [l] -> [l]
    gals -> map galUnionsLex $ combs gals
  where
    gen = fromPolyhedron vars indeps prime (H.minEpsilon heur)
    combs = take 10 . filter (not . null) . permutationsUpTo 2 -- TODO: add heursitic values

permutationsUpTo :: Int -> [a] -> [[a]]
permutationsUpTo maxL =
  List.sortOn length . concatMap List.permutations . filter ((<= maxL) . length) . List.subsequences

-- condition: all priming is the same!, list not empty
galChain :: Variables -> GenAccelLemma -> GenAccelLemma -> GenAccelLemma
galChain vars main sub =
  GenAccelLemma
    { gbase = gbase main
    , gconc = FOL.andf [gconc main, gconc sub]
    , gstay = FOL.andf [gstay main, gstay sub]
    , gstep =
        FOL.orf
          [ FOL.andf [prm (gbase sub), gstep main]
          , FOL.andf [prm (FOL.neg (gbase sub)), gstay main, gstep sub]
          ]
    , gprime = gprime main
    }
  where
    prm = primeT vars (gprime main)

-- condition: all priming is the same!, list not empty
galUnionLex :: GenAccelLemma -> GenAccelLemma -> GenAccelLemma
galUnionLex gal1 gal2 =
  GenAccelLemma
    { gbase = FOL.orf [gbase gal1, gbase gal2]
    , gconc = FOL.orf [gconc gal1, gconc gal2]
    , gstay = FOL.andf [gstay gal1, gstay gal2]
    , gstep = FOL.orf [gstep gal1, FOL.andf [gstay gal1, gstep gal2]]
    , gprime = gprime gal1
    }

-- condition: all priming is the same!, list not empty
galUnionsLex :: [GenAccelLemma] -> GenAccelLemma
galUnionsLex = go
  where
    go [] = error "assertion"
    go [x] = x
    go (x:xr) = galUnionLex x (go xr)

-- condition: all priming is the same!, list not empty
galUnion :: [GenAccelLemma] -> GenAccelLemma
galUnion subs =
  GenAccelLemma
    { gbase = FOL.orfL subs gbase
    , gstay = FOL.andfL subs gstay
    , gconc = FOL.orfL subs gconc
    , gstep =
        FOL.orfL (singleOut subs) $ \(poly, others) -> FOL.andf $ gstep poly : map gstay others
    , gprime = gprime (head subs)
    }

fromPolyhedron ::
     Variables -> Set Symbol -> Symbol -> Rational -> (Polyhedron, Set Term) -> Maybe GenAccelLemma
fromPolyhedron vars indeps prime epsilon (poly, sideConstr) =
  let ineqs = toIneqs poly
      someDeps = any (any ((`notElem` indeps) . (fst . fst)) . fst) ineqs --TODO: improve by filter on idividual terms!
      inv = FOL.andf $ Set.toList sideConstr -- Remark: this is fairly simplistic, and could be enhanced
   in justOn someDeps
        $ GenAccelLemma
            { gbase = FOL.andf [inv, FOL.andfL ineqs ineqGoal]
            , gconc = inv
            , gstay = FOL.andf [inv, FOL.andfL ineqs $ ineqStay vars prime]
            , gstep =
                FOL.orfL (singleOut ineqs) $ \(ineq, others) ->
                  FOL.andf
                    [inv, ineqStep vars prime epsilon ineq, FOL.andfL others (ineqStay vars prime)]
            , gprime = prime
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
        -- Remark: Note that priming is "inverted" (previous part is primed)
        -- as we do a backward computation
   in FOL.orf
        [ ineqGoal (linComb, bounds)
        , FOL.andf [ltLow bounds sum, sum `FOL.geqT` sum', inUpp bounds sum']
        , FOL.andf [gtUpp bounds sum, sum `FOL.leqT` sum', inLow bounds sum']
        ]

ineqStep :: Variables -> Symbol -> Rational -> Ineq Integer -> Term
ineqStep vars prime epsilon (linComb, bounds) =
  let sum = sumTerm linComb
      sum' = primeT vars prime sum
        -- Remark: Note that priming is "inverted" (previous part is primed)
        -- as we do a backward computation
   in FOL.orf
        [ ineqGoal (linComb, bounds)
        , FOL.andf [ltLow bounds sum, sum' `ltEpsilon` sum, inUpp bounds sum']
        , FOL.andf [gtUpp bounds sum, sum `ltEpsilon` sum', inLow bounds sum']
        ]
  where
    ltEpsilon t1 t2
      | (FOL.sorts t1 `Set.union` FOL.sorts t2) == Set.singleton FOL.SInt = t1 `FOL.ltT` t2
      | otherwise = t1 `FOL.ltT` FOL.addT [FOL.numberT epsilon, t2]
---------------------------------------------------------------------------------------------------
