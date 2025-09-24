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
import qualified Data.List as List
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
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- Top-level acceleration
---------------------------------------------------------------------------------------------------
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GGeoA" conf
  accelGAL conf heur player arena loc reach

accelGAL :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelGAL conf heur player arena loc reach = do
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  (indeps, preComb) <- preCompGen conf heur player arena loc reach prime
  let gal = guessLemma heur (vars arena) indeps prime (reach `get` loc)
  case gal of
    [] -> lg conf ["Could not guess any lemma"] $> (FOL.false, Synt.empty)
    gals -> do
      res <- go preComb indeps gals
      case res of
        Nothing -> lg conf ["Failed"] $> (FOL.false, Synt.empty)
        Just (conc, prog) -> lg conf ["Suceeded with", SMTLib.toString conc] $> (conc, prog)
  where
    -- Priming symbol for the previous state in the lemma
    prime = FOL.uniquePrefix "init_" $ usedSymbols arena
    -- Try out different lemmas
    go _ _ [] = lg conf ["All lemma-tries failed"] $> Nothing
    go preComb indeps (gal:galr) = do
      lgGAL conf "Lemma try" gal
      res <- iter 0 FOL.true gal
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
                -- TODO: Proper heuristic
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
guessLemmaSimple :: Heur -> Variables -> Set Symbol -> Symbol -> Term -> [GenAccelLemma]
guessLemmaSimple heur vars indeps prime = concatMap gen . nontrivialPolyhedra
  where
    gen = fromPolyhedron vars indeps prime (H.minEpsilon heur)

-- TODO use heuristic better
guessLemma :: Heur -> Variables -> Set Symbol -> Symbol -> Term -> [GenAccelLemma]
guessLemma heur vars indeps prime trg =
  case filter (not . null) $ map gen (nontrivialPolyhedra trg) of
    [] -> []
    [l] -> l
    gals -> concatMap (map galUnionsLex . listProduct) $ reverse $ combs gals
  where
    gen = fromPolyhedron vars indeps prime (H.minEpsilon heur)
    combs = take 10 . filter (not . null) . permutationsUpTo 2 -- TODO: add heursitic values

-- TODO: this neeeds to be documents why stuff happens
fromPolyhedron ::
     Variables -> Set Symbol -> Symbol -> Rational -> (Polyhedron, Set Term) -> [GenAccelLemma]
fromPolyhedron vars indeps prime epsilon (poly, sideConstr) =
  let (statics, gals) = partitionMaybe (ineqGal vars indeps prime epsilon) $ toIneqs poly
      invFor staticGals =
        FOL.andf $ Set.toList sideConstr ++ map ineqGoal statics ++ map gbase staticGals -- Remark: this is fairly simplistic, and could be enhanced
   in if null gals
        then []
        else map (\(rank, keep) -> addInvariant (invFor keep) (galIntersections vars rank))
               $ filter (not . null . fst)
               $ partitionsUpTo 2 gals -- TODO heursitic instead of 2

ineqGal :: Variables -> Set Symbol -> Symbol -> Rational -> Ineq Integer -> Maybe GenAccelLemma
ineqGal vars indeps prime epsilon (linComb, bounds)
  | all ((`elem` indeps) . fst . fst) linComb = Nothing
  | otherwise =
    let sum = sumTerm linComb
        sum' = primeT vars prime sum
                -- Remark: Note that priming is "inverted" (previous part is primed)
                -- as we do a backward computation
     in Just
          $ GenAccelLemma
              { gprime = prime
              , gbase = ineqGoal (linComb, bounds)
              , gstay =
                  FOL.orf
                    [ ineqGoal (linComb, bounds)
                    , FOL.andf [ltLow bounds sum, sum `FOL.geqT` sum', inUpp bounds sum']
                    , FOL.andf [gtUpp bounds sum, sum `FOL.leqT` sum', inLow bounds sum']
                    ]
              , gstep =
                  FOL.orf
                    [ ineqGoal (linComb, bounds)
                    , FOL.andf [ltLow bounds sum, sum' `ltEpsilon` sum, inUpp bounds sum']
                    , FOL.andf [gtUpp bounds sum, sum `ltEpsilon` sum', inLow bounds sum']
                    ]
              , gconc = FOL.true
              }
  where
    ltEpsilon t1 t2
      | (FOL.sorts t1 `Set.union` FOL.sorts t2) == Set.singleton FOL.SInt = t1 `FOL.ltT` t2
      | otherwise = t1 `FOL.ltT` FOL.addT [FOL.numberT epsilon, t2]

ineqGoal :: Ineq Integer -> Term
ineqGoal (linComb, bounds) =
  let sum = sumTerm linComb
   in FOL.andf [inLow bounds sum, inUpp bounds sum]

---------------------------------------------------------------------------------------------------
-- General Acceleration Lemmas
-- TODO: can this be generalized module wise?
---------------------------------------------------------------------------------------------------
data GenAccelLemma = GenAccelLemma
  { gbase :: Term
  , gstep :: Term
  , gstay :: Term
  , gconc :: Term
  , gprime :: Symbol
  }

galToAl :: GenAccelLemma -> AccelLemma
galToAl gal = AccelLemma {base = gbase gal, step = gstep gal, conc = gconc gal, prime = gprime gal}

data Combinator a
  = CBase a
  | CInv Term (Combinator a)
  | CChain (Combinator a) (Combinator a)
  | CUnionLex [Combinator a]
  | CIntersection [Combinator a]

toGAL :: Variables -> (a -> GenAccelLemma) -> Combinator a -> GenAccelLemma
toGAL vars mkGAL = go
  where
    go =
      \case
        CBase a -> mkGAL a
        CInv inv a -> addInvariant inv (go a)
        CChain a b -> galChain vars (go a) (go b)
        CUnionLex gs -> galUnionsLex (map go gs)
        CIntersection gs -> galIntersections vars (map go gs)

addInvariant :: Term -> GenAccelLemma -> GenAccelLemma
addInvariant inv gal =
  gal
    { gbase = FOL.andf [gbase gal, inv]
    , gconc = FOL.andf [gconc gal, inv]
    , gstay = FOL.andf [gstay gal, inv]
    , gstep = FOL.andf [gstep gal, inv]
    }

lgGAL :: Config -> String -> GenAccelLemma -> IO ()
lgGAL conf name gal = do
  lg conf ["GAL:", name]
  lg conf ["- base:", SMTLib.toString (gbase gal)]
  lg conf ["- stay:", SMTLib.toString (gstay gal)]
  lg conf ["- step:", SMTLib.toString (gstep gal)]
  lg conf ["- conc:", SMTLib.toString (gconc gal)]

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
galUnionsLex [] = error "assert: cannot compute empty list of GAL unions"
galUnionsLex (x:xr) = foldr galUnionLex x xr

-- condition: all priming is the same!, list not empty
galIntersections :: Variables -> [GenAccelLemma] -> GenAccelLemma
galIntersections vars gals =
  let newConc = FOL.andfL gals gconc
      newStep =
        FOL.orfL (singleOut gals) $ \(gal, others) ->
          FOL.andf [gstep gal, prm (FOL.neg (gbase gal)), FOL.andfL others gstay]
   in GenAccelLemma
        { gbase = FOL.andfL gals gbase
        , gstay = FOL.andfL gals gstay
        , gstep = FOL.andf [newConc, newStep]
        , gconc = newConc
        , gprime = gprime (head gals)
        }
  where
    prm = primeT vars (gprime (head gals))

---------------------------------------------------------------------------------------------------
-- Generic Functions
---------------------------------------------------------------------------------------------------
permutationsUpTo :: Int -> [a] -> [[a]]
permutationsUpTo maxL =
  List.sortOn length . concatMap List.permutations . filter ((<= maxL) . length) . List.subsequences

singleOut :: [a] -> [(a, [a])]
singleOut = go []
  where
    go acc =
      \case
        [] -> []
        x:xr -> (x, acc ++ xr) : go (acc ++ [x]) xr

-- 'paritionsUpTo' computes all partitions of the given list with a bound on the lenght of the first
-- partitioning
partitionsUpTo :: Int -> [a] -> [([a], [a])]
partitionsUpTo maxL = map (\(_, as, bs) -> (as, bs)) . go
  where
    go [] = [(0, [], [])]
    go (x:xr) =
      flip concatMap (go xr) $ \(n, as, bs) ->
        if n >= maxL
          then [(n, as, x : bs)]
          else [(n, as, x : bs), (n + 1, x : as, bs)]

-- 'listProduct' computes the n-ary cartesian product over a list
listProduct :: [[a]] -> [[a]]
listProduct [] = []
listProduct [xs] = map (: []) xs
listProduct (xs:yr) = concatMap (\y -> map (: y) xs) $ listProduct yr

-- TODO: Move to Prelude or so Utils.Extra!
partitionMaybe :: (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe _ [] = ([], [])
partitionMaybe f (x:xr) =
  case f x of
    Nothing -> first (x :) $ partitionMaybe f xr
    Just y -> second (y :) $ partitionMaybe f xr
---------------------------------------------------------------------------------------------------
