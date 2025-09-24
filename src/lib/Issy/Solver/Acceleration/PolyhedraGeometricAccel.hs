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

-- TODO: switch lemma search to BFS instead of DFS
accelGAL :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelGAL conf heur player arena loc reach = do
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  (indeps, preComb) <- preCompGen conf heur player arena loc reach prime
  let gals = guessLemma heur indeps (reach `get` loc)
  when (null gals) $ lg conf ["Could not guess any lemma"]
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
      lg conf ["GAL try", polyLemmaToStr gal]
      res <- iter 0 FOL.true gal
      case res of
        Just res -> lg conf ["Lemma try suceeded"] $> Just res
        Nothing -> lg conf ["Lemma try failed"] >> go preComb indeps galr
        -- Try out different invaraints
      where
        iter cnt inv gal
          | cnt > H.ggaIters heur = pure Nothing
          | otherwise = do
            lg conf ["Use invariant", SMTLib.toString inv, show cnt]
            let al = polyLemma (vars arena) prime (H.minEpsilon heur) $ combInv inv gal
            (pre, preProg) <- preComb al
            check <- lemmaCond conf arena loc reach al pre
            case check of
              NotApplicable -> pure Nothing
              Applicable -> pure $ Just (conc al, preProg)
              Refine
                -- TODO: Proper heuristic
                | cnt == H.ggaIters heur -> iter (cnt + 1) pre gal
                | otherwise -> do
                  lg conf ["Guess sublemma for", SMTLib.toString pre]
                  trySublemmas $ guessLemmaSimple heur indeps pre
          where
            trySublemmas =
              \case
                [] -> lg conf ["No more sublemmas to try"] $> Nothing
                subGal:rest -> do
                  gal <- pure $ combChain gal subGal
                  lg conf ["GAL enhance to", polyLemmaToStr gal]
                  res <- iter (cnt + 1) inv gal
                  case res of
                    Just res -> pure $ Just res
                    Nothing -> trySublemmas rest

--lemmaTry :: PolyLemma -> LemmaTry
--lemmaTry lemma = LemmaTry {lemmaCom = lemma, iterCnt = 0, nestCnt = 0}
--
--data LemmaTry = LemmaTry 
--    {   lemmaComb :: PolyLemma
--    ,   iterCnt :: Int
--    ,   nestCnt :: Int
--    }
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
iterA _ heur player arena attr shadow = go (noVisits arena) (OL.fromSet (preds arena shadow)) attr
  where
    go vcnt open attr prog =
      case OL.pop open of
        Nothing -> pure (attr, prog)
        Just (l, open)
          | visits l vcnt < H.iterAMaxCPres heur -> do
            -- TODO add nesting
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
type PolyLemma = Combinator (Ineq Integer)

polyLemmaToStr :: PolyLemma -> String
polyLemmaToStr = combToStr $ ("Rank to " ++) . SMTLib.toString . ineqToTerm

guessLemmaSimple :: Heur -> Set Symbol -> Term -> [PolyLemma]
guessLemmaSimple heur indeps = concatMap (fromPolyhedron heur indeps) . nontrivialPolyhedra

-- TODO use heuristic better
guessLemma :: Heur -> Set Symbol -> Term -> [PolyLemma]
guessLemma heur indeps trg =
  case filter (not . null) $ map gen (nontrivialPolyhedra trg) of
    [] -> []
    [l] -> l
    gals -> concatMap (map combLexiUnion . listProduct) $ combs gals
  where
    gen = fromPolyhedron heur indeps
    combs =
      reverse
        . take (H.ggaMaxLexiUnion heur)
        . filter (not . null)
        . permutationsUpTo (H.ggaMaxLexiUnionSize heur)

-- TODO: this neeeds to be documents why stuff happens
fromPolyhedron :: Heur -> Set Symbol -> (Polyhedron, Set Term) -> [PolyLemma]
fromPolyhedron heur indeps (poly, sideConstr) =
  let (rankIneqs, invIneqs) = List.partition (potentialGAL indeps) $ toIneqs poly
      invFor keep = FOL.andf $ Set.toList sideConstr ++ map ineqToTerm (invIneqs ++ keep)
   in map (\(rank, keep) -> combInv (invFor keep) (combIntersect (map combBase rank)))
        $ filter (not . null . fst)
        $ partitionsUpTo (H.ggaMaxIntersect heur) rankIneqs

potentialGAL :: Set Symbol -> Ineq Integer -> Bool
potentialGAL indeps = any ((`notElem` indeps) . fst . fst) . fst

polyLemma :: Variables -> Symbol -> Rational -> PolyLemma -> AccelLemma
polyLemma vars prime epsilon = toLemma vars $ ineqGal vars prime epsilon

ineqGal :: Variables -> Symbol -> Rational -> Ineq Integer -> AccelLemma
ineqGal vars primeSym epsilon (linComb, bounds) =
  let sum = sumTerm linComb
      sum' = primeT vars primeSym sum
                -- Remark: Note that priming is "inverted" (previous part is primed)
                -- as we do a backward computation
   in AccelLemma
        { prime = primeSym
        , base = ineqToTerm (linComb, bounds)
        , stay =
            FOL.orf
              [ ineqToTerm (linComb, bounds)
              , FOL.andf [ltLow bounds sum, sum `FOL.geqT` sum', inUpp bounds sum']
              , FOL.andf [gtUpp bounds sum, sum `FOL.leqT` sum', inLow bounds sum']
              ]
        , step =
            FOL.orf
              [ ineqToTerm (linComb, bounds)
              , FOL.andf [ltLow bounds sum, sum' `ltEpsilon` sum, inUpp bounds sum']
              , FOL.andf [gtUpp bounds sum, sum `ltEpsilon` sum', inLow bounds sum']
              ]
        , conc = FOL.true
        }
  where
    ltEpsilon t1 t2
      | (FOL.sorts t1 `Set.union` FOL.sorts t2) == Set.singleton FOL.SInt = t1 `FOL.ltT` t2
      | otherwise = t1 `FOL.ltT` FOL.addT [FOL.numberT epsilon, t2]

---------------------------------------------------------------------------------------------------
-- Generic Functions
---------------------------------------------------------------------------------------------------
permutationsUpTo :: Int -> [a] -> [[a]]
permutationsUpTo maxL =
  List.sortOn length . concatMap List.permutations . filter ((<= maxL) . length) . List.subsequences

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
---------------------------------------------------------------------------------------------------
