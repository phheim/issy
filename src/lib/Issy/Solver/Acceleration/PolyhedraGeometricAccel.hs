---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Solver.Acceleration.PolyhedraGeometricAccel
-- Description : Implementaion of the general version of geometric acceleration based on polyhedra
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, MultiWayIf #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.PolyhedraGeometricAccel
  ( accelReach
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.List as List
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (extendAcceleration)
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
import qualified Issy.Utils.OpenList as OL
import qualified Issy.Utils.PrioQueue as PQ

---------------------------------------------------------------------------------------------------
-- Top-level acceleration
---------------------------------------------------------------------------------------------------
-- | 'accelReach' does reachability acceleration with a polyhedra-based method
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GGeoA" conf
  accelGAL conf heur player arena loc reach

-- | 'accelGAL' is the top-level function which does the main search of the
-- polyhedra-based acceleration
accelGAL :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelGAL conf heur player arena loc reach = do
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  (indeps, preComb) <- preCompGen conf heur player arena loc reach prime
  let gals = guessLemma heur indeps (reach `get` loc)
  when (null gals) $ lg conf ["Could not guess any lemma"]
  searchLemma preComb indeps gals
  where
    -- Priming symbol for the previous state in the lemma
    prime = FOL.uniquePrefix "init_" $ usedSymbols arena
    -- Search for lemmas with a priority queue
    searchLemma preComb indeps gals = search Nothing $ PQ.fromList searchKeyInit gals
      where
        search currSolution queue =
          case PQ.pop queue of
            Nothing ->
              case currSolution of
                Nothing -> lg conf ["Did not find any applicable lemma!"] $> (FOL.false, Synt.empty)
                Just sol -> pure sol
            Just (sk, lemmaComb, queue) -> do
              let lemma = polyLemma (vars arena) prime (H.minEpsilon heur) lemmaComb
              better <- conc lemma `couldBeBetter` currSolution
              if better
                then do
                  lg conf ["Try", polyLemmaToStr lemmaComb]
                  check <- preComb lemma
                  case check of
                    Applicable preProg -> do
                      lg conf ["Found", SMTLib.toString (conc lemma)]
                      if conc lemma == FOL.true
                        then pure (conc lemma, preProg)
                        else search (Just (conc lemma, preProg)) queue
                    NotApplicable -> search currSolution queue
                    Refine pre ->
                      let queueA
                            | doRefine heur sk = PQ.push (skRefine sk) (combInv pre lemmaComb) queue
                            | otherwise = queue
                          queueB
                            | doNest heur sk =
                              let subLemmas =
                                    map (combChain lemmaComb) $ guessLemmaSimple heur indeps pre
                               in PQ.pushs (skNest sk) subLemmas queueA
                            | otherwise = queueA
                       in search currSolution queueB
                else search currSolution queue
        -- Check if the conclusion could be better than the current result
        couldBeBetter _ Nothing = pure True
        couldBeBetter new (Just (res, _)) =
          SMT.sat conf $ FOL.andf [new, FOL.neg res, dom arena loc]

---------------------------------------------------------------------------------------------------
-- Priority for search guidance
---------------------------------------------------------------------------------------------------
data SearchKey = SearchKey
  { refinementCnt :: Int
  , nestingCnt :: Int
  } deriving (Eq, Show)

-- The order here is important as larger 'SearchKey's will be tried first!
instance Ord SearchKey where
  compare skA skB =
    if | nestingCnt skA < nestingCnt skB -> GT
       | nestingCnt skA > nestingCnt skB -> LT
       | refinementCnt skA < refinementCnt skB -> GT
       | refinementCnt skA > refinementCnt skB -> LT
       | otherwise -> EQ

searchKeyInit :: SearchKey
searchKeyInit = SearchKey {refinementCnt = 0, nestingCnt = 0}

doRefine :: Heur -> SearchKey -> Bool
doRefine heur sk = refinementCnt sk <= H.ggaIters heur

skRefine :: SearchKey -> SearchKey
skRefine sk = sk {refinementCnt = refinementCnt sk + 1}

doNest :: Heur -> SearchKey -> Bool
doNest heur sk = nestingCnt sk <= H.ggaDepth heur

skNest :: SearchKey -> SearchKey
skNest sk = sk {nestingCnt = nestingCnt sk + 1}

---------------------------------------------------------------------------------------------------
-- Attractor through loop arena
---------------------------------------------------------------------------------------------------
-- | small three-valued data structure to indicate the resulf of checking the
-- conditions for an acceleration lemma
data LemmaStatus
  = Applicable SyBo
 -- ^ all conditions hold with resulting program
  | Refine Term
 -- ^ the step condtion failed but maybe a better invariant could do it
  | NotApplicable
 -- ^ the loop game result is false, or the base condition not applicable

-- | 'lemmaCond' check if the condition of a lemma holds on a specific loop game result
lemmaCond :: Config -> Arena -> Loc -> SymSt -> AccelLemma -> Term -> SyBo -> IO LemmaStatus
lemmaCond conf arena loc target lemma loopGameResult prog = do
  let stepCond = FOL.andf [dom arena loc, conc lemma] `FOL.impl` loopGameResult
  let baseCond = FOL.andf [dom arena loc, base lemma] `FOL.impl` (target `get` loc)
  lgd conf ["Loop game result", SMTLib.toString loopGameResult]
  holds <- SMT.sat conf loopGameResult
  if not holds
    then lgd conf ["Precondition trivially false"] $> NotApplicable
    else do
      holds <- SMT.valid conf baseCond
      if not holds
        then lgd conf ["Base condition failed"] $> NotApplicable
        else do
          holds <- SMT.valid conf stepCond
          if not holds
            then lgd conf ["Step condition failed"] $> Refine loopGameResult
            else lgd conf ["Lemma conditions hold"] $> Applicable prog

-- | 'preCompGen' is responsible for computing a pass of an acceleration lemma through a loop 
-- game. In order to avoid dublicate computation of the loop game and independent variables.
-- preCompGen is a generator function, i.e. it return a function that compute the pass of a
-- lemma through a loop game and the check of conditions (in addition to the independen variables).
preCompGen ::
     Config
  -> Heur
  -> Player
  -> Arena
  -> Loc
  -> SymSt
  -> Symbol
  -> IO (Set Symbol, AccelLemma -> IO LemmaStatus)
preCompGen conf heur player arena loc target prime = do
  (arena, loc, loc', subs, target, prog) <- pure $ reducedLoopArena conf heur arena loc target prime
  lg conf ["Loop Scenario on", strS (locName arena) subs]
  prog <- pure $ Synt.returnOn target prog
  indeps <- independentProgVars conf arena
  lg conf ["Independent state variables", strS id indeps]
  pure
    ( indeps
    , \lemma -> do
        target <- pure $ set target loc' $ FOL.orf [target `get` loc, step lemma]
    -- Remark: we do not use independent variables here , as their constrains are expected to be 
    -- found otherwise in the invariant generation iteration. This is beneficial as
    -- otherwise we usually do an underapproximating projection
        (stAcc, prog) <- iterA conf heur player arena target loc' prog
        let res = unprime lemma $ stAcc `get` loc
        res <- SMT.simplify conf res
        lemmaCond conf arena loc target lemma res prog)

-- | 'iterA' underappoximating computation of an attractor
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
            -- Remark: here we could still only add the predcessors locations if 
            -- things changed however, it will often not be relevant in most cases
            go
              (visit l vcnt)
              (preds arena l `OL.push` open)
              (SymSt.disj attr l new)
              (Synt.enforceTo l new attr prog)
          | visits l vcnt == H.iterAMaxCPres heur && extendAcceleration conf && arena `cyclicIn` l -> do
            lg conf ["Nest acceleration in", locName arena l]
            attr <- SymSt.simplify conf attr
            (accelRes, accelProg) <- accelReach conf heur player arena l attr
            if accelRes == FOL.false
              then do
                lg conf ["Nesting failed"]
                go (visit l vcnt) open attr prog
              else do
                lg conf ["Nesting succeeded"]
                go
                  (visit l vcnt)
                  (preds arena l `OL.push` open)
                  (SymSt.disj attr l accelRes)
                  (Synt.callOn l accelRes accelProg prog)
          | otherwise -> go vcnt open attr prog

---------------------------------------------------------------------------------------------------
-- Lemma Guessing based on polyhedra
---------------------------------------------------------------------------------------------------
type PolyLemma = Combinator (Ineq Integer)

polyLemmaToStr :: PolyLemma -> String
polyLemmaToStr = combToStr $ SMTLib.toString . ineqToTerm

guessLemmaSimple :: Heur -> Set Symbol -> Term -> [PolyLemma]
guessLemmaSimple heur indeps = concatMap (fromPolyhedron heur indeps) . nontrivialPolyhedra

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
