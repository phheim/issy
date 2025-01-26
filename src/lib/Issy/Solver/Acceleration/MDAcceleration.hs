-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Solver.Acceleration.MDAcceleration
  ( accelReach
  ) where

-------------------------------------------------------------------------------
import Control.Monad (filterM, unless)
import Data.Bifunctor (second)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

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
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

-------------------------------------------------------------------------------
-- It assume that the arena is cycic in the location it accelerates.
accelReach :: Config -> Heur -> Player -> Arena -> Loc -> SymSt -> IO (Term, SyBo)
accelReach conf heur player arena loc reach = do
  conf <- pure $ setName "GeoAc" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  let prime = FOL.uniquePrefix "init_" $ usedSymbols arena
  -- 0. Compute loop sceneario
  (arena, loc, loc', reach, fixInv, prog) <- loopScenario conf heur arena loc reach prime
  -- 1. Guess lemma
  lemma <- lemmaGuess conf heur prime player arena (reach `get` loc)
  case lemma of
    Nothing -> do
      lg conf ["Lemma guessing failed"]
      pure (FOL.false, Synt.empty)
    Just (base, step, conc) -> do
      lg
        conf
        [ "Lemma guessing succeded with"
        , SMTLib.toString base
        , SMTLib.toString step
        , SMTLib.toString conc
        ]
      -- 1.5 Check base condition
      baseCond <-
        SMT.valid conf
          $ Vars.forallX (vars arena)
          $ FOL.andf [dom arena loc, base] `FOL.impl` (reach `get` loc)
      unless baseCond $ error "assert: the base should be computed that this holds"
        -- 2. try a few explicit iterations to find invariant
      invRes <-
        tryFindInv conf heur prime player arena (base, step, conc) (loc, loc') fixInv reach prog
      case invRes of
        Right (conc, prog) -> do
          lg conf ["Invariant iteration resulted in", SMTLib.toString conc]
          pure (conc, prog)
        Left overApprox -> do
          lg conf ["Invariant iteration failed"]
          pure (FOL.false, Synt.empty)

-------------------------------------------------------------------------------
-- Invariant Iteration
-------------------------------------------------------------------------------
tryFindInv ::
     Config
  -> Heur
  -> Symbol
  -> Player
  -> Arena
  -> (Term, Term, Term)
  -> (Loc, Loc)
  -> Term
  -> SymSt
  -> SyBo
  -> IO (Either Term (Term, SyBo))
tryFindInv conf heur prime player arena (_, step, conc) (loc, loc') fixInv reach prog =
  iter 0 FOL.true
  where
    iter cnt invar
      | cnt >= H.invariantIterations heur = pure $ Left invar
      | otherwise = do
        lg conf ["Try invariant", SMTLib.toString invar]
        let reach' = set reach loc' $ FOL.orf [reach `get` loc, FOL.andf [step, invar]]
        (stAcc, prog) <- pure $ iterA heur player arena reach' loc' prog
        let res = FOL.removePref prime $ stAcc `get` loc
        res <- SMT.simplify conf res
        let query =
              Vars.forallX (vars arena)
                $ FOL.andf [fixInv, dom arena loc, conc, invar] `FOL.impl` res
        unless (null (FOL.frees query)) $ error "assert: found free variables in query"
        holds <- SMT.valid conf query
        if holds
          then pure $ Right (FOL.andf [dom arena loc, conc, invar, fixInv], prog)
          else iter (cnt + 1) res

iterA :: Heur -> Player -> Arena -> SymSt -> Loc -> SyBo -> (SymSt, SyBo)
iterA heur player arena attr shadow = go (noVisits arena) (OL.fromSet (preds arena shadow)) attr
  where
    go vcnt open attr prog =
      case OL.pop open of
        Nothing -> (attr, prog)
        Just (l, open)
          | visits l vcnt < H.iterAMaxCPres heur ->
            let new = cpre player arena attr l
             in go
                  (visit l vcnt)
                  (preds arena l `OL.push` open)
                  (SymSt.disj attr l new)
                  (Synt.enforceTo l new attr prog)
          | otherwise -> go vcnt open attr prog

-------------------------------------------------------------------------------
-- Manhatten distance lemma generation
-------------------------------------------------------------------------------
lemmaGuess :: Config -> Heur -> Symbol -> Player -> Arena -> Term -> IO (Maybe (Term, Term, Term))
lemmaGuess conf heur prime player arena reach = do
  lg conf ["Guess lemma on", SMTLib.toString reach]
  boxVars <- boxVars conf player arena reach
  lg conf ["Use variables", strL id boxVars]
  box <- mkBox conf heur (vars arena) boxVars reach
  if null box
    then pure Nothing
    else let dist = manhatten box
             base = boxTerm id box
             epsilon
               | FOL.SReal `elem` FOL.sorts dist = FOL.Const $ FOL.CReal $ H.minEpsilon heur
               | otherwise = FOL.oneT
             step = FOL.mapSymbol (prime ++) dist `FOL.geqT` FOL.addT [dist, epsilon]
             conc = FOL.true
          in pure $ Just (base, step, conc)

type Box a = [(Term, (Bool, a))]

boxTerm :: (a -> Term) -> Box a -> Term
boxTerm toTerm = FOL.andf . map go
  where
    go (term, (upper, bound))
      | upper = term `FOL.leqT` toTerm bound
      | otherwise = term `FOL.geqT` toTerm bound

manhatten :: Box Term -> Term
manhatten = FOL.addT . map go
  where
    go (term, (upper, bound))
      | upper = FOL.ite (term `FOL.leqT` bound) FOL.zeroT $ FOL.func "-" [term, bound]
      | otherwise = FOL.ite (term `FOL.geqT` bound) FOL.zeroT $ FOL.func "-" [bound, term]

mkBox :: Config -> Heur -> Variables -> [Symbol] -> Term -> IO (Box Term)
mkBox conf heur vars boxVars reach = do
  reach <- SMT.simplify conf reach
  box <- mkOptBox conf heur vars boxVars reach
  if null box
    then do
      lg conf ["Switch to point-base"]
      fromMaybe [] <$> completeBox conf boxVars reach
    else pure box

mkOptBox :: Config -> Heur -> Variables -> [Symbol] -> Term -> IO (Box Term)
mkOptBox conf heur vars boxVars reach = do
  let boxTerms = generateTerms (H.manhattenTermCount heur) vars boxVars
  (boxScheme, maxTerms) <- prepareBox conf reach boxTerms
  if null boxScheme
    then pure []
    else do
      let impCond = Vars.forallX vars $ boxTerm (uncurry FOL.Var) boxScheme `FOL.impl` reach
      let exCond = Vars.existsX vars $ boxTerm (uncurry FOL.Var) boxScheme
      cond <- SMT.simplify conf $ FOL.andf [impCond, exCond]
      model <- SMT.tryOptPareto conf (H.boxOptSmtTO heur) cond maxTerms
      case model of
        Just (Just model) ->
          let toInteger = fmap $ assertConst . FOL.setModel model . uncurry FOL.Var
           in pure $ map (second toInteger) boxScheme
        _ -> pure []
  where
    assertConst term
      | null (FOL.frees term) = term
      | otherwise = error "assert: result should be an constant"

completeBox :: Config -> [Symbol] -> Term -> IO (Maybe (Box Term))
completeBox conf boxVars reach = do
  let nonBoxVars = filter (`notElem` boxVars) $ Set.toList $ FOL.frees reach
  model <- SMT.satModel conf (FOL.forAll nonBoxVars reach)
  case model of
    Nothing -> do
      model <- SMT.satModel conf reach
      case model of
        Nothing -> pure Nothing
        Just model -> pure $ Just $ concatMap (modelCons model) $ Map.toList $ FOL.bindings reach
    Just model -> pure $ Just $ concatMap (modelCons model) $ Map.toList $ FOL.bindings reach
  where
    modelCons model (var, sort) =
      let varTerm = FOL.Var var sort
          bound = FOL.setModel model varTerm
       in [(varTerm, (True, bound)), (varTerm, (False, bound))]

prepareBox :: Config -> Term -> [Term] -> IO (Box (Symbol, Sort), [Term])
prepareBox conf reach boxTerms = go [] [] boxTerms
  where
    go box maxTerms =
      \case
        [] -> pure (box, maxTerms)
        boxTerm:xr -> do
          let syms = FOL.symbols $ FOL.andf $ [reach] ++ boxTerms ++ map fst box
          let sort
                | FOL.SReal `elem` FOL.sorts boxTerm = FOL.SReal
                | otherwise = FOL.SInt
          let newname upper
                | upper = FOL.uniqueName "upper" syms
                | otherwise = FOL.uniqueName "lower" syms
          let newvar upper = FOL.Var (newname upper) sort
          let newbox upper = (boxTerm, (upper, (newname upper, sort)))
          up <- boundIn conf True boxTerm reach
          lo <- boundIn conf False boxTerm reach
          case (lo, up) of
            (True, False) ->
              go (newbox False : box) (FOL.func "-" [FOL.zeroT, newvar False] : maxTerms) xr
            (False, True) -> go (newbox True : box) (newvar True : maxTerms) xr
            (True, True) ->
              go
                (newbox True : newbox False : box)
                (FOL.func "-" [newvar True, newvar False] : maxTerms)
                xr
            (False, False) -> go box maxTerms xr

boundIn :: Config -> Bool -> Term -> Term -> IO Bool
boundIn conf upper dimTerm reach = do
  let boundName = FOL.unusedName "bound" $ FOL.andf [dimTerm, reach]
  let bound
        | FOL.SReal `elem` FOL.sorts dimTerm = FOL.rvarT boundName
        | otherwise = FOL.ivarT boundName
  let vars = Set.toList $ FOL.frees dimTerm `Set.union` FOL.frees reach
  let query =
        FOL.forAll vars
          $ FOL.impl reach
          $ if upper
              then FOL.leqT dimTerm bound
              else FOL.geqT dimTerm bound
  query <- SMT.simplify conf query
  SMT.sat conf query

generateTerms :: Int -> Variables -> [Symbol] -> [Term]
generateTerms maxSize vars boxVars =
  concatMap (filter (not . isMixed) . combToTerms)
    $ filter (not . null)
    $ boundPowerList
    $ map (Vars.mk vars) boxVars
  where
    combToTerms :: [Term] -> [Term]
    combToTerms =
      map
        (\case
           [] -> error "assert: unreachable code"
           [x] -> x
           xs -> FOL.addT xs)
        . multCombs
    multCombs :: [Term] -> [[Term]]
    multCombs =
      \case
        [] -> error "assert: unreachable code"
        [x] -> [[x]]
        x:xr ->
          let rec = multCombs xr
           in map (x :) rec ++ map (FOL.func "-" [FOL.zeroT, x] :) rec
        --
    boundPowerList :: [a] -> [[a]]
    boundPowerList =
      \case
        [] -> [[]]
        x:xr ->
          let rec = boundPowerList xr
           in rec ++ map (x :) (filter ((< maxSize) . length) rec)

isMixed :: Term -> Bool
isMixed t =
  let sorts = FOL.sorts t
   in (FOL.SReal `elem` sorts) && (FOL.SInt `elem` sorts)

boxVars :: Config -> Player -> Arena -> Term -> IO [Symbol]
boxVars conf player arena reach =
  filterM (usefullTargetVar conf player arena)
    $ filter (FOL.isNumber . Vars.sortOf (vars arena))
    $ Set.toList
    $ FOL.frees reach

usefullTargetVar :: Config -> Player -> Arena -> Symbol -> IO Bool
usefullTargetVar conf player arena var = do
  opVar <- varPlayerControlled conf (opponent player) arena var
  if opVar
    then varPlayerControlled conf player arena var
    else pure True

varPlayerControlled :: Config -> Player -> Arena -> Symbol -> IO Bool
varPlayerControlled conf player arena var = do
  let cVarName = FOL.uniqueName ("c_" ++ var) $ usedSymbols arena
  let cvar = FOL.Var cVarName (sortOf arena var)
  let st = SymSt.symSt (locations arena) $ const $ cvar `FOL.equal` Vars.mk (vars arena) var
  let query =
        FOL.orfL (Set.toList (locations arena)) $ \l ->
          FOL.andf [pre arena st l, FOL.neg (cpre player arena st l)]
  SMT.unsat conf query
