-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Solver.Acceleration.MDAcceleration
  ( accelReach
  ) where

-------------------------------------------------------------------------------
import Control.Monad (unless)
import Data.Bifunctor (second)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, geomCHCAcceleration, invariantIterations, manhattenTermCount, setName)
import qualified Issy.Logic.CHC as CHC
import Issy.Logic.FOL (Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Acceleration.Heuristics
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

-------------------------------------------------------------------------------
-- It assume that the arena is cycic in the location it accelerates.
accelReach :: Config -> Int -> Player -> Arena -> Loc -> SymSt -> IO (Term, CFG)
accelReach conf limit player arena loc reach = do
  conf <- pure $ setName "AccReachMD" conf
  lg conf ["Accelerate in", locName arena loc, "on", strSt arena reach]
  lg conf ["Size bound", show (limit2size limit)]
  let prime = FOL.uniquePrefix "init_" $ usedSymbols arena
  -- 0. Compute loop sceneario
  (arena, loc, loc', reach, fixInv) <- loopScenario conf (Just (limit2size limit)) arena loc reach
  lg conf ["Fixed invariant", smtLib2 fixInv]
  -- 1. Guess lemma
  lemma <- lemmaGuess conf prime (vars arena) (reach `get` loc)
  case lemma of
    Nothing -> do
      lg conf ["Lemma guessing failed"]
      pure (FOL.false, CFG.empty)
    Just (base, step, conc) -> do
      lg conf ["Lemma guessing succeded with", smtLib2 base, smtLib2 step, smtLib2 conc]
      -- 1.5 Check base condition
      baseCond <-
        SMT.valid conf
          $ Vars.forallX (vars arena)
          $ FOL.andf [inv arena loc, base] `FOL.impl` (reach `get` loc)
      unless baseCond $ error "assert: the base should be computed that this holds"
        -- 2. try a few explicit iterations to find invariant
      invRes <- tryFindInv conf prime player arena (step, conc) (loc, loc') fixInv reach
      case invRes of
        Right (conc, prog) -> do
          lg conf ["Invariant iteration resulted in", smtLib2 conc]
          pure (conc, prog)
        Left overApprox -> do
          lg conf ["Invariant iteration failed"]
          if geomCHCAcceleration conf
            then do
              lg conf ["MaxCHC invariant computation"]
              invRes <-
                exactInv conf prime player arena (step, conc) (loc, loc') fixInv reach overApprox
              case invRes of
                Left err -> do
                  lg conf ["MaxCHC invariant computation failed with", err]
                  pure (FOL.false, CFG.empty)
                Right (conc, prog) -> do
                  lg conf ["MaxCHC invariant computation resulted in", smtLib2 conc]
                  pure (conc, prog)
            else pure (FOL.false, CFG.empty)

-------------------------------------------------------------------------------
-- Invariant Iteration
-------------------------------------------------------------------------------
tryFindInv ::
     Config
  -> Symbol
  -> Player
  -> Arena
  -> (Term, Term)
  -> (Loc, Loc)
  -> Term
  -> SymSt
  -> IO (Either Term (Term, CFG))
tryFindInv conf prime player arena (step, conc) (loc, loc') fixInv reach = iter 0 FOL.true
  where
    iter cnt invar
      | cnt >= invariantIterations conf = pure $ Left invar
      | otherwise = do
        lg conf ["Try invariant", smtLib2 invar]
        let reach' = set reach loc' $ FOL.orf [reach `get` loc, FOL.andf [step, invar]]
                            -- TODO: Build proper CFG
        let (stAcc, _) = iterA player arena reach' loc' CFG.empty
        let res = unprime prime $ stAcc `get` loc
        res <- SMT.simplifyStrong conf res
        let query = Vars.forallX (vars arena) $ FOL.andf [inv arena loc, conc, invar] `FOL.impl` res
        unless (null (FOL.frees query)) $ error "assert: found free variables in query"
        holds <- SMT.valid conf query
        if holds
          then pure $ Right (FOL.andf [inv arena loc, conc, invar, fixInv], CFG.empty)
          else iter (cnt + 1) res

unprime :: Symbol -> Term -> Term
unprime prime =
  FOL.mapSymbol $ \v ->
    if prime `isPrefixOf` v
      then drop (length prime) v
      else v

iterA :: Player -> Arena -> SymSt -> Loc -> CFG -> (SymSt, CFG)
iterA player arena attr shadow = go (noVisits arena) (OL.fromSet (preds arena shadow)) attr
  where
    go vcnt open attr cfgl =
      case OL.pop open of
        Nothing -> (attr, cfgl)
        Just (l, open)
          | visits l vcnt < visitingThreshold ->
            go
              (visit l vcnt)
              (preds arena l `OL.push` open)
              (SymSt.disj attr l $ cpre player arena attr l)
              (CFG.addUpd attr arena l cfgl)
          | otherwise -> go vcnt open attr cfgl

exactInv ::
     Config
  -> Symbol
  -> Player
  -> Arena
  -> (Term, Term)
  -> (Loc, Loc)
  -> Term
  -> SymSt
  -> Term
  -> IO (Either String (Term, CFG))
exactInv conf prime player arena (step, conc) (loc, loc') fixInv reach invApprox = do
    -- TODO: Add logging
  let invName = FOL.uniquePrefix "chc_invar" $ Set.insert prime $ usedSymbols arena
    -- TODO: enhance by only useing usefull stuff! Needs change in CHC stuff
  let sorts = map (Vars.sortOf (vars arena)) (Vars.stateVarL (vars arena))
  let invar =
        FOL.Func (FOL.CustomF invName sorts FOL.SBool)
          $ map (\v -> FOL.Var v (Vars.sortOf (vars arena) v))
          $ Vars.stateVarL (vars arena)
  let reach' = set reach loc' $ FOL.orf [reach `get` loc, FOL.andf [step, invar]]
  let (stAcc, _) = iterA player arena reach' loc' CFG.empty
  let res = unprime prime $ stAcc `get` loc
  res <- SMT.simplifyUF conf res --TODO: Maybe add timeout here?
  let query = Vars.forallX (vars arena) $ FOL.andf [inv arena loc, conc, invar] `FOL.impl` res
  let minQuery = Vars.forallX (vars arena) $ invar `FOL.impl` invApprox
  unless (null (FOL.frees query)) $ error "assert: found free variables in query"
  chcRes <- CHC.computeMax conf (vars arena) invName [query, minQuery]
  case chcRes of
    Left err -> pure $ Left err
    Right invar -> pure $ Right (FOL.andf [inv arena loc, conc, invar, fixInv], CFG.empty)

-------------------------------------------------------------------------------
-- Manhatten distance lemma generation
-------------------------------------------------------------------------------
lemmaGuess :: Config -> Symbol -> Variables -> Term -> IO (Maybe (Term, Term, Term))
lemmaGuess conf prime vars reach = do
  lg conf ["Guess lemma on", smtLib2 reach]
  box <- mkBox conf vars reach
  pure
    $ if null box
        then Nothing
        else let dist = manhatten box
                 base = boxTerm id box
            -- TODO: Make more real number friendly!
                 step = FOL.mapSymbol (prime ++) dist `FOL.geqT` FOL.addT [dist, FOL.oneT]
                 conc = FOL.true
              in Just (base, step, conc)

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

mkBox :: Config -> Variables -> Term -> IO (Box Term)
mkBox conf vars reach = do
  box <- mkOptBox conf vars reach
  if null box
    then do
      lg conf ["Switch to point-base"]
      fromMaybe [] <$> completeBox conf reach
    else pure box

mkOptBox :: Config -> Variables -> Term -> IO (Box Term)
mkOptBox conf vars reach = do
  let boxTerms = generateTerms (manhattenTermCount conf) vars reach
  (boxScheme, maxTerms) <- prepareBox conf vars reach boxTerms
  if null boxScheme
    then pure []
    else do
      let query = Vars.forallX vars $ boxTerm (uncurry FOL.Var) boxScheme `FOL.impl` reach
      model <- SMT.optPareto conf query maxTerms
      case model of
        Nothing -> pure []
        Just model ->
          let toInteger = fmap $ assertConst . FOL.setModel model . uncurry FOL.Var
           in pure $ map (second toInteger) boxScheme
  where
    assertConst term
      | null (FOL.frees term) = term
      | otherwise = error "assert: result should be an constant"

completeBox :: Config -> Term -> IO (Maybe (Box Term))
completeBox conf reach = do
  model <- SMT.satModel conf reach
  case model of
    Nothing -> pure Nothing
    Just model -> pure $ Just $ concatMap (modelCons model) $ Map.toList $ FOL.bindings reach
  where
    modelCons model (var, sort) =
      let varTerm = FOL.Var var sort
          bound = FOL.setModel model varTerm
       in [(varTerm, (True, bound)), (varTerm, (False, bound))]

prepareBox :: Config -> Variables -> Term -> [Term] -> IO (Box (Symbol, Sort), [Term])
prepareBox conf vars reach boxTerms = go [] [] boxTerms
  where
    go box maxTerms =
      \case
        [] -> pure (box, maxTerms)
        boxTerm:xr -> do
          let syms = FOL.symbols $ FOL.andf $ [reach] ++ boxTerms ++ map fst box
          let sort =
                if any ((FOL.SReal ==) . Vars.sortOf vars) (FOL.frees boxTerm)
                  then FOL.SReal
                  else FOL.SInt
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
  let bound = FOL.ivarT $ FOL.unusedName "bound" $ FOL.andf [dimTerm, reach]
  let vars = Set.toList $ FOL.frees dimTerm `Set.union` FOL.frees reach
  let query =
        FOL.forAll vars
          $ FOL.impl reach
          $ if upper
              then FOL.leqT dimTerm bound
              else FOL.geqT dimTerm bound
  SMT.sat conf query

generateTerms :: Int -> Variables -> Term -> [Term]
generateTerms maxSize vars reach =
  concatMap combToTerms
    $ filter (not . null)
    $ boundPowerList
    $ map (\v -> FOL.Var v (Vars.sortOf vars v))
    $ filter (FOL.isNumber . Vars.sortOf vars)
    $ Set.toList
    $ FOL.frees reach
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
-------------------------------------------------------------------------------
-- Heurisitics
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
