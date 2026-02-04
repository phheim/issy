---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Acceleration.MDAcceleration
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Solver.Acceleration.MDAcceleration
  ( accelReach
  , iterA
  ) where

-------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
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
import Issy.Utils.Extra
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
    Nothing -> lg conf ["Lemma guessing failed"] $> (FOL.false, Synt.empty)
    Just (base, step, conc, invar) -> do
      lg
        conf
        [ "Lemma guessing succeded with"
        , SMTLib.toString base
        , SMTLib.toString step
        , SMTLib.toString conc
        , "with invariant"
        , SMTLib.toString invar
        ]
        -- 2. try a few explicit iterations to find invariant
      invRes <-
        tryFindInv
          conf
          heur
          prime
          player
          arena
          (base, step, conc)
          (loc, loc')
          fixInv
          reach
          prog
          invar
      case invRes of
        Just (conc, prog) ->
          lg conf ["Invariant  search resulted in", SMTLib.toString conc] $> (conc, prog)
        Nothing -> lg conf ["Invariant search failed"] $> (FOL.false, Synt.empty)

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
  -> Term
  -> IO (Maybe (Term, SyBo))
tryFindInv conf heur prime player arena (base, step, conc) (loc, loc') fixInv reach prog = iter 0
  where
    check = checkInv conf heur prime player arena (base, step, conc) (loc, loc') fixInv reach prog
    iter cnt invar
      | cnt < H.invariantIterations heur = do
        res <- check invar
        case res of
          Right res -> pure $ Just res
          Left invar -> iter (cnt + 1) invar
      | otherwise = do
        lg conf ["Try to strenghten smartly"]
        let prefix =
              FOL.uniquePrefix "selectors_b"
                $ Set.insert prime
                $ Set.union (FOL.symbols invar)
                $ usedSymbols arena
        res <- check =<< strengthenBool conf prefix invar
        case res of
          Right res -> pure $ Just res
          Left res -> do
            lg conf ["Smart strengthening failed with remainder", SMTLib.toString res]
            pure Nothing

checkInv ::
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
  -> Term
  -> IO (Either Term (Term, SyBo))
checkInv conf heur prime player arena (base, step, conc) (loc, loc') fixInv reach prog invar
  | invar == FOL.false = pure $ Left FOL.false
  | otherwise = do
    lg conf ["Check invariant", SMTLib.toString invar]
    let reach' = set reach loc' $ FOL.orf [reach `get` loc, FOL.andf [step, invar]]
    (stAcc, prog) <- pure $ iterA heur player arena reach' loc' prog
    let res = FOL.removePref prime $ stAcc `get` loc
    res <- SMT.simplify conf res
    let query =
          Vars.forallX (vars arena) $ FOL.andf [fixInv, dom arena loc, conc, invar] `FOL.impl` res
    let baseCond =
          Vars.forallX (vars arena)
            $ FOL.andf [dom arena loc, fixInv, base, invar] `FOL.impl` (reach `get` loc)
    let accelValue = FOL.andf [dom arena loc, conc, invar, fixInv]
    let progress = Vars.existsX (vars arena) $ FOL.andf [accelValue, FOL.neg (get reach loc)]
    if null (FOL.frees query)
       -- Not Boolean Paramters
      then do
        holds <- SMT.valid conf query
        if holds
          then do
            baseCondHolds <- SMT.valid conf baseCond
            if baseCondHolds
              then pure $ Right (accelValue, prog)
              else do
                lg conf ["Base condition failed"]
                pure $ Left res
          else pure $ Left res
      else do
        model <- SMT.trySatModel conf (H.invSatModelTO heur) $ FOL.andf [query, baseCond, progress]
        case model of
          Just (Just model) -> do
            accelValue <- SMT.simplify conf $ FOL.setModel model accelValue
            prog <- pure $ Synt.mapTerms (FOL.setModel model) prog
            pure $ Right (accelValue, prog)
          _ -> pure $ Left res

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
lemmaGuess ::
     Config -> Heur -> Symbol -> Player -> Arena -> Term -> IO (Maybe (Term, Term, Term, Term))
lemmaGuess conf heur prime player arena reach = do
  reach <- SMT.simplify conf reach
  lg conf ["Guess lemma on", SMTLib.toString reach]
  box <- mkBox conf heur player arena reach
  case box of
    Nothing -> pure Nothing
    Just (box, invar) ->
      let dist = manhatten box
          base = boxTerm id box
          epsilon
            | FOL.SReal `elem` FOL.sorts dist = FOL.Const $ FOL.CReal $ H.minEpsilon heur
            | otherwise = FOL.oneT
          step = FOL.mapSymbol (prime ++) dist `FOL.geqT` FOL.addT [dist, epsilon]
          conc = FOL.true
       in pure $ Just (base, step, conc, invar)

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
      | upper = FOL.ite (term `FOL.leqT` bound) FOL.zeroT $ FOL.subT term bound
      | otherwise = FOL.ite (term `FOL.geqT` bound) FOL.zeroT $ FOL.subT bound term

mkBox :: Config -> Heur -> Player -> Arena -> Term -> IO (Maybe (Box Term, Term))
mkBox conf heur player arena reach = do
  (reach, invar, boxVars) <- mkTarget conf heur player arena reach
  box <- mkOptBox conf heur (vars arena) reach
  case box of
    Nothing -> do
      lg conf ["Switch to point-base"]
      fmap (\box -> (filterBoxAll boxVars box, invar)) <$> completeBox conf reach
    Just box -> pure $ Just (filterBoxAny boxVars box, invar)

filterBoxAll :: [Symbol] -> Box a -> Box a
filterBoxAll boxVars = filter (all (`elem` boxVars) . FOL.frees . fst)

filterBoxAny :: [Symbol] -> Box a -> Box a
filterBoxAny boxVars = filter (any (`elem` boxVars) . FOL.frees . fst)

mkTarget :: Config -> Heur -> Player -> Arena -> Term -> IO (Term, Term, [Symbol])
mkTarget conf _ player arena reach = do
  reach <- SMT.simplify conf reach
  boxVars <- boxVars conf player arena reach
  boxVars <-
    if null boxVars
      then pure (filter (FOL.isNumber . sortOf arena) (Vars.stateVarL (vars arena)))
      else pure boxVars
  let nonBoxVars = filter (`notElem` boxVars) $ Set.toList $ FOL.frees reach
  lg conf ["Use variables", strL id boxVars]
  invar <- SMT.simplify conf $ FOL.exists boxVars reach
  newReach <- SMT.simplify conf $ FOL.forAll nonBoxVars $ invar `FOL.impl` reach
  let check1 = SMT.sat conf $ FOL.andf [invar, newReach]
  let check2 = SMT.valid conf $ FOL.andf [invar, newReach] `FOL.impl` reach
  check <- andM check1 check2
  if check
    then do
      lg conf ["New target", SMTLib.toString newReach]
      lg conf ["New invariant", SMTLib.toString invar]
      pure (newReach, invar, boxVars)
    else do
      lg conf ["Keep target"]
      pure (reach, FOL.true, boxVars)

mkOptBox :: Config -> Heur -> Variables -> Term -> IO (Maybe (Box Term))
mkOptBox conf heur vars reach = do
  let boxTerms = generateTerms (H.manhattenTermCount heur) vars $ Set.toList $ FOL.frees reach
  (boxScheme, maxTerms) <- prepareBox conf reach boxTerms
  if null boxScheme
    then pure Nothing
    else do
      let impCond = Vars.forallX vars $ boxTerm (uncurry FOL.var) boxScheme `FOL.impl` reach
      let exCond = Vars.existsX vars $ boxTerm (uncurry FOL.var) boxScheme
      cond <- SMT.simplify conf $ FOL.andf [impCond, exCond]
      model <- SMT.tryOptPareto conf (H.boxOptSmtTO heur) cond maxTerms
      case model of
        Just (Just model) ->
          let toInteger = fmap $ assertConst . FOL.setModel model . uncurry FOL.var
           in pure $ Just $ map (second toInteger) boxScheme
        _ -> pure Nothing
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
      let varTerm = FOL.var var sort
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
                | upper = FOL.uniquePrefix "upper" syms
                | otherwise = FOL.uniquePrefix "lower" syms
          let newvar upper = FOL.var (newname upper) sort
          let newbox upper = (boxTerm, (upper, (newname upper, sort)))
          up <- boundIn conf True boxTerm reach
          lo <- boundIn conf False boxTerm reach
          case (lo, up) of
            (True, False) ->
              go (newbox False : box) (FOL.subT FOL.zeroT (newvar False) : maxTerms) xr
            (False, True) -> go (newbox True : box) (newvar True : maxTerms) xr
            (True, True) ->
              go
                (newbox True : newbox False : box)
                (FOL.subT (newvar True) (newvar False) : maxTerms)
                xr
            (False, False) -> go box maxTerms xr

boundIn :: Config -> Bool -> Term -> Term -> IO Bool
boundIn conf upper dimTerm reach = do
  let boundName = FOL.unusedPrefix "bound" $ FOL.andf [dimTerm, reach]
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
           in map (x :) rec ++ map (FOL.subT FOL.zeroT x :) rec
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
usefullTargetVar conf player arena var =
  andM (varProgress conf arena var)
    $ orM (varPlayerControlled conf player arena var)
    $ not <$> varPlayerControlled conf (opponent player) arena var

varPlayerControlled :: Config -> Player -> Arena -> Symbol -> IO Bool
varPlayerControlled conf player arena var = do
  let cVarName = FOL.uniquePrefix ("copy_" ++ var) $ usedSymbols arena
  let cvar = FOL.var cVarName (sortOf arena var)
  let st = SymSt.symSt (locations arena) $ const $ cvar `FOL.equal` Vars.mk (vars arena) var
  SMT.unsat conf
    $ FOL.orfL (locationL arena)
    $ \l -> FOL.andf [pre arena st l, FOL.neg (cpre player arena st l)]

varProgress :: Config -> Arena -> Symbol -> IO Bool
varProgress conf arena var
  | not (FOL.isNumber (sortOf arena var)) = pure False
  | otherwise = do
    let bVarName = FOL.uniquePrefix ("bound_" ++ var) $ usedSymbols arena
    let prefix = FOL.uniquePrefix "prefix_" $ usedSymbols arena
    let varBound = FOL.var bVarName (sortOf arena var)
    let varAbs = FOL.absT $ Vars.mk (vars arena) var
    let varAbsCopy = FOL.absT $ FOL.var (prefix ++ var) (sortOf arena var)
    let st =
          SymSt.symSt (locations arena)
            $ const
            $ FOL.andf [varAbs `FOL.gtT` varBound, FOL.neg (varAbs `FOL.equal` varAbsCopy)]
    SMT.sat conf
      $ FOL.forAll [bVarName]
      $ Vars.existsX (vars arena)
      $ FOL.orfL (Set.toList (locations arena))
      $ \l -> FOL.andf [dom arena l, FOL.removePref prefix (pre arena st l)]
---------------------------------------------------------------------------------------------------
