-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Monitor.Rules
  ( applyRules
  , GlobalS
  , globalState
  , globalStateTSL
  , deducedInvariant
  , derivedEventually
  ) where

-------------------------------------------------------------------------------
import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.List (nub)
import Data.Map.Strict (Map, (!), (!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set, cartesianProduct)
import qualified Data.Set as Set

-------------------------------------------------------------------------------
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config
  ( Config
  , rulesDeduction
  , rulesDeductionPrecise
  , rulesSaturation
  , rulesSubsitution
  , rulesUnsatChecks
  , setName
  )
import qualified Issy.Logic.CHC as CHC
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Monitor.Fixpoints
import Issy.Monitor.Formula
import Issy.Monitor.State
import Issy.Utils.Extra (ifQuery, intmapSet)
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- Overall
-------------------------------------------------------------------------------
applyRules :: Config -> GlobalS -> State -> IO (State, GlobalS)
applyRules cfg gls st
  | isFalse st || isTrue st = pure (st, gls)
  | otherwise = do
    cfg <- pure $ setName "Rules" cfg
    lg cfg ["Apply rules to", stateToString st]
    let rewrite =
          ruleChainAccum
            [ ruleG (rulesUnsatChecks cfg) unsatRules
            , ruleG (rulesSaturation cfg) saturate
            , ruleG (rulesSubsitution cfg) substitute
            ]
    let deduce =
          ruleChainAccum
            [ liftS deduceInv
            , liftS deduceLiveness
            , ruleG (rulesDeductionPrecise cfg) (liftS deducePreciseInv)
            ]
    let overall = ruleChain [liftP liftImps, rewrite, ruleG (rulesDeduction cfg) deduce, rewrite]
    st <- pure $ normSt st
    (st, gls) <- first normSt <$> overall cfg gls Set.empty (reorganise st)
    lg cfg ["Finished rules with", stateToString st]
    pure (st, gls)

-------------------------------------------------------------------------------
-- Global State
-------------------------------------------------------------------------------
data GlobalS = GlobalS
  { vars :: Variables
  , fixpointPred :: Symbol
  , fpPred :: Term
  , fpPred' :: Term
  -- Update related
  , aux :: [Symbol]
  , updateEncodes :: Map (Symbol, Term) Symbol
  , exactlyOneUpd :: Term
  , updateEffect :: Term
    -- MUTABLE
  , genReaches :: Map [Formula] (Set (Formula, Formula))
  , unsatCache :: Map [Formula] Bool
  , implCache :: Map (Formula, Formula) Bool
  , muvalUnsat :: Set ([Formula], Formula, Formula)
  , chcCache :: Map [([Term], Term)] Bool
  , chcMaxCache :: Map ([Formula], [Formula]) (Maybe Formula)
  } deriving (Show)

globalState :: Variables -> GlobalS
globalState vars =
  let fpn = FOL.uniqueName "fixpointpred" $ Vars.allSymbols vars
   in GlobalS
        { vars = vars
        , fixpointPred = fpn
        , fpPred = Vars.unintPredTerm vars fpn
        , fpPred' = Vars.primeT vars $ Vars.unintPredTerm vars fpn
            --
        , aux = []
        , updateEncodes = Map.empty
        , exactlyOneUpd = FOL.true
        , updateEffect = FOL.true
            --
        , genReaches = Map.empty
        , unsatCache = Map.empty
        , implCache = Map.empty
        , muvalUnsat = Set.empty
        , chcCache = Map.empty
        , chcMaxCache = Map.empty
        }

globalStateTSL :: Variables -> Set (Symbol, Term) -> GlobalS
globalStateTSL vars updates =
  let complUpd = Set.union updates $ Set.map (\v -> (v, Vars.mk vars v)) $ Vars.stateVars vars
      prefUpd = FOL.uniquePrefix "update" $ Vars.allSymbols vars
      updAux = intmapSet (\n upd -> (upd, prefUpd ++ show n)) complUpd
   in (globalState vars)
        { updateEncodes = Map.fromList updAux
        , aux = map snd updAux
        , exactlyOneUpd =
            FOL.andf
              $ flip map (Vars.stateVarL vars)
              $ \var ->
                  FOL.exactlyOne $ map (FOL.bvarT . snd) $ filter ((== var) . fst . fst) updAux
        , updateEffect =
            FOL.andf
              $ flip map updAux
              $ \((var, term), aux) ->
                  FOL.impl (FOL.bvarT aux) $ FOL.equal term $ Vars.primeT vars $ Vars.mk vars var
        }

-------------------------------------------------------------------------------
-- Rule Apllication Framework
-------------------------------------------------------------------------------
type Rule = Config -> GlobalS -> Set (Domain, Formula, Formula) -> State -> IO (State, GlobalS)

type SRule
  = Config -> GlobalS -> Set (Domain, Formula, Formula) -> Domain -> State -> IO (State, GlobalS)

type PRule = Config -> GlobalS -> Domain -> State -> IO State

liftS :: SRule -> Rule
liftS rule cfg gls new st = do
  (st, gls) <- rule cfg gls new Assumptions st
  rule cfg gls new Guarantees st

liftP :: PRule -> Rule
liftP rule =
  liftS $ \cfg gls _ dom st -> do
    st <- rule cfg gls dom st
    pure (st, gls)

ruleFP :: Rule -> Rule
ruleFP rule cfg gls new st
  | null new || isTrue st || isFalse st = pure (st, gls)
  | otherwise = do
    (st', gls) <- first simpleNormSt <$> rule cfg gls new st
    let generated = newImps st st'
    ruleFP rule cfg gls generated st'

ruleChain :: [Rule] -> Rule
ruleChain rules cfg gls new st
  | isTrue st || isFalse st = pure (st, gls)
  | otherwise =
    case rules of
      [] -> pure (st, gls)
      rule:rules -> do
        (st', gls) <- first simpleNormSt <$> rule cfg gls new st
        let generated = newImps st st'
        ruleChain rules cfg gls generated st'

ruleChainAccum :: [Rule] -> Rule
ruleChainAccum rules cfg gls new st
  | isTrue st || isFalse st = pure (st, gls)
  | otherwise =
    case rules of
      [] -> pure (st, gls)
      rule:rules -> do
        (st', gls) <- first simpleNormSt <$> rule cfg gls new st
        let generated = newImps st st'
        ruleChainAccum rules cfg gls (generated `Set.union` new) st'

ruleG :: Bool -> Rule -> Rule
ruleG g
  | g = id
  | otherwise = \_ _ gls _ st -> pure (st, gls)

-------------------------------------------------------------------------------
-- State Acessors / Helper Methods 
-------------------------------------------------------------------------------
deducedInvariant :: Config -> GlobalS -> Domain -> State -> IO Term
deducedInvariant cfg gls dom st =
  SMT.simplify cfg $ encode gls $ fand $ filter (staticFormula (vars gls)) $ dedInv dom st

derivedEventually :: Config -> GlobalS -> Domain -> State -> IO ([Formula], GlobalS)
derivedEventually cfg gls dom st = first nub <$> foldM go ([], gls) (impD dom st)
  where
    go (derived, gls) =
      \case
        (gamma, FEventually alpha)
          | notTemporal alpha ->
            ifQuery
              (checkImpl cfg gls (fand (current dom st ++ dedInv dom st)) gamma)
              (alpha : derived)
              derived
          | otherwise -> pure (derived, gls)
        _ -> pure (derived, gls)

unsatDedInv :: Config -> GlobalS -> Domain -> State -> [Formula] -> IO (Bool, GlobalS)
unsatDedInv cfg gls dom st fs = checkUnsat cfg gls $ fs ++ dedInv dom st

encode :: GlobalS -> Formula -> Term
encode gls = encodeFormula (updateEncodes gls !)

checkImpl :: Config -> GlobalS -> Formula -> Formula -> IO (Bool, GlobalS)
checkImpl cfg gls a b
  | b == FTrue = pure (True, gls)
  | a == FFalse = pure (True, gls)
  | a == b = pure (True, gls)
  | otherwise =
    case implCache gls !? (a, b) of
      Just res -> pure (res, gls)
      Nothing -> do
        res <- SMT.valid cfg $ FOL.impl (FOL.andf [encode gls a, exactlyOneUpd gls]) $ encode gls b
        pure (res, gls {implCache = Map.insert (a, b) res (implCache gls)})

checkUnsat :: Config -> GlobalS -> [Formula] -> IO (Bool, GlobalS)
checkUnsat cfg gls =
  \case
    [] -> pure (False, gls)
    fs ->
      case unsatCache gls !? fs of
        Just res -> pure (res, gls)
        Nothing -> do
          res <- SMT.unsat cfg $ FOL.andf $ exactlyOneUpd gls : map (encode gls) fs
          pure (res, gls {unsatCache = Map.insert fs res (unsatCache gls)})

callCHC :: Config -> GlobalS -> [([Term], Term)] -> IO (Maybe Bool, GlobalS)
callCHC cfg gls query = do
  case chcCache gls !? query of
    Just res -> pure (Just res, gls)
    Nothing -> do
      res <-
        CHC.check
          cfg
          (fixpointPred gls)
          (Vars.sortOf (vars gls) <$> Vars.stateVarL (vars gls))
          query
      pure
        $ case res of
            Nothing -> (Nothing, gls)
            Just res -> (Just res, gls {chcCache = Map.insert query res (chcCache gls)})

-------------------------------------------------------------------------------
-- Saturation Rules
-------------------------------------------------------------------------------
liftImps :: PRule
liftImps cfg _ dom st = foldM liftGlob st (eset dom st)
  where
    liftGlob st =
      \case
        FGlobally f -> addImp cfg "Lift-G" dom st (ftrue, f)
        _ -> pure st

saturate :: Rule
saturate =
  ruleFP
    $ ruleChainAccum
        [ ruleFP (liftS deriveImplications)
        , liftS liftGloballies
        , ruleFP (liftS propagateWeaks)
        , liftS groupImps
        ]

groupImps :: SRule
groupImps cfg gls new dom st = do
  lg cfg ["Apply group-imp to", show dom]
  let newConcs = Set.map snd $ filterDom dom new
  let groups =
        Map.toList
          $ Map.fromListWith Set.union
          $ map (\(p, c) -> (c, Set.singleton p))
          $ Set.toList
          $ impD dom st
  let merges = map (\(c, ps) -> (for (Set.toList ps), c)) $ filter ((`elem` newConcs) . fst) groups
  merges <-
    mapM
      (\(p, c) ->
         if staticFormula (vars gls) p
           then do
             p <- SMT.simplify cfg $ staticFormulaToTerm p
             pure (fpred True p, c)
           else pure (p, c))
      merges
  st <- foldM (addImp cfg "group-imp" dom) st merges
  pure (st, gls)

deriveImplications :: SRule
deriveImplications cfg gls new dom st = do
  lg cfg ["Apply chain/chain-F/chain-X to", show dom]
  let pairs = Set.toList $ newPairs (filterDom dom new) (impD dom st)
  (derived, gls) <-
    foldM
      (\(derived, gls) impl -> do
         (res, gls) <- chainRule cfg gls impl
         pure (maybe derived (`Set.insert` derived) res, gls))
      (Set.empty, gls)
      pairs
  st <- foldM (addImp cfg "Chain-PFX" dom) st derived
  pure (st, gls)

chainRule ::
     Config
  -> GlobalS
  -> ((Formula, Formula), (Formula, Formula))
  -> IO (Maybe (Formula, Formula), GlobalS)
chainRule cfg gls ((a, b1), (b2, phi))
  | b2 == FTrue = pure (Nothing, gls)
  | otherwise =
    case b1 of
      FEventually b1 -> eval b1 (a, feventually phi)
      FNext b1 -> eval b1 (a, fnext phi)
      b1 -> eval b1 (a, phi)
  where
    eval b1 res
      | notTemporal b1 = ifQuery (checkImpl cfg gls b1 b2) (Just res) Nothing
      | otherwise = pure (Nothing, gls)

newPairs :: Ord a => Set a -> Set a -> Set (a, a)
newPairs new base =
  Set.filter (\(x, y) -> x `elem` base && y `elem` base && x /= y)
    $ cartesianProduct new base `Set.union` cartesianProduct base new

liftGloballies :: SRule
liftGloballies cfg gls _ dom st = foldM (liftGlobally cfg dom) (st, gls) (impD dom st)

liftGlobally :: Config -> Domain -> (State, GlobalS) -> (Formula, Formula) -> IO (State, GlobalS)
liftGlobally cfg dom (st, gls) =
  \case
    (a, FGlobally b)
      | (ftrue, b) `elem` impD dom st -> pure (st, gls)
      | otherwise -> do
        (res, gls) <- checkImpl cfg gls (fand (current dom st)) a
        if res
          then do
            st <- addImp cfg "Lift-G" dom st (ftrue, b)
            pure (st, gls)
          else pure (st, gls)
    _ -> pure (st, gls)

propagateWeaks :: SRule
propagateWeaks cfg gls _ dom st = do
  lg cfg ["Apply propagate-W to", show dom]
  let weak = weaks dom st
  let weakPairs = commutativePairs weak
  foldM (propagateWeak cfg dom) (st, gls) weakPairs

propagateWeak ::
     Config
  -> Domain
  -> (State, GlobalS)
  -> ((Formula, Formula), (Formula, Formula))
  -> IO (State, GlobalS)
propagateWeak cfg dom (st, gls) ((a1, b1), (a2, b2)) = do
  (res, gls) <- chain gls [[b1, b2], [a1, b2], [a2, b1]]
  st <-
    if res
      then addImp cfg "propagate-W" dom st (ftrue, fand [a1, a2])
      else pure st
  pure (st, gls)
  where
    chain gls =
      \case
        [] -> pure (True, gls)
        f:fr -> do
          (res, gls) <- unsatDedInv cfg gls dom st f
          if res
            then chain gls fr
            else pure (False, gls)

commutativePairs :: [a] -> [(a, a)]
commutativePairs =
  \case
    [] -> []
    [_] -> []
    x:xr -> map (\y -> (x, y)) xr ++ commutativePairs xr

-------------------------------------------------------------------------------
-- Unsat Rules
-------------------------------------------------------------------------------
unsatRules :: Rule
unsatRules = ruleChain [liftS checkGlobalUnsat, liftS unsatLiveness]

checkGlobalUnsat :: SRule
checkGlobalUnsat cfg gls _ dom st = do
  lg cfg ["Apply Subst-UNSAT to", show dom]
  ifQuery (unsatDedInv cfg gls dom st (current dom st)) (invalidate dom st) st

unsatLiveness :: SRule
unsatLiveness cfg gls _ dom st = do
  lg cfg ["Apply Subst-UNSAT-Live to", show dom]
  (lives, gls) <- derivedEventually cfg gls dom st
  let check (usat, gls) live
        | usat = pure (True, gls)
        | otherwise = unsatDedInv cfg gls dom st [live]
  ifQuery (foldM check (False, gls) lives) (invalidate dom st) st

-------------------------------------------------------------------------------
-- Substitution Rules
-------------------------------------------------------------------------------
substitute :: Rule
substitute = ruleChainAccum [liftP simplifyImp, liftS substConst, liftS substImpl]

simplifyImp :: PRule
simplifyImp cfg _ dom st = do
  lg cfg ["Apply simplify-IA to", show dom]
  pure $ foldl (\st -> mapFs dom st . mp) st (impD dom st)
  where
    mp (f, g) = subst (for [fnot f, g]) ftrue . subst (fand [f, g]) f

substConst :: SRule
substConst cfg gls _ dom st = do
  lg cfg ["Apply subst-TB to", show dom]
  foldM substTerm (st, gls) $ Set.unions $ map findTerms $ fset dom st
  where
    substTerm (st, gls) term = do
      let query gls pol = unsatDedInv cfg gls dom st [fpred pol term]
      (res, gls) <- query gls True
      if res
        then pure (mapFs dom st (substT (term, False)), gls)
        else ifQuery (query gls False) (mapFs dom st (substT (term, True))) st

substImpl :: SRule
substImpl cfg gls _ dom st = do
  lg cfg ["Apply simplify-non-nested to", show dom]
  foldM subst (st, gls) (impD dom st)
  where
    substitutable = Set.unions $ map notNestedSubForms (fset dom st)
    --
    subst (st, gls) (gamma, phi)
      | phi `elem` substitutable =
        ifQuery
          (checkImpl cfg gls (fand (current dom st ++ dedInv dom st)) gamma)
          (mapFs dom st (substNotNested phi ftrue))
          st
      | otherwise = pure (st, gls)

-------------------------------------------------------------------------------
-- Deduction Rules
-------------------------------------------------------------------------------
deduceInv :: SRule
deduceInv cfg gls _ dom st = do
  lg cfg ["Apply Gen-Inv rules to", show dom]
  let pot = Set.unions $ map findPotInv (fset dom st)
  foldM (genInv cfg dom) (st, gls) pot

genInv :: Config -> Domain -> (State, GlobalS) -> Formula -> IO (State, GlobalS)
genInv cfg dom (st, gls) alpha
  | (ftrue, alpha) `elem` impD dom st = pure (st, gls)
  | stateOnly (Vars.isStateVar (vars gls)) alpha =
    let fp = fpPred gls
        fp' = fpPred' gls
        gammaE = encode gls $ fand $ current dom st
        alphaE = encode gls alpha
        init = ([gammaE], fp)
        trans = ([fp, exactlyOneUpd gls, updateEffect gls] ++ map (encode gls) (dedInv dom st), fp')
        exclude = ([FOL.neg alphaE, fp], FOL.false)
        query = [init, trans, exclude]
     in do
          (res, gls) <- callCHC cfg gls query
          case res of
            Just True -> do
              st <- addImp cfg "Gen-Inv" dom st (ftrue, alpha)
              pure (st, gls)
            _ -> pure (st, gls)
  | otherwise = pure (st, gls)

findPotInv :: Formula -> Set Formula
findPotInv = go
  where
    go =
      \case
        FAnd fs -> Set.unions $ map go fs
        FOr fs -> Set.unions $ map go fs
        FNext f -> go f
        FGlobally f -> go f
        FEventually f
          | notTemporal f -> Set.singleton (fnot f)
          | otherwise -> go f
        FWeak f g
          | notTemporal g -> Set.singleton (fnot g)
          | otherwise -> go f `Set.union` go g
        _ -> Set.empty

deduceLiveness :: SRule
deduceLiveness cfg gls _ dom st = do
  lg cfg ["Apply Gen-Reach rules to", show dom]
  let cached = Map.findWithDefault Set.empty (dedInv dom st) (genReaches gls)
  st <- foldM (addImp cfg "Gen-Reach-Prop" dom) st cached
  let cand = searchLiveness gls (current dom st) (fset dom st ++ eset dom st)
  foldM (genReach cfg dom) (st, gls) cand

genReach :: Config -> Domain -> (State, GlobalS) -> (Formula, Formula) -> IO (State, GlobalS)
genReach cfg dom (st, gls) (gamma, beta)
  | (gamma, feventually beta) `elem` impD dom st = pure (st, gls)
  | (dedInv dom st, gamma, feventually beta) `elem` muvalUnsat gls = pure (st, gls)
  | stateOnly (Vars.isStateVar (vars gls)) beta && stateOnly (Vars.isStateVar (vars gls)) gamma = do
    let query = Vars.forallX (vars gls) $ FOL.impl (encode gls gamma) $ fpPred gls
        fp =
          FOL.orf
            [ encode gls beta
            , Vars.forallI (vars gls)
                $ FOL.forAll (aux gls)
                $ Vars.forallX' (vars gls)
                $ FOL.impl
                    (FOL.andf
                       (map (encode gls) (dedInv dom st) ++ [exactlyOneUpd gls, updateEffect gls]))
                $ fpPred' gls
            ]
    res <- checkFPInclusion cfg (vars gls) query (fixpointPred gls) fp
    if res
      then do
        st <- addImp cfg "Gen-Reach" dom st (gamma, feventually beta)
        pure
          ( st
          , gls
              { genReaches =
                  Map.insertWith
                    Set.union
                    (dedInv dom st)
                    (Set.singleton (gamma, feventually beta))
                    (genReaches gls)
              })
      else pure
             ( st
             , gls
                 {muvalUnsat = (dedInv dom st, gamma, feventually beta) `Set.insert` muvalUnsat gls})
  | otherwise = pure (st, gls)

searchLiveness :: GlobalS -> [Formula] -> [Formula] -> Set (Formula, Formula)
searchLiveness gls currents = Set.unions . map go
  where
    current = fand $ filter (stateOnly (Vars.isStateVar (vars gls))) currents
    go =
      \case
        FGlobally f
          | notTemporal f -> Set.singleton (current, fnot f)
          | otherwise -> go f
        FEventually f
          | notTemporal f -> Set.singleton (current, f)
          | otherwise -> go f
        FOr [f, FEventually g]
          | notTemporal f && notTemporal g -> Set.fromList [(fnot f, g), (current, g)]
          | otherwise -> go g `Set.union` go f `Set.union` go (FEventually g)
        FOr [FEventually g, f]
          | notTemporal f && notTemporal g -> Set.fromList [(fnot f, g), (current, g)]
          | otherwise -> go g `Set.union` go f `Set.union` go (FEventually g)
        FAnd fs -> Set.unions $ map go fs
        FOr fs -> Set.unions $ map go fs
        FNext f -> go f
        FWeak f g -> go g `Set.union` go f
        _ -> Set.empty

deducePreciseInv :: SRule
deducePreciseInv cfg gls _ dom st = do
  lg cfg ["Apply Gen-Inv-P rules to", show dom]
  genInvPrec cfg gls dom st

genInvPrec :: Config -> GlobalS -> Domain -> State -> IO (State, GlobalS)
genInvPrec cfg gls dom st
  | (current dom st, dedInv dom st) `Map.member` chcMaxCache gls =
    case chcMaxCache gls ! (current dom st, dedInv dom st) of
      Just alpha -> do
        let gamma = fand $ current dom st
        st <- addImp cfg "Gen-Inv-P" dom st (gamma, alpha)
        pure (st, gls)
      Nothing -> pure (st, gls)
  | otherwise = do
    let gamma = fand $ current dom st
    let base = encode gls $ fand $ gamma : dedInv dom st
    base <- SMT.simplify cfg $ Vars.existsI (vars gls) $ FOL.exists (aux gls) base
    if base == FOL.true || base == FOL.false
      then pure (st, gls)
      else do
        let init =
              Vars.forallX (vars gls) $ FOL.func FOL.FImply [FOL.andf [base, fpPred gls], FOL.false]
            -- Transtion condition in CHC
        let tr = FOL.andf $ exactlyOneUpd gls : updateEffect gls : (encode gls <$> dedInv dom st)
        let trans =
              Vars.forallX (vars gls)
                $ Vars.forallI (vars gls)
                $ FOL.forAll (aux gls)
                $ Vars.forallX' (vars gls)
                $ FOL.func FOL.FImply [FOL.andf [fpPred' gls, tr], fpPred gls]
        res <- CHC.computeFP cfg (vars gls) (fixpointPred gls) init trans
        case res of
          Just alpha -> do
            alpha <- SMT.simplify cfg alpha
            alpha <- pure $ fglobally (fpred False alpha)
            st <- addImp cfg "Gen-Inv-P" dom st (gamma, alpha)
            gls <-
              pure
                $ gls
                    { chcMaxCache =
                        Map.insert (current dom st, dedInv dom st) (Just alpha) (chcMaxCache gls)
                    }
            pure (st, gls)
          Nothing -> do
            gls <-
              pure
                $ gls
                    { chcMaxCache =
                        Map.insert (current dom st, dedInv dom st) Nothing (chcMaxCache gls)
                    }
            pure (st, gls)
-------------------------------------------------------------------------------
