-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Monitor.Rules
  ( applyRules
  , Context
  , context
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
import Issy.Base.Variables
import Issy.Config
  ( Config
  , rulesDeduction
  , rulesDeductionPrecise
  , rulesSaturation
  , rulesSubsitution
  , rulesUnsatChecks
  , setName
  )
import Issy.Logic.FOL
import Issy.Logic.SMT
import Issy.Monitor.CHC
import Issy.Monitor.Fixpoints
import Issy.Monitor.Formula
import Issy.Monitor.State
import Issy.Utils.Extra
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- Overall
-------------------------------------------------------------------------------
applyRules :: Config -> Context -> State -> IO (State, Context)
applyRules cfg ctx st
  | isFalse st || isTrue st = pure (st, ctx)
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
    (st, ctx) <- first normSt <$> overall cfg ctx Set.empty (reorganise st)
    lg cfg ["Finished rules with", stateToString st]
    pure (st, ctx)

-------------------------------------------------------------------------------
-- Context
-------------------------------------------------------------------------------
-- TODO: Maybe rename
data Context = Context
  { vars :: Variables
  , sortedStateVarL :: [(Symbol, Sort)]
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

baseContext :: Variables -> Context
baseContext vars =
  let fpn = uniqueName "fixpointpred" (allSymbols vars)
      stv = (\v -> (v, sortOf vars v)) <$> stateVarL vars
   in Context
        { vars = vars
        , sortedStateVarL = stv
        , fixpointPred = fpn
        , fpPred = Func (UnintF fpn) $ map (uncurry Var) stv
        , fpPred' = primeT vars $ Func (UnintF fpn) $ map (uncurry Var) stv
            --
        , aux = []
        , updateEncodes = Map.empty
        , exactlyOneUpd = true
        , updateEffect = true
            --
        , genReaches = Map.empty
        , unsatCache = Map.empty
        , implCache = Map.empty
        , muvalUnsat = Set.empty
        , chcCache = Map.empty
        , chcMaxCache = Map.empty
        }

context :: Variables -> Set (Symbol, Term) -> Context
context vars updates =
  let complUpd = updates `Set.union` Set.map (\v -> (v, Var v (sortOf vars v))) (stateVars vars)
      prefUpd = uniquePrefix "update" (allSymbols vars)
      updAux = intmapSet (\n upd -> (upd, prefUpd ++ show n)) complUpd
   in (baseContext vars)
        { updateEncodes = Map.fromList updAux
        , aux = map snd updAux
        , exactlyOneUpd =
            andf
              $ map
                  (\var -> exactlyOne (map (bvarT . snd) (filter ((== var) . fst . fst) updAux)))
                  (stateVarL vars)
        , updateEffect =
            andf
              $ map
                  (\((var, term), aux) ->
                     bvarT aux `impl` (Var (prime var) (sortOf vars var) `equal` term))
                  updAux
        }

-------------------------------------------------------------------------------
-- Rule Apllication Framework
-------------------------------------------------------------------------------
-- TODO: Maybe make state to (State, Context) and rname context
type Rule = Config -> Context -> Set (Domain, Formula, Formula) -> State -> IO (State, Context)

type SRule
  = Config -> Context -> Set (Domain, Formula, Formula) -> Domain -> State -> IO (State, Context)

type PRule = Config -> Context -> Domain -> State -> IO State

liftS :: SRule -> Rule
liftS rule cfg ctx new st = do
  (st, ctx) <- rule cfg ctx new Assumptions st
  rule cfg ctx new Guarantees st

liftP :: PRule -> Rule
liftP rule =
  liftS $ \cfg ctx _ dom st -> do
    st <- rule cfg ctx dom st
    pure (st, ctx)

ruleFP :: Rule -> Rule
ruleFP rule cfg ctx new st
  | null new || isTrue st || isFalse st = pure (st, ctx)
  | otherwise = do
    (st', ctx) <- first simpleNormSt <$> rule cfg ctx new st
    let generated = newImps st st'
    ruleFP rule cfg ctx generated st'

ruleChain :: [Rule] -> Rule
ruleChain rules cfg ctx new st
  | isTrue st || isFalse st = pure (st, ctx)
  | otherwise =
    case rules of
      [] -> pure (st, ctx)
      rule:rules -> do
        (st', ctx) <- first simpleNormSt <$> rule cfg ctx new st
        let generated = newImps st st'
        ruleChain rules cfg ctx generated st'

ruleChainAccum :: [Rule] -> Rule
ruleChainAccum rules cfg ctx new st
  | isTrue st || isFalse st = pure (st, ctx)
  | otherwise =
    case rules of
      [] -> pure (st, ctx)
      rule:rules -> do
        (st', ctx) <- first simpleNormSt <$> rule cfg ctx new st
        let generated = newImps st st'
        ruleChainAccum rules cfg ctx (generated `Set.union` new) st'

ruleG :: Bool -> Rule -> Rule
ruleG True = id
ruleG False = \_ _ ctx _ st -> pure (st, ctx)

-------------------------------------------------------------------------------
-- State Acessors / Helper Methods 
-- TODO reorganise and check with context
-------------------------------------------------------------------------------
deducedInvariant :: Config -> Context -> Domain -> State -> IO Term
deducedInvariant cfg ctx dom st =
  simplify cfg $ encode ctx $ fand $ filter (staticFormula (vars ctx)) $ dedInv dom st

derivedEventually :: Config -> Context -> Domain -> State -> IO ([Formula], Context)
derivedEventually cfg ctx dom st = first nub <$> foldM go ([], ctx) (impD dom st)
  where
    go (derived, ctx) =
      \case
        (gamma, FEventually alpha)
          | notTemporal alpha ->
            ifQuery
              (checkImpl cfg ctx (fand (current dom st ++ dedInv dom st)) gamma)
              (alpha : derived)
              derived
          | otherwise -> pure (derived, ctx)
        _ -> pure (derived, ctx)

unsatDedInv :: Config -> Context -> Domain -> State -> [Formula] -> IO (Bool, Context)
unsatDedInv cfg ctx dom st fs = checkUnsat cfg ctx $ fs ++ dedInv dom st

encode :: Context -> Formula -> Term
encode ctx = encodeFormula (updateEncodes ctx !)

checkImpl :: Config -> Context -> Formula -> Formula -> IO (Bool, Context)
checkImpl cfg ctx a b
  | b == FTrue = pure (True, ctx)
  | a == FFalse = pure (True, ctx)
  | a == b = pure (True, ctx)
  | otherwise =
    case implCache ctx !? (a, b) of
      Just res -> pure (res, ctx)
      Nothing -> do
        res <- valid cfg $ andf [encode ctx a, exactlyOneUpd ctx] `impl` encode ctx b
        pure (res, ctx {implCache = Map.insert (a, b) res (implCache ctx)})

checkUnsat :: Config -> Context -> [Formula] -> IO (Bool, Context)
checkUnsat _ ctx [] = pure (False, ctx)
checkUnsat cfg ctx fs =
  case unsatCache ctx !? fs of
    Just res -> pure (res, ctx)
    Nothing -> do
      res <- unsat cfg $ andf $ exactlyOneUpd ctx : map (encode ctx) fs
      pure (res, ctx {unsatCache = Map.insert fs res (unsatCache ctx)})

callCHC :: Config -> Context -> [([Term], Term)] -> IO (Maybe Bool, Context)
callCHC cfg ctx query = do
  case chcCache ctx !? query of
    Just res -> pure (Just res, ctx)
    Nothing -> do
      res <- checkCHC cfg (fixpointPred ctx) (sortOf (vars ctx) <$> stateVarL (vars ctx)) query
      pure
        $ case res of
            Nothing -> (Nothing, ctx)
            Just res -> (Just res, ctx {chcCache = Map.insert query res (chcCache ctx)})

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
groupImps cfg ctx new dom st = do
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
         if staticFormula (vars ctx) p
           then do
             p <- simplify cfg $ staticFormulaToTerm p
             pure (fpred True p, c)
           else pure (p, c))
      merges
  st <- foldM (addImp cfg "group-imp" dom) st merges
  pure (st, ctx)

deriveImplications :: SRule
deriveImplications cfg ctx new dom st = do
  lg cfg ["Apply chain/chain-F/chain-X to", show dom]
  let pairs = Set.toList $ newPairs (filterDom dom new) (impD dom st)
  (derived, ctx) <-
    foldM
      (\(derived, ctx) impl -> do
         (res, ctx) <- chainRule cfg ctx impl
         pure (maybe derived (`Set.insert` derived) res, ctx))
      (Set.empty, ctx)
      pairs
  st <- foldM (addImp cfg "Chain-PFX" dom) st derived
  pure (st, ctx)

chainRule ::
     Config
  -> Context
  -> ((Formula, Formula), (Formula, Formula))
  -> IO (Maybe (Formula, Formula), Context)
chainRule cfg ctx ((a, b1), (b2, phi))
  | b2 == FTrue = pure (Nothing, ctx)
  | otherwise =
    case b1 of
      FEventually b1 -> eval b1 (a, feventually phi)
      FNext b1 -> eval b1 (a, fnext phi)
      b1 -> eval b1 (a, phi)
  where
    eval b1 res
      | notTemporal b1 = ifQuery (checkImpl cfg ctx b1 b2) (Just res) Nothing
      | otherwise = pure (Nothing, ctx)

newPairs :: Ord a => Set a -> Set a -> Set (a, a)
newPairs new base =
  Set.filter (\(x, y) -> x `elem` base && y `elem` base && x /= y)
    $ cartesianProduct new base `Set.union` cartesianProduct base new

liftGloballies :: SRule
liftGloballies cfg ctx _ dom st = foldM (liftGlobally cfg dom) (st, ctx) (impD dom st)

liftGlobally :: Config -> Domain -> (State, Context) -> (Formula, Formula) -> IO (State, Context)
liftGlobally cfg dom (st, ctx) =
  \case
    (a, FGlobally b)
      | (ftrue, b) `elem` impD dom st -> pure (st, ctx)
      | otherwise -> do
        (res, ctx) <- checkImpl cfg ctx (fand (current dom st)) a
        if res
          then do
            st <- addImp cfg "Lift-G" dom st (ftrue, b)
            pure (st, ctx)
          else pure (st, ctx)
    _ -> pure (st, ctx)

propagateWeaks :: SRule
propagateWeaks cfg ctx _ dom st = do
  lg cfg ["Apply propagate-W to", show dom]
  let weak = weaks dom st
  let weakPairs = commutativePairs weak
  foldM (propagateWeak cfg dom) (st, ctx) weakPairs

propagateWeak ::
     Config
  -> Domain
  -> (State, Context)
  -> ((Formula, Formula), (Formula, Formula))
  -> IO (State, Context)
propagateWeak cfg dom (st, ctx) ((a1, b1), (a2, b2)) = do
  (res, ctx) <- chain ctx [[b1, b2], [a1, b2], [a2, b1]]
  st <-
    if res
      then addImp cfg "propagate-W" dom st (ftrue, fand [a1, a2])
      else pure st
  pure (st, ctx)
  where
    chain ctx =
      \case
        [] -> pure (True, ctx)
        f:fr -> do
          (res, ctx) <- unsatDedInv cfg ctx dom st f
          if res
            then chain ctx fr
            else pure (False, ctx)

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
checkGlobalUnsat cfg ctx _ dom st = do
  lg cfg ["Apply Subst-UNSAT to", show dom]
  ifQuery (unsatDedInv cfg ctx dom st (current dom st)) (invalidate dom st) st

unsatLiveness :: SRule
unsatLiveness cfg ctx _ dom st = do
  lg cfg ["Apply Subst-UNSAT-Live to", show dom]
  (lives, ctx) <- derivedEventually cfg ctx dom st
  let check (usat, ctx) live
        | usat = pure (True, ctx)
        | otherwise = unsatDedInv cfg ctx dom st [live]
  ifQuery (foldM check (False, ctx) lives) (invalidate dom st) st

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
substConst cfg ctx _ dom st = do
  lg cfg ["Apply subst-TB to", show dom]
  foldM substTerm (st, ctx) $ Set.unions $ map findTerms $ fset dom st
  where
    substTerm (st, ctx) term = do
      let query ctx pol = unsatDedInv cfg ctx dom st [fpred pol term]
      (res, ctx) <- query ctx True
      if res
        then pure (mapFs dom st (substT (term, False)), ctx)
        else ifQuery (query ctx False) (mapFs dom st (substT (term, True))) st

substImpl :: SRule
substImpl cfg ctx _ dom st = do
  lg cfg ["Apply simplify-non-nested to", show dom]
  foldM subst (st, ctx) (impD dom st)
  where
    substitutable = Set.unions $ map notNestedSubForms (fset dom st)
    --
    subst (st, ctx) (gamma, phi)
      | phi `elem` substitutable =
        ifQuery
          (checkImpl cfg ctx (fand (current dom st ++ dedInv dom st)) gamma)
          (mapFs dom st (substNotNested phi ftrue))
          st
      | otherwise = pure (st, ctx)

-------------------------------------------------------------------------------
-- Deduction Rules
-------------------------------------------------------------------------------
deduceInv :: SRule
deduceInv cfg ctx _ dom st = do
  lg cfg ["Apply Gen-Inv rules to", show dom]
  let pot = Set.unions $ map findPotInv (fset dom st)
  foldM (genInv cfg dom) (st, ctx) pot

genInv :: Config -> Domain -> (State, Context) -> Formula -> IO (State, Context)
genInv cfg dom (st, ctx) alpha
  | (ftrue, alpha) `elem` impD dom st = pure (st, ctx)
  | stateOnly (isStateVar (vars ctx)) alpha =
    let fp = fpPred ctx
        fp' = fpPred' ctx
        gammaE = encode ctx $ fand $ current dom st
        alphaE = encode ctx alpha
        init = ([gammaE], fp)
        trans = ([fp, exactlyOneUpd ctx, updateEffect ctx] ++ map (encode ctx) (dedInv dom st), fp')
        exclude = ([neg alphaE, fp], false)
        query = [init, trans, exclude]
     in do
          (res, ctx) <- callCHC cfg ctx query
          case res of
            Just True -> do
              st <- addImp cfg "Gen-Inv" dom st (ftrue, alpha)
              pure (st, ctx)
            _ -> pure (st, ctx)
  | otherwise = pure (st, ctx)

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
deduceLiveness cfg ctx _ dom st = do
  lg cfg ["Apply Gen-Reach rules to", show dom]
  let cached = Map.findWithDefault Set.empty (dedInv dom st) (genReaches ctx)
  -- TODO: guard and don't add existing stuff
  st <- foldM (addImp cfg "Gen-Reach-Prop" dom) st cached
  let cand = searchLiveness ctx (current dom st) (fset dom st ++ eset dom st)
  foldM (genReach cfg dom) (st, ctx) cand

genReach :: Config -> Domain -> (State, Context) -> (Formula, Formula) -> IO (State, Context)
genReach cfg dom (st, ctx) (gamma, beta)
  | (gamma, feventually beta) `elem` impD dom st = pure (st, ctx)
  | (dedInv dom st, gamma, feventually beta) `elem` muvalUnsat ctx = pure (st, ctx)
  | stateOnly (isStateVar (vars ctx)) beta && stateOnly (isStateVar (vars ctx)) gamma = do
    let query = forallX (vars ctx) $ encode ctx gamma `impl` fpPred ctx
        fp =
          orf
            [ encode ctx beta
            , forAll (inputL (vars ctx) ++ aux ctx ++ stateVarL' (vars ctx))
                $ andf (map (encode ctx) (dedInv dom st) ++ [exactlyOneUpd ctx, updateEffect ctx])
                    `impl` fpPred' ctx
            ]
    res <- checkFPInclusion cfg query (fixpointPred ctx) (sortedStateVarL ctx) fp
    if res
      then do
        st <- addImp cfg "Gen-Reach" dom st (gamma, feventually beta)
        pure
          ( st
          , ctx
              { genReaches =
                  Map.insertWith
                    Set.union
                    (dedInv dom st)
                    (Set.singleton (gamma, feventually beta))
                    (genReaches ctx)
              })
      else pure
             ( st
             , ctx
                 {muvalUnsat = (dedInv dom st, gamma, feventually beta) `Set.insert` muvalUnsat ctx})
  | otherwise = pure (st, ctx)

-- TODO: How about nested stuff?
searchLiveness :: Context -> [Formula] -> [Formula] -> Set (Formula, Formula)
searchLiveness ctx currents = Set.unions . map go
  where
    current = fand $ filter (stateOnly (isStateVar (vars ctx))) currents
    go =
      \case
        FGlobally f
          | notTemporal f -> Set.singleton (current, fnot f)
          | otherwise -> go f
        FEventually f
          | notTemporal f -> Set.singleton (current, f)
          | otherwise -> Set.empty
        FOr [f, FEventually g]
          | notTemporal f && notTemporal g -> Set.fromList [(fnot f, g), (current, g)]
          | otherwise -> go f `Set.union` go (FEventually g)
        FOr [FEventually g, f]
          | notTemporal f && notTemporal g -> Set.fromList [(fnot f, g), (current, g)]
          | otherwise -> go f `Set.union` go (FEventually g)
        FAnd fs -> Set.unions $ map go fs
        FOr fs -> Set.unions $ map go fs
        _ -> Set.empty

deducePreciseInv :: SRule
deducePreciseInv cfg ctx _ dom st = do
  lg cfg ["Apply Gen-Inv-P rules to", show dom]
  genInvPrec cfg ctx dom st

genInvPrec :: Config -> Context -> Domain -> State -> IO (State, Context)
genInvPrec cfg ctx dom st
  | (current dom st, dedInv dom st) `Map.member` chcMaxCache ctx =
    case chcMaxCache ctx ! (current dom st, dedInv dom st) of
      Just alpha -> do
        let gamma = fand $ current dom st
        st <- addImp cfg "Gen-Inv-P" dom st (gamma, alpha)
        pure (st, ctx)
      Nothing -> pure (st, ctx)
  | otherwise = do
    let gamma = fand $ current dom st
    let base = encode ctx $ fand $ gamma : dedInv dom st
    base <- simplify cfg $ existsI (vars ctx) $ exists (aux ctx) base
    if base == true || base == false
      then pure (st, ctx)
      else do
        let init = forallX (vars ctx) $ func "=>" [andf [base, fpPred ctx], false]
            -- Transtion condition in CHC
        let tr = andf $ exactlyOneUpd ctx : updateEffect ctx : (encode ctx <$> dedInv dom st)
        let trans =
              forallX (vars ctx)
                $ forallI (vars ctx)
                $ forAll (aux ctx)
                $ forallX' (vars ctx)
                $ func "=>" [andf [fpPred' ctx, tr], fpPred ctx]
        res <- computeFP cfg (fixpointPred ctx) (sortedStateVarL ctx) init trans
        case res of
          Just alpha -> do
            alpha <- simplify cfg alpha
            alpha <- pure $ fglobally (fpred False alpha)
            st <- addImp cfg "Gen-Inv-P" dom st (gamma, alpha)
            ctx <-
              pure
                $ ctx
                    { chcMaxCache =
                        Map.insert (current dom st, dedInv dom st) (Just alpha) (chcMaxCache ctx)
                    }
            pure (st, ctx)
          Nothing -> do
            ctx <-
              pure
                $ ctx
                    { chcMaxCache =
                        Map.insert (current dom st, dedInv dom st) Nothing (chcMaxCache ctx)
                    }
            pure (st, ctx)
-------------------------------------------------------------------------------
