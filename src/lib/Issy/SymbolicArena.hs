---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.SymbolicArena
-- Description : Data structure and methods for arenas of symbolic games
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.SymbolicArena
  ( Arena
  , domain
  , locations
  , preds
  , predSet
  , trans
  , transList
  , locSet
  , locName
  , setDomain
  , usedSymbols
  , cyclicIn
  , pre
  , cpreEnv
  , cpreSys
  , variables
  , loopArena
  , simplifySG
  , setTrans
  , redirectTransTo
  , createLocsFor
  , addLoc
  , addSink
  , empty
  , succs
  , check
  , -- Solving
    removeAttrSys
  , removeAttrEnv
  , independentProgVars
  , inducedSubArena
  , isSubarenaFrom
  , addConstants
  , -- Synthesis
    syntCPre
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective(..))
import qualified Issy.Base.Objectives as Obj
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Utils.Extra hiding (reachables)
import Issy.Utils.Logging
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- Arena
---------------------------------------------------------------------------------------------------
data Arena = Arena
  { variables :: Variables
  , locations :: Locs.Store
  , aDomain :: Map Loc Term
  , transRel :: Map Loc (Map Loc Term)
  , predRel :: Map Loc (Set Loc)
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Accessors
---------------------------------------------------------------------------------------------------
domain :: Arena -> Loc -> Term
domain arena l = Map.findWithDefault FOL.false l (aDomain arena)

trans :: Arena -> Loc -> Loc -> Term
trans arena src trg =
  Map.findWithDefault FOL.false trg $ Map.findWithDefault Map.empty src $ transRel arena

transList :: Arena -> [(Loc, Loc, Term)]
transList =
  concatMap (\(src, sucs) -> map (\(trg, term) -> (src, trg, term)) (Map.toList sucs))
    . Map.toList
    . transRel

succs :: Arena -> Loc -> Set Loc
succs arena src =
  Set.fromList
    $ map fst
    $ filter ((/= FOL.false) . snd)
    $ Map.toList
    $ Map.findWithDefault Map.empty src
    $ transRel arena

succL :: Arena -> Loc -> [Loc]
succL arena = Set.toList . succs arena

preds :: Arena -> Loc -> Set Loc
preds arena l = Map.findWithDefault Set.empty l (predRel arena)

predSet :: Arena -> Set Loc -> Set Loc
predSet arena ls = Set.unions $ map (preds arena) $ Set.toList ls

locSet :: Arena -> Set Loc
locSet = Locs.toSet . locations

locName :: Arena -> Loc -> String
locName = Locs.name . locations

usedSymbols :: Arena -> Set Symbol
usedSymbols arena =
  Vars.allSymbols (variables arena)
    `Set.union` Set.unions (map FOL.symbols (concatMap Map.elems (Map.elems (transRel arena))))

---------------------------------------------------------------------------------------------------
-- Construction and basic moddification
---------------------------------------------------------------------------------------------------
empty :: Variables -> Arena
empty vars =
  Arena
    { variables = vars
    , locations = Locs.empty
    , aDomain = Map.empty
    , transRel = Map.empty
    , predRel = Map.empty
    }

addLoc :: Arena -> String -> (Arena, Loc)
addLoc arena name =
  let (newLoc, newStore) = Locs.add (locations arena) name
   in (arena {locations = newStore}, newLoc)

setDomain :: Arena -> Loc -> Term -> Arena
setDomain arena l dom
  | l `elem` Locs.toSet (locations arena) = arena {aDomain = Map.insert l dom (aDomain arena)}
  | otherwise = error "assert: try to set domain of undefined location!"

setTrans :: Arena -> Loc -> Loc -> Term -> Arena
setTrans arena src trg trans
  | trans == FOL.false = arena
  | not (FOL.frees trans `Set.isSubsetOf` Vars.allSymbols (variables arena)) =
    error "assert: try to set transition with unkown variabels"
  | otherwise =
    let newTransRel =
          Map.insert src (Map.insert trg trans (Map.findWithDefault Map.empty src (transRel arena)))
            $ transRel arena
        newPredRel = Map.insertWith Set.union trg (Set.singleton src) (predRel arena)
     in arena {transRel = newTransRel, predRel = newPredRel}

createLocsFor ::
     (Foldable t, Ord a) => Arena -> (a -> String) -> (a -> Term) -> t a -> (Arena, a -> Loc)
createLocsFor arena name dom =
  second (flip (Map.findWithDefault (error "assert: lookup non-mapped element")))
    . foldl
        (\(a, mp) e ->
           let (a', l) = addLoc a (name e)
            in (setDomain a' l (dom e), Map.insert e l mp))
        (arena, Map.empty)

addSink :: Arena -> (Arena, Loc)
addSink arena =
  let sinkName = FOL.uniqueName "sink" $ Set.map (locName arena) $ locSet arena
      (arena0, sink) = addLoc arena sinkName
      arena1 = setDomain arena0 sink FOL.true
   in (setTrans arena1 sink sink FOL.true, sink)

redirectTransTo :: Arena -> Loc -> Loc -> Arena
redirectTransTo arena src trg =
  arena
    { transRel = Map.insert src (Map.singleton trg FOL.true) $ transRel arena
    , predRel =
        Map.insertWith Set.union trg (Set.singleton src) $ Set.filter (/= src) <$> predRel arena
    }

---------------------------------------------------------------------------------------------------
-- Analysis
---------------------------------------------------------------------------------------------------
cyclicIn :: Arena -> Loc -> Bool
cyclicIn arena l = any (elem l . reachables arena) (succs arena l)

reachables :: Arena -> Loc -> Set Loc
reachables g l = bfs Set.empty (l `OL.pushOne` OL.empty)
  where
    bfs seen ol =
      case OL.pop ol of
        Nothing -> seen
        Just (o, ol')
          | o `elem` seen -> bfs seen ol'
          | otherwise ->
            let seen' = o `Set.insert` seen
             in bfs seen' ((succs g o `Set.difference` seen) `OL.push` ol')

---------------------------------------------------------------------------------------------------
-- Sanitize
---------------------------------------------------------------------------------------------------
check :: Config -> Arena -> IO (Maybe String)
check cfg a = go $ Set.toList $ locSet a
  where
    v = variables a
    go =
      \case
        [] -> pure Nothing
        l:lr -> do
                -- Check non-blocking condition from symbolic game structure definition
                -- The other one is uneccesary restrictive!
          c <-
            SMT.valid cfg
              $ Vars.forallX v
              $ FOL.impl (domain a l)
              $ Vars.existsI v
              $ Vars.existsX' v
              $ FOL.orfL (Set.toList (locSet a))
              $ \l' -> FOL.andf [Vars.primeT v (domain a l'), trans a l l']
          if c
            then go lr
            else pure $ Just $ locName a l ++ " might be blocking!"

---------------------------------------------------------------------------------------------------
-- Simplification
---------------------------------------------------------------------------------------------------
simplifyArena :: Config -> Arena -> IO Arena
simplifyArena cfg arena = do
  let filt mp = Map.filter (/= FOL.false) <$> mapM (SMT.simplify cfg) mp
  newDom <- filt (aDomain arena)
  let newTransRel = Map.map (Map.filter (/= FOL.false)) $ transRel arena -- TODO: Apply light simplification!
  arena <- pure $ arena {aDomain = newDom, transRel = newTransRel}
  let newPredRel =
        Map.mapWithKey (\l' -> Set.filter (\l -> trans arena l l' /= FOL.false)) (predRel arena)
  pure $ arena {predRel = newPredRel}

simplifySG :: Config -> (Arena, Objective) -> IO (Arena, Objective)
simplifySG cfg (arena, obj) = do
  arena <- simplifyArena cfg arena
  let notReachable = locSet arena `Set.difference` reachables arena (initialLoc obj)
  arena <- pure $ foldl (\a l -> setDomain a l FOL.false) arena notReachable
  let wc =
        Obj.mapWC
          (`Set.difference` notReachable)
          (\rank -> foldl (\r l -> Map.insert l 0 r) rank notReachable)
          (winningCond obj)
  pure (arena, obj {winningCond = wc})

---------------------------------------------------------------------------------------------------
-- (Enforcable) Predecessors
---------------------------------------------------------------------------------------------------
pre :: Arena -> SymSt -> Loc -> Term
pre a d l =
  let v = variables a
      f = Vars.existsI v $ FOL.andf [validInput a l, sysPre a l (SymSt.get d)]
   in FOL.andf [f, domain a l]

cpreEnv :: Arena -> SymSt -> Loc -> Term
cpreEnv a d l =
  let v = variables a
      f =
        Vars.existsI v
          $ FOL.andf
              [ validInput a l
              , Vars.forallX' v
                  $ FOL.andfL (succL a l)
                  $ \l' ->
                      FOL.andf [trans a l l', Vars.primeT v (domain a l')]
                        `FOL.impl` Vars.primeT v (SymSt.get d l')
              ]
   in FOL.andf [f, domain a l]

cpreSys :: Arena -> SymSt -> Loc -> Term
cpreSys a d l =
  let v = variables a
      f = Vars.forallI v $ FOL.impl (validInput a l) $ sysPre a l (SymSt.get d)
   in FOL.andf [f, domain a l]

validInput :: Arena -> Loc -> Term
validInput a l = sysPre a l (const FOL.true)

sysPre :: Arena -> Loc -> (Loc -> Term) -> Term
sysPre a l d =
  let v = variables a
   in Vars.existsX' v
        $ FOL.orfL (succL a l)
        $ \l' -> FOL.andf [trans a l l', Vars.primeT v (domain a l'), Vars.primeT v (d l')]

removeAttrSys :: Config -> SymSt -> Arena -> IO Arena
removeAttrSys conf st arena = do
  interSt <- SymSt.simplify conf $ SymSt.symSt (locSet arena) (\l -> sysPre arena l (SymSt.get st))
  arena <-
    pure
      $ foldl
          (\arena l -> setDomain arena l (FOL.andf [domain arena l, FOL.neg (SymSt.get st l)]))
          arena
          (locSet arena)
  let newTransRel =
        Map.mapWithKey
          (\l -> Map.map (\tr -> FOL.andf [tr, FOL.neg (SymSt.get interSt l)]))
          (transRel arena)
  simplifyArena conf $ arena {transRel = newTransRel}

removeAttrEnv :: Config -> SymSt -> Arena -> IO Arena
removeAttrEnv conf st arena =
  simplifyArena conf
    $ foldl
        (\arena l -> setDomain arena l (FOL.andf [domain arena l, FOL.neg (SymSt.get st l)]))
        arena
        (locSet arena)

---------------------------------------------------------------------------------------------------
-- Loop- and Subarena
---------------------------------------------------------------------------------------------------
loopArena :: Arena -> Loc -> (Arena, Loc)
loopArena arena l =
  let (arena0, l') = addLoc arena $ locName arena l ++ "'"
      arena1 = setDomain arena0 l' $ domain arena0 l
      (arena2, sink) = addSink arena1
      arena3 = setTrans arena2 l' sink FOL.true
      arena4 = foldl (moveTrans l l') arena3 $ preds arena l
   in (arena4, l')

moveTrans :: Loc -> Loc -> Arena -> Loc -> Arena
moveTrans old new arena l
  | domain arena old /= domain arena new =
    error "assert: moving transition only to same domain targets"
  | otherwise =
    let arena' = setTrans arena l new $ trans arena l old
     in arena'
          { transRel = Map.adjust (Map.delete old) l $ transRel arena'
          , predRel = Map.adjust (Set.delete l) old $ predRel arena'
          }

inducedSubArena :: Arena -> Set Loc -> (Arena, Loc -> Loc)
inducedSubArena arena locs
  | not (locs `Set.isSubsetOf` locSet arena) =
    error "assert: can only induced sub-arena on subset of locations!"
  | otherwise =
    let locsC = Set.unions (Set.map (succs arena) locs) `Set.union` locs
        (arena0, oldToNew) =
          createLocsFor (empty (variables arena)) (locName arena) (domain arena) locsC
        -- Add transitions 
        arena1 =
          foldl (\ar old -> setTrans ar (oldToNew old) (oldToNew old) FOL.true) arena0
            $ locsC `Set.difference` locs
        arena2 =
          foldl
            (\ar old ->
               foldl
                 (\ar old' -> setTrans ar (oldToNew old) (oldToNew old') (trans arena old old'))
                 ar
                 (succs arena old))
            arena1
            locs
        -- Create mappings for restricting locations only, not for the sinks
        mOldToNew l
          | l `elem` locs = oldToNew l
          | otherwise = error "assert: cannot map non-restricing location"
     in (arena2, mOldToNew)

independentProgVars :: Config -> Arena -> IO (Set Symbol)
independentProgVars cfg arena = do
  depends <- foldM indepTerm Set.empty $ map (\(_, _, term) -> term) $ transList arena
  pure $ Vars.stateVars vars `Set.difference` depends
  where
    vars = variables arena
    indepTerm depends term =
      foldM
        (indepVar term)
        depends
        (Set.filter (Vars.isStateVar (variables arena)) (FOL.frees term))
    indepVar term depends v
      | v `elem` depends = pure depends
      | otherwise = do
        let vt = Vars.mk vars v
        res <- SMT.valid cfg $ term `FOL.impl` FOL.equal vt (Vars.primeT vars vt)
        pure
          $ if res
              then depends
              else Set.insert v depends

isSubarenaFrom :: (Loc, Arena) -> (Loc, Arena) -> Maybe (Loc -> Loc)
isSubarenaFrom (ls, arenaS) (l, arena) =
  case go Set.empty (OL.pushOne (ls, l) OL.empty) of
    Nothing -> Nothing
    Just mp -> Just (mp !)
  where
    go isos ol =
      case OL.pop ol of
        Nothing -> Just $ mapFromSet isos
        Just ((ls, l), _)
          | domain arenaS ls /= domain arena l -> Nothing
          | otherwise -> error "TODO This is not trivial after all!"

addConstants :: [(Symbol, Sort)] -> Arena -> Arena
addConstants cvars arena =
  let newVars = foldl (uncurry . Vars.addStateVar) (variables arena) cvars
      eqCond = FOL.andfL cvars (\(v, s) -> FOL.var v s `FOL.equal` FOL.var (Vars.prime v) s)
   in arena
        {variables = newVars, transRel = Map.map (\t -> FOL.andf [t, eqCond]) <$> transRel arena}

---------------------------------------------------------------------------------------------------
-- Synthesis
---------------------------------------------------------------------------------------------------
syntCPre ::
     Config -> Arena -> Symbol -> (Loc -> Term) -> Loc -> Term -> SymSt -> IO [(Symbol, Term)]
syntCPre conf arena locVar toLoc loc cond targ = do
  let vs = variables arena
  let skolem = skolemFuncs arena locVar cond targ
  let preCond = FOL.andf [validInput arena loc, cond, domain arena loc]
  let postCond =
        FOL.orfL (succL arena loc) $ \loc' ->
          FOL.andf
            [ FOL.equal (FOL.ivarT locVar) (toLoc loc')
            , trans arena loc loc'
            , Vars.primeT vs (domain arena loc')
            , Vars.primeT vs (SymSt.get targ loc')
            ]
  lgd conf ["Synthesize in", locName arena loc, "on", SymSt.toString (locName arena) targ]
  let doElim (elimRes, skolemRes, postCond) var
        | var `notElem` FOL.frees postCond = pure (elimRes, skolemRes, postCond)
        | otherwise = do
          t <- syntElim conf vs var preCond postCond
          case t of
            Nothing -> pure (elimRes, (Vars.unprime var, skolem var) : skolemRes, postCond)
            Just t -> do
              postCond <- SMT.simplify conf $ FOL.mapTerm (\v _ -> justOn (v == var) t) postCond
              pure ((Vars.unprime var, t) : elimRes, skolemRes, postCond)
  (elimRes, skolemRes, postCond) <- foldM doElim ([], [], postCond) (locVar : Vars.stateVarL' vs)
  postCond <-
    pure $ FOL.mapTerm (\v _ -> justOn (Vars.isPrimed v || v == locVar) (skolem v)) postCond
  let f = FOL.impl preCond postCond
  let query = FOL.pushdownQE $ FOL.forAll (Set.toList (FOL.frees f)) f
  if null skolemRes
    then pure elimRes
    else do
      model <- SMT.satModel conf query
      case model of
        Nothing -> die "synthesis failure: could not compute skolem function!"
        Just model -> do
          lgv conf ["Skolem model", show model]
          pure $ elimRes ++ map (second (FOL.setModel model)) skolemRes

syntElim :: Config -> Variables -> Symbol -> Term -> Term -> IO (Maybe Term)
syntElim conf vars var preCond postCond = do
  let equals = Set.filter (not . any Vars.isPrimed . FOL.frees) $ FOL.equalitiesFor var postCond
  lgd conf ["For", var, "use equalties", strS SMTLib.toString equals]
  res <- go preCond $ Set.toList equals
  case res of
    Nothing -> lgd conf ["Failed to derive skolem function"]
    Just res -> lgd conf ["Derive skolem function", var, ":=", SMTLib.toString res]
  pure res
  where
    go preCond =
      \case
        [] -> pure Nothing
        eq:eqr -> do
          let condSet = Vars.existsX' vars $ FOL.mapTerm (\v _ -> justOn (v == var) eq) postCond
          condSet <- SMT.simplify conf condSet
          satT <- SMT.sat conf condSet
          preCond' <- SMT.simplify conf $ FOL.andf [preCond, FOL.neg condSet]
          satE <- SMT.sat conf preCond'
          if satT
            then if satE
                   then fmap (FOL.ite condSet eq) <$> go preCond' eqr
                   else pure $ Just eq
            else go preCond eqr

skolemFuncs :: Arena -> Symbol -> Term -> SymSt -> Symbol -> Term
skolemFuncs arena locVar cond targ =
  let syms =
        Set.insert locVar
          $ Set.union (FOL.symbols cond)
          $ usedSymbols arena `Set.union` SymSt.symbols targ
      skolemPref = FOL.uniquePrefix "skolem_" syms
    -- Build type and arguments for skolem functions
      vs = variables arena
      inputSL = (\v -> (v, Vars.sortOf vs v)) <$> Vars.inputL vs
      stateSL = (\v -> (v, Vars.sortOf vs v)) <$> Vars.stateVarL vs
      newSL = getNewVars vs targ
      args = stateSL ++ inputSL ++ newSL
    -- Build skolem functions for variables and location
      skolem var
        | Vars.isPrimed var =
          FOL.unintFunc (skolemPref ++ Vars.unprime var) (Vars.sortOf vs var) args
        | var == locVar = FOL.unintFunc (skolemPref ++ locVar) FOL.SInt args
        | otherwise = error "assert: unreachable code"
   in skolem

getNewVars :: Variables -> SymSt -> [(Symbol, Sort)]
getNewVars vars =
  filter (\(v, _) -> not (Vars.isInput vars v || Vars.isStateVar vars v))
    . Set.toList
    . Set.fromList
    . concatMap (Map.toList . FOL.bindings . snd)
    . SymSt.toList
