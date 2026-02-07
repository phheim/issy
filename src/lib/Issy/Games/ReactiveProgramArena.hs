---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Games.ReactiveProgramArena
-- Description : Data structure and methods for reactive program games
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Games.ReactiveProgramArena
  ( RPArena
  , Loc
  , -- Transition
    Transition(..)
  , succT
  , mapTerms
  , selfLoop
  , -- Access
    variables
  , locations
  , locationSet
  , locName
  , inv
  , trans
  , preds
  , predSet
  , succs
  , usedSymbols
  , -- Construction
    empty
  , addLocation
  , addTransition
  , addSink
  , createLocsFor
  , addConstants
  , -- Analysis
    cyclicIn
  , isSelfUpdate
  , -- Simplification
    simplifyRPG
  , -- Predecessors
    removeAttrSys
  , removeAttrEnv
  , pre
  , cpreEnv
  , cpreSys
  , -- Loop- and Subarena
    loopArena
  , independentProgVars
  , inducedSubArena
  , -- Synthesis
    syntCPre
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad (liftM2)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.Locations as Locs
import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Utils.Extra hiding (reachables)
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- RPG Transitions
---------------------------------------------------------------------------------------------------
-- | If-then-else-tree shaped representation of a transition in a reactive program arena.
data Transition
  = TIf Term Transition Transition
  -- ^ guarded branch on some quantifier-free formula
  | TSys [(Map Symbol Term, Loc)]
  -- ^ system selection with not-empty and unique mapping
  deriving (Eq, Ord, Show)

-- | Return all the successor locations of a transition.
succT :: Transition -> Set Loc
succT =
  \case
    TIf _ tt te -> succT tt `Set.union` succT te
    TSys choices -> Set.fromList (snd <$> choices)

-- | Moddify all terms in a transitions, both predicate terms as
-- well as update terms.
mapTerms :: (Term -> Term) -> Transition -> Transition
mapTerms m =
  \case
    TIf p tt te -> TIf (m p) (mapTerms m tt) (mapTerms m te)
    TSys upds -> TSys $ map (first (fmap m)) upds

-- | Moddify all updates of a transition.
mapUpdates :: (Map Symbol Term -> Map Symbol Term) -> Transition -> Transition
mapUpdates m = go
  where
    go (TIf p tt te) = TIf p (go tt) (go te)
    go (TSys upds) = TSys $ map (first m) upds

-- | Create a self-loop transition.
selfLoop :: Loc -> Transition
selfLoop l = TSys [(Map.empty, l)]

---------------------------------------------------------------------------------------------------
-- Arena
---------------------------------------------------------------------------------------------------
data RPArena = RPArena
  { locationSet :: Locs.Store
  , variables :: Variables
  , transRel :: Map Loc Transition
  , predecessors :: Map Loc (Set Loc)
  , invariant :: Map Loc Term
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Accessors
---------------------------------------------------------------------------------------------------
locations :: RPArena -> Set Loc
locations = Locs.toSet . locationSet

inv :: RPArena -> Loc -> Term
inv g l = fromMaybe FOL.true $ invariant g !? l

locName :: RPArena -> Loc -> String
locName = Locs.name . locationSet

trans :: RPArena -> Loc -> Transition
trans g l = fromMaybe (selfLoop l) $ transRel g !? l

preds :: RPArena -> Loc -> Set Loc
preds g l = Map.findWithDefault Set.empty l (predecessors g)

succs :: RPArena -> Loc -> Set Loc
succs g l = maybe Set.empty succT (transRel g !? l)

predSet :: RPArena -> Set Loc -> Set Loc
predSet g ls = Set.unions (Set.map (preds g) ls)

usedSymbols :: RPArena -> Set Symbol
usedSymbols g =
  Set.union (Vars.allSymbols (variables g))
    $ Set.unions
    $ Map.elems (symTrans <$> transRel g) ++ map (FOL.symbols . snd) (Map.toList (invariant g))
  where
    symTrans =
      \case
        TIf p t1 t2 -> Set.unions [FOL.symbols p, symTrans t1, symTrans t2]
        TSys choices -> Set.unions (concatMap (map (FOL.symbols . snd) . Map.toList . fst) choices)

---------------------------------------------------------------------------------------------------
-- Construction and basic modification
---------------------------------------------------------------------------------------------------
empty :: Variables -> RPArena
empty vars =
  RPArena
    { locationSet = Locs.empty
    , variables = vars
    , transRel = Map.empty
    , predecessors = Map.empty
    , invariant = Map.empty
    }

setInv :: RPArena -> Loc -> Term -> RPArena
setInv g l i = g {invariant = Map.insert l i (invariant g)}

addLocation :: RPArena -> String -> (RPArena, Loc)
addLocation g name =
  let (newLoc, locSet) = Locs.add (locationSet g) name
   in (g {locationSet = locSet}, newLoc)

addTransition :: RPArena -> Loc -> Transition -> Maybe RPArena
addTransition g l t
  | l `Map.member` transRel g = Nothing
  | otherwise = Just $ foldl (addPred l) (g {transRel = Map.insert l t (transRel g)}) (succT t)
  where
    addPred pre g suc =
      g {predecessors = Map.insertWith Set.union suc (Set.singleton pre) (predecessors g)}

createLocsFor ::
     (Foldable t, Ord a) => RPArena -> (a -> String) -> (a -> Term) -> t a -> (RPArena, a -> Loc)
createLocsFor arena name inv =
  second (flip (Map.findWithDefault (error "assert: lookup non-mapped element")))
    . foldl
        (\(g, mp) e ->
           let (g', l) = addLocation g (name e)
            in (setInv g' l (inv e), Map.insert e l mp))
        (arena, Map.empty)

addSink :: RPArena -> String -> (RPArena, Loc)
addSink g name =
  let (g', sink) = addLocation g name
   in ( g'
          { transRel = Map.insert sink (selfLoop sink) (transRel g')
          , predecessors = Map.insert sink (Set.singleton sink) (predecessors g')
          }
      , sink)

addConstants :: [(Symbol, Sort)] -> RPArena -> RPArena
addConstants cvars arena =
  arena
    { variables = foldl (uncurry . Vars.addStateVar) (variables arena) cvars
    , transRel = Map.map (mapUpdates addEqUpd) $ transRel arena
    }
  where
    addEqUpd upd = foldr (\(v, s) -> Map.insert v (FOL.var v s)) upd cvars

---------------------------------------------------------------------------------------------------
-- Anaysis
---------------------------------------------------------------------------------------------------
cyclicIn :: RPArena -> Loc -> Bool
cyclicIn g start = any (elem start . reachables g) (succs g start)

reachables :: RPArena -> Loc -> Set Loc
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

isSelfUpdate :: (Symbol, Term) -> Bool
isSelfUpdate =
  \case
    (v, FOL.Var v' _) -> v == v'
    _ -> False

---------------------------------------------------------------------------------------------------
-- Simplification
---------------------------------------------------------------------------------------------------
simplifyRPG :: Config -> (RPArena, Objective) -> IO (RPArena, Objective)
simplifyRPG cfg (arena, wc) = do
  newTrans <- mapM (simplifyTransition cfg) (transRel arena)
  let next l = fromMaybe (error ("assert: location not mapped " ++ show l)) $ newTrans !? l
  arena <-
    pure
      $ arena
          {transRel = newTrans, predecessors = predecessorRelation (succT . next) (locations arena)}
  pure (pruneUnreachables (Obj.initialLoc wc) arena, wc)

simplifyTransition :: Config -> Transition -> IO Transition
simplifyTransition cfg = go [FOL.true]
  where
    go cond =
      \case
        TSys upd -> return $ TSys $ nub $ map (first simplifyUpdates) upd
        TIf p tt tf ->
          let rectt = go (p : cond) tt
              rectf = go (FOL.neg p : cond) tf
           in ifM (SMT.unsat cfg (FOL.andf (p : cond))) rectf
                $ ifM (SMT.unsat cfg (FOL.andf (FOL.neg p : cond))) rectt
                $ liftM2 (TIf p) rectt rectf

simplifyUpdates :: Map Symbol Term -> Map Symbol Term
simplifyUpdates =
  Map.filterWithKey $ \var ->
    \case
      FOL.Var v _ -> v /= var
      _ -> True

pruneUnreachables :: Loc -> RPArena -> RPArena
pruneUnreachables init g = foldl disableLoc g $ locations g `Set.difference` reachables g init
  where
    disableLoc :: RPArena -> Loc -> RPArena
    disableLoc g l =
      g
        { invariant = Map.insert l FOL.false (invariant g)
        , transRel = Map.insert l (selfLoop l) (transRel g)
        , predecessors = Map.insert l (Set.singleton l) $ Set.filter (/= l) <$> predecessors g
        }

---------------------------------------------------------------------------------------------------
-- (Enforcable) Predecessors
---------------------------------------------------------------------------------------------------
pre :: RPArena -> SymSt -> Loc -> Term
pre g st l =
  FOL.andf
    [g `inv` l, Vars.existsI (variables g) (FOL.andf [validInput g l, sysPre g l (SymSt.get st)])]

cpreSys :: RPArena -> SymSt -> Loc -> Term
cpreSys g st l =
  FOL.andf
    [g `inv` l, Vars.forallI (variables g) (validInput g l `FOL.impl` sysPre g l (SymSt.get st))]

cpreEnv :: RPArena -> SymSt -> Loc -> Term
cpreEnv g st l =
  FOL.andf [g `inv` l, Vars.existsI (variables g) (FOL.andf [validInput g l, cpreET (trans g l)])]
  where
    cpreET =
      \case
        TIf p tt te -> FOL.ite p (cpreET tt) (cpreET te)
        TSys upds ->
          FOL.andf [FOL.mapTermM u ((g `inv` l) `FOL.impl` (st `SymSt.get` l)) | (u, l) <- upds]

sysPre :: RPArena -> Loc -> (Loc -> Term) -> Term
sysPre arena l d = go (trans arena l)
  where
    go =
      \case
        TIf p tt te -> FOL.ite p (go tt) (go te)
        TSys upds -> FOL.orf [FOL.mapTermM u (FOL.andf [d l, arena `inv` l]) | (u, l) <- upds]

validInput :: RPArena -> Loc -> Term
validInput g l = go (trans g l)
  where
    go =
      \case
        TIf p tt te -> FOL.ite p (go tt) (go te)
        TSys upds -> FOL.orf [FOL.mapTermM u (g `inv` l) | (u, l) <- upds]

removeAttrSys :: Config -> SymSt -> RPArena -> IO RPArena
removeAttrSys conf st arena = do
  interSt <-
    SymSt.simplify conf $ SymSt.symSt (locations arena) (\l -> sysPre arena l (SymSt.get st))
  arena <- removeAttrEnv conf st arena
  foldM
    (\arena l -> do
       newTrans <- simplifyTransition conf (TIf (interSt `SymSt.get` l) (TSys []) (trans arena l))
       pure (arena {transRel = Map.insert l newTrans (transRel arena)}))
    arena
    (locations arena)

removeAttrEnv :: Config -> SymSt -> RPArena -> IO RPArena
removeAttrEnv conf st arena = do
  foldM
    (\arena l ->
       setInv arena l <$> SMT.simplify conf (FOL.andf [inv arena l, FOL.neg (SymSt.get st l)]))
    arena
    (locations arena)

---------------------------------------------------------------------------------------------------
-- Loop- and Subarena
---------------------------------------------------------------------------------------------------
loopArena :: RPArena -> Loc -> (RPArena, Loc)
loopArena arena l =
  let (arena0, l') = addLocation arena $ locName arena l ++ "'"
      arena1 = setInv arena0 l' $ inv arena0 l
      (arena2, sink) = addSink arena1 "sink"
      arena3 = arena2 {transRel = Map.insert sink (selfLoop sink) (transRel arena2)}
      arena4 = foldl (moveTrans l l') arena3 $ preds arena l
   in (arena4, l')

moveTrans :: Loc -> Loc -> RPArena -> Loc -> RPArena
moveTrans old new arena l
  | inv arena old /= inv arena new = error "assert: moving transition only to same domain targets"
  | otherwise =
    arena
      { transRel = Map.adjust (replaceByE old new) l $ transRel arena
      , predecessors =
          Map.adjust (Set.delete l) old
            $ Map.insertWith Set.union new (Set.singleton l)
            $ predecessors arena
      }

replaceByE :: Loc -> Loc -> Transition -> Transition
replaceByE src trg = h
  where
    h =
      \case
        TIf p tt te -> TIf p (h tt) (h te)
        TSys choices ->
          TSys
            ((\(upd, l) ->
                if l == src
                  then (upd, trg)
                  else (upd, l))
               <$> choices)

inducedSubArena :: RPArena -> Set Loc -> (RPArena, (Loc -> Loc, Set Loc))
inducedSubArena arena locs
  | not (locs `Set.isSubsetOf` locations arena) =
    error "assert: can only induce subgame on subset of locations!"
  | otherwise =
    let locsC = Set.unions (Set.map (succs arena) locs) `Set.union` locs
        (arena0, oldToNew) =
          createLocsFor (empty (variables arena)) (locName arena) (inv arena) locsC
        -- Add transitions
        cleanTrans =
          \case
            TIf p tt tf -> TIf p (cleanTrans tt) (cleanTrans tf)
            TSys upds ->
              TSys
                $ map
                    (\(upd, l) ->
                       if l `notElem` locs
                         then (Map.empty, l)
                         else (upd, l))
                    upds
        repTrans =
          \case
            TIf p tt tf -> TIf p (repTrans tt) (repTrans tf)
            TSys upds -> TSys $ map (second oldToNew) upds
        arena1 =
          foldl
            (\ar old ->
               let new = oldToNew old
                in fromMaybe
                     (error "assert: transition exists")
                     (addTransition
                        ar
                        new
                        (if old `elem` locs
                           then repTrans (cleanTrans (trans arena old))
                           else selfLoop new)))
            arena0
            locsC
        mOldToNew l
          | l `elem` locsC = oldToNew l
          | otherwise = error "assert: cannot map location"
     in (arena1, (mOldToNew, locsC))

independentProgVars :: Config -> RPArena -> IO (Set Symbol)
independentProgVars _ arena = do
  pure
    $ Set.difference (Vars.stateVars (variables arena))
    $ Set.map fst
    $ Set.filter (not . isSelfUpdate)
    $ Set.unions
    $ Set.map (go . trans arena)
    $ locations arena
  where
    go =
      \case
        TIf _ tt tf -> go tt `Set.union` go tf
        TSys upds -> Set.fromList $ concatMap (Map.toList . fst) upds

---------------------------------------------------------------------------------------------------
-- Synthesis
---------------------------------------------------------------------------------------------------
syntCPre ::
     Config -> RPArena -> Symbol -> (Loc -> Term) -> Loc -> Term -> SymSt -> IO [(Symbol, Term)]
syntCPre conf arena locVar toLoc loc cond target = do
  preCond <- SMT.simplify conf $ FOL.andf [cond, inv arena loc, validInput arena loc]
  Map.toList <$> syntTrans preCond (trans arena loc)
  where
    syntTrans preCond =
      \case
        TIf cond tt tf -> do
          let recT = syntTrans (FOL.andf [preCond, cond]) tt
          let recF = syntTrans (FOL.andf [preCond, FOL.neg cond]) tf
          satT <- SMT.sat conf $ FOL.andf [preCond, cond]
          satF <- SMT.sat conf $ FOL.andf [preCond, FOL.neg cond]
          case (satT, satF) of
            (False, _) -> recF
            (_, False) -> recT
            _ -> do
              mt <- recT
              Map.unionWith (FOL.ite cond) mt <$> recF
        TSys upds -> do
          preCond <- SMT.simplify conf preCond
          selectUpds preCond upds
    --
    selectUpds preCond =
      \case
        [] -> error "assert: unreachable code - partiy game extraction made a mistake!"
        (upd, loc):ur -> do
          let uassign = updateAssign upd loc
          let preSt = FOL.mapTermM upd $ FOL.andf [target `SymSt.get` loc, inv arena loc]
          preSt <- SMT.simplify conf preSt
          satPre <- SMT.sat conf preSt
          preCond' <- SMT.simplify conf $ FOL.andf [preCond, FOL.neg preSt]
          satOther <- SMT.sat conf preCond'
          if satPre
            then if satOther
                   then Map.unionWith (FOL.ite preSt) uassign <$> selectUpds preCond' ur
                   else pure uassign
            else selectUpds preCond ur
    --
    updateAssign upd loc =
      Map.insert locVar (toLoc loc)
        $ Map.fromSet (\var -> Map.findWithDefault (Vars.mk (variables arena) var) var upd)
        $ Vars.stateVars (variables arena)
---------------------------------------------------------------------------------------------------
