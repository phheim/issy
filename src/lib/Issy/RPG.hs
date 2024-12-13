---------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.RPG
  ( Loc
  , Game
  , variables
  , locationSet
  , Transition(..)
  , -- Access
    locations
  , trans
  , inv
  , preds
  , predSet
  , locName
  , -- Construction
    empty
  , addLocation
  , addTransition
  , setInv
  , selfLoop
  , -- Other
    succT
  , succs
  , mapTerms
  , cyclicIn
  , usedSymbols
  , --
    simplifyRPG
  , -- Solving
    cpreEnv
  , cpreSys
  , loopGame
  ) where

-------------------------------------------------------------------------------
import Control.Monad (liftM2)
import Data.Bifunctor (first)
import Data.List (nub)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Locations (Loc)
import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective)
import qualified Issy.Base.Objectives as Obj
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.SMT as SMT
import Issy.Utils.Extra (ifM, predecessorRelation)
import qualified Issy.Utils.OpenList as OL

-------------------------------------------------------------------------------
data Transition
  = TIf Term Transition Transition
  -- ^ guarded branch on some quanitifer-free formula
  | TSys [(Map Symbol Term, Loc)]
  -- ^ system selection with not-empty and unique mapping
  deriving (Eq, Ord, Show)

succT :: Transition -> Set Loc
succT =
  \case
    TIf _ tt te -> succT tt `Set.union` succT te
    TSys choices -> Set.fromList (snd <$> choices)

mapTerms :: (Term -> Term) -> Transition -> Transition
mapTerms m =
  \case
    TIf p tt te -> TIf (m p) (mapTerms m tt) (mapTerms m te)
    TSys upds -> TSys $ map (first (fmap m)) upds

selfLoop :: Loc -> Transition
selfLoop l = TSys [(Map.empty, l)]

data Game = Game
  { locationSet :: Locs.Store
  , variables :: Variables
  , transRel :: Map Loc Transition
  , predecessors :: Map Loc (Set Loc)
  , invariant :: Map Loc Term
  } deriving (Show)

locName :: Game -> Loc -> String
locName = Locs.name . locationSet

trans :: Game -> Loc -> Transition
trans g l = fromMaybe (selfLoop l) $ transRel g !? l

inv :: Game -> Loc -> Term
inv g l = fromMaybe FOL.true $ invariant g !? l

setInv :: Game -> Loc -> Term -> Game
setInv g l i = g {invariant = Map.insert l i (invariant g)}

empty :: Variables -> Game
empty vars =
  Game
    { locationSet = Locs.empty
    , variables = vars
    , transRel = Map.empty
    , predecessors = Map.empty
    , invariant = Map.empty
    }

locations :: Game -> Set Loc
locations = Locs.toSet . locationSet

addLocation :: Game -> String -> (Game, Loc)
addLocation g name =
  let (newLoc, locSet) = Locs.add (locationSet g) name
   in (g {locationSet = locSet}, newLoc)

addTransition :: Game -> Loc -> Transition -> Maybe Game
addTransition g l t
  | l `Map.member` transRel g = Nothing
  | otherwise = Just $ foldl (addPred l) (g {transRel = Map.insert l t (transRel g)}) (succT t)
  where
    addPred pre g suc =
      g {predecessors = Map.insertWith Set.union suc (Set.singleton pre) (predecessors g)}

preds :: Game -> Loc -> Set Loc
preds g l = Map.findWithDefault Set.empty l (predecessors g)

predSet :: Game -> Set Loc -> Set Loc
predSet g ls = Set.unions (Set.map (preds g) ls)

succs :: Game -> Loc -> Set Loc
succs g l = maybe Set.empty succT (transRel g !? l)

cyclicIn :: Game -> Loc -> Bool
cyclicIn g start = any (elem start . reachables g) (succs g start)

reachables :: Game -> Loc -> Set Loc
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

pruneUnreachables :: Loc -> Game -> Game
pruneUnreachables init g = foldl disableLoc g $ locations g `Set.difference` reachables g init
  where
    disableLoc :: Game -> Loc -> Game
    disableLoc g l =
      g
        { invariant = Map.insert l FOL.false (invariant g)
        , transRel = Map.insert l (selfLoop l) (transRel g)
        , predecessors = Map.insert l (Set.singleton l) $ (Set.filter (/= l)) <$> (predecessors g)
        }

usedSymbols :: Game -> Set Symbol
usedSymbols g =
  Set.union (Vars.allSymbols (variables g))
    $ Set.unions
    $ Map.elems (symTrans <$> transRel g) ++ map (FOL.symbols . snd) (Map.toList (invariant g))
  where
    symTrans =
      \case
        TIf p t1 t2 -> Set.unions [FOL.symbols p, symTrans t1, symTrans t2]
        TSys choices -> Set.unions (concatMap (map (FOL.symbols . snd) . Map.toList . fst) choices)

-------------------------------------------------------------------------------
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

simplifyRPG :: Config -> (Game, Objective) -> IO (Game, Objective)
simplifyRPG cfg (game, wc) = do
  newTrans <- mapM (simplifyTransition cfg) (transRel game)
  let next l = fromMaybe (error ("assert: location not mapped " ++ show l)) $ newTrans !? l
  game <-
    pure
      $ game
          {transRel = newTrans, predecessors = predecessorRelation (succT . next) (locations game)}
  pure (pruneUnreachables (Obj.initialLoc wc) game, wc)

cpreSys :: Game -> SymSt -> Loc -> Term
cpreSys g st l =
  FOL.andf [g `inv` l, Vars.forallI (variables g) (validInput g l `FOL.impl` cpreST (trans g l))]
  where
    cpreST =
      \case
        TIf p tt te -> FOL.ite p (cpreST tt) (cpreST te)
        TSys upds ->
          FOL.orf [FOL.mapTermM u (FOL.andf [st `SymSt.get` l, g `inv` l]) | (u, l) <- upds]

cpreEnv :: Game -> SymSt -> Loc -> Term
cpreEnv g st l =
  FOL.andf [g `inv` l, Vars.existsI (variables g) (FOL.andf [validInput g l, cpreET (trans g l)])]
  where
    cpreET =
      \case
        TIf p tt te -> FOL.ite p (cpreET tt) (cpreET te)
        TSys upds ->
          FOL.andf [FOL.mapTermM u ((g `inv` l) `FOL.impl` (st `SymSt.get` l)) | (u, l) <- upds]

validInput :: Game -> Loc -> Term
validInput g l = go (trans g l)
  where
    go =
      \case
        TIf p tt te -> FOL.ite p (go tt) (go te)
        TSys upds -> FOL.orf [FOL.mapTermM u (g `inv` l) | (u, l) <- upds]

-------------------------------------------------------------------------------
-- Loop Game
-------------------------------------------------------------------------------
loopGame :: Game -> Loc -> (Game, Loc)
loopGame g l =
  let (g', shadow) = addLocation g (locName g l ++ "'")
      shadowPreds = shadow `Set.insert` preds g l
      g'' =
        g'
          { transRel =
              Map.insert shadow (selfLoop shadow) $ Map.map (replaceByE l shadow) (transRel g')
          , predecessors = Map.insert l Set.empty . Map.insert shadow shadowPreds $ predecessors g'
          , invariant = Map.insert shadow (g' `inv` l) (invariant g')
          }
   in (pruneUnreachables l g'', shadow)

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
