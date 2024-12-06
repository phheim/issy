---------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-- TODO: Add sortOf, remove IO type, encapsulate more!!!
-- TODO: Make consitent with project wide connvetion: game structure -> g, ...
-- TODO: Encapsulate structure of Game completely!
-- TODO: Replace variables and Co.
-------------------------------------------------------------------------------
module Issy.RPG
  ( Loc
  , Game
  , inputs
  , outputs
  , locationSet
  , boundedCells
  , Transition(..)
  , -- Access
    locations
  , tran
  , inv
  , tryTrans
  , sortOf
  , trySortOf
  , preds
  , predSet
  , locName
  , -- Construction
    emptyGame
  , sameSymbolGame
  , addInput
  , addOutput
  , addLocation
  , addTransition
  , setInv
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
import Data.Map.Strict (Map, (!?), findWithDefault, insertWith, member, restrictKeys)
import qualified Data.Map.Strict as Map (elems, empty, filterWithKey, insert, map, toList)
import Data.Maybe (fromMaybe)
import Data.Set (Set, difference, empty, fromList, insert, intersection, singleton, union, unions)
import qualified Data.Set as Set (map)

import Issy.Base.Locations (Loc)
import qualified Issy.Base.Locations as Locs (Store, add, empty, name, toSet)
import Issy.Base.Objectives (Objective)
import Issy.Base.SymbolicState (SymSt)
import Issy.Base.SymbolicState as SymSt (get)

import Issy.Config (Config)
import Issy.Logic.FOL
  ( Sort
  , Symbol
  , Term(Var)
  , andf
  , exists
  , forAll
  , impl
  , ite
  , mapTermM
  , neg
  , orf
  , symbols
  , true
  )
import Issy.Logic.SMT (unsat)
import Issy.Utils.Extra (ifM, predecessorRelation)
import Issy.Utils.OpenList (pop, push, pushOne)
import qualified Issy.Utils.OpenList as OL (empty)

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
    TIf _ tt te -> succT tt `union` succT te
    TSys choices -> fromList (snd <$> choices)

mapTerms :: (Term -> Term) -> Transition -> Transition
mapTerms m =
  \case
    TIf p tt te -> TIf (m p) (mapTerms m tt) (mapTerms m te)
    TSys upds -> TSys $ map (first (fmap m)) upds

-- Loc go form 0 to cnt - 1
data Game = Game
  { locationSet :: Locs.Store
  , inputs :: [Symbol]
  , outputs :: [Symbol]
  , ioType :: Map Symbol Sort
  , trans :: Map Loc Transition
    -- ^ all locations should be mapped
  , predecessors :: Map Loc (Set Loc)
  , invariant :: Map Loc Term
    -- ^ all location should be mapped, default mapping to true
    -- Domain knowledge:
  , boundedCells :: [Symbol]
  } deriving (Show)

locName :: Game -> Loc -> String
locName = Locs.name . locationSet

trySortOf :: Game -> Symbol -> Maybe Sort
trySortOf g v = ioType g !? v

sortOf :: Game -> Symbol -> Sort
sortOf g v = fromMaybe (error ("assert: sort of " ++ v ++ " not found")) $ trySortOf g v

tryTrans :: Game -> Loc -> Maybe Transition
tryTrans g l = trans g !? l

tran :: Game -> Loc -> Transition
tran g l = fromMaybe (error "assert: transition expected") $ tryTrans g l

inv :: Game -> Loc -> Term
inv g l = fromMaybe (error "assert: all invariants should be mapped!") $ invariant g !? l

setInv :: Game -> Loc -> Term -> Game
setInv g l i = g {invariant = Map.insert l i (invariant g)}

emptyGame :: Game
emptyGame =
  Game
    { locationSet = Locs.empty
    , inputs = []
    , outputs = []
    , ioType = Map.empty
    , trans = Map.empty
    , predecessors = Map.empty
    , invariant = Map.empty
    , boundedCells = []
    }

sameSymbolGame :: Game -> Game
sameSymbolGame game =
  emptyGame
    { inputs = inputs game
    , outputs = outputs game
    , ioType = ioType game
    , boundedCells = boundedCells game
    }

locations :: Game -> Set Loc
locations = Locs.toSet . locationSet

addLocation :: Game -> String -> (Game, Loc)
addLocation g name =
  let (newLoc, locSet) = Locs.add (locationSet g) name
   in (g {locationSet = locSet}, newLoc)

addInput :: Game -> Symbol -> Sort -> Maybe Game
addInput g input sort
  | input `elem` inputs g = Nothing
  | input `elem` outputs g = Nothing
  | otherwise = Just $ g {inputs = input : inputs g, ioType = Map.insert input sort (ioType g)}

addOutput :: Game -> Symbol -> Sort -> Bool -> Maybe Game
addOutput g output sort bound
  | output `elem` outputs g = Nothing
  | output `elem` inputs g = Nothing
  | otherwise =
    Just
      $ g
          { outputs = output : outputs g
          , ioType = Map.insert output sort (ioType g)
          , boundedCells = [output | bound] ++ boundedCells g
          }

addTransition :: Game -> Loc -> Transition -> Maybe Game
addTransition g l t
  | l `member` trans g = Nothing
  | otherwise = Just $ foldl (addPred l) (g {trans = Map.insert l t (trans g)}) (succT t)
  where
    addPred pre g suc = g {predecessors = insertWith union suc (singleton pre) (predecessors g)}

preds :: Game -> Loc -> Set Loc
preds g l = findWithDefault empty l (predecessors g)

predSet :: Game -> Set Loc -> Set Loc
predSet g ls = unions (Set.map (preds g) ls)

succs :: Game -> Loc -> Set Loc
succs g l = maybe empty succT (trans g !? l)

cyclicIn :: Game -> Loc -> Bool
cyclicIn g start = any (elem start . reachables g) (succs g start)

reachables :: Game -> Loc -> Set Loc
reachables g l = bfs empty (l `pushOne` OL.empty)
  where
    bfs seen ol =
      case pop ol of
        Nothing -> seen
        Just (o, ol')
          | o `elem` seen -> bfs seen ol'
          | otherwise ->
            let seen' = o `insert` seen
             in bfs seen' ((succs g o `difference` seen) `push` ol')

-- TODO: this breaks the invariants
pruneUnreachables :: Loc -> Game -> Game
pruneUnreachables init g =
  let reach = reachables g init
   in g
        { predecessors = intersection reach <$> restrictKeys (predecessors g) reach
        , trans = restrictKeys (trans g) reach
        }

usedSymbols :: Game -> Set Symbol
usedSymbols g =
  fromList (inputs g)
    `union` fromList (outputs g)
    `union` unions (Map.elems (symTrans <$> trans g))
    `union` unions (map (symbols . snd) (Map.toList (invariant g)))
  where
    symTrans =
      \case
        TIf p t1 t2 -> symbols p `union` symTrans t1 `union` symTrans t2
        TSys choices -> unions (concatMap (map (symbols . snd) . Map.toList . fst) choices)

-------------------------------------------------------------------------------
simplifyTransition :: Config -> Transition -> IO Transition
simplifyTransition cfg = go [true]
  where
    go cond =
      \case
        TSys upd -> return $ TSys $ nub $ map (first simplifyUpdates) upd
        TIf p tt tf ->
          let rectt = go (p : cond) tt
              rectf = go (neg p : cond) tf
           in ifM (unsat cfg (andf (p : cond))) rectf
                $ ifM (unsat cfg (andf (neg p : cond))) rectt
                $ liftM2 (TIf p) rectt rectf

simplifyUpdates :: Map Symbol Term -> Map Symbol Term
simplifyUpdates =
  Map.filterWithKey $ \var ->
    \case
      Var v _ -> v /= var
      _ -> True

--TODO: add pruning of locations. Warning this needs also to accounte possible winning conditions!
simplifyRPG :: Config -> (Game, Objective) -> IO (Game, Objective)
simplifyRPG cfg (game, wc) = do
  newTrans <- mapM (simplifyTransition cfg) (trans game)
  let next l = fromMaybe (error ("assert: location not mapped " ++ show l)) $ newTrans !? l
  return
    ( game {trans = newTrans, predecessors = predecessorRelation (succT . next) (locations game)}
    , wc)

cpreSys :: Game -> SymSt -> Loc -> Term
cpreSys g st l = andf [g `inv` l, forAll (inputs g) (validInput g l `impl` cpreST (tran g l))]
  where
    cpreST =
      \case
        TIf p tt te -> ite p (cpreST tt) (cpreST te)
        TSys upds -> orf [mapTermM u (andf [st `SymSt.get` l, g `inv` l]) | (u, l) <- upds]

cpreEnv :: Game -> SymSt -> Loc -> Term
cpreEnv g st l = andf [g `inv` l, exists (inputs g) (andf [validInput g l, cpreET (tran g l)])]
  where
    cpreET =
      \case
        TIf p tt te -> ite p (cpreET tt) (cpreET te)
        TSys upds -> andf [mapTermM u ((g `inv` l) `impl` (st `SymSt.get` l)) | (u, l) <- upds]

validInput :: Game -> Loc -> Term
validInput g l = go (tran g l)
  where
    go =
      \case
        TIf p tt te -> ite p (go tt) (go te)
        TSys upds -> orf [mapTermM u (g `inv` l) | (u, l) <- upds]

-------------------------------------------------------------------------------
-- Loop Game
-------------------------------------------------------------------------------
-- TODO: This is still a bit different from the formal definition as it
-- creates dead-ends. We take care that they are not queried but maybe
-- this should change
-- SHOULD only BE CALLED ON
loopGame :: Game -> Loc -> (Game, Loc)
loopGame g l =
  let (g', shadow) = addLocation g (locName g l ++ "'")
      oldPreds = preds g l
      g'' =
        g'
          { trans = Map.map (replaceByE l shadow) (trans g')
          , predecessors = (Map.insert l empty . Map.insert shadow oldPreds) (predecessors g')
          , invariant = Map.insert shadow (g' `inv` l) (invariant g')
          }
    -- TODO WARNING: This might destroy stuff if game not cyclic? Probably not though
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
