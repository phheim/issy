{-# LANGUAGE LambdaCase #-}

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
  ) where

import Data.Bifunctor (second)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Locations (Loc)
import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective(..))
import qualified Issy.Base.Objectives as Obj
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Utils.OpenList as OL

data Arena = Arena
  { variables :: Variables
  , locations :: Locs.Store
  , aDomain :: Map Loc Term
  , transRel :: Map Loc (Map Loc Term)
  , predRel :: Map Loc (Set Loc)
  } deriving (Eq, Ord, Show)

empty :: Variables -> Arena
empty vars =
  Arena
    { variables = vars
    , locations = Locs.empty
    , aDomain = Map.empty
    , transRel = Map.empty
    , predRel = Map.empty
    }

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

usedSymbols :: Arena -> Set Symbol
usedSymbols arena =
  Vars.allSymbols (variables arena)
    `Set.union` Set.unions (map FOL.symbols (concatMap Map.elems (Map.elems (transRel arena))))

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

redirectTransTo :: Arena -> Loc -> Loc -> Arena
redirectTransTo arena src trg =
  arena
    { transRel = Map.insert src (Map.singleton trg FOL.true) $ transRel arena
    , predRel =
        Map.insertWith Set.union trg (Set.singleton src) $ Set.filter (/= src) <$> predRel arena
    }

addSink :: Arena -> (Arena, Loc)
addSink arena =
  let sinkName = FOL.uniqueName "sink" $ Set.map (locName arena) $ locSet arena
      (arena0, sink) = addLoc arena sinkName
      arena1 = setDomain arena0 sink FOL.true
   in (setTrans arena1 sink sink FOL.true, sink)

createLocsFor ::
     (Foldable t, Ord a) => Arena -> (a -> String) -> (a -> Term) -> t a -> (Arena, a -> Loc)
createLocsFor arena name dom =
  second (!)
    . foldl
        (\(a, mp) e ->
           let (a', l) = addLoc a (name e)
            in (setDomain a' l (dom e), Map.insert e l mp))
        (arena, Map.empty)

--
-- Solving
--
validInput :: Arena -> Loc -> Term
validInput a l =
  let v = variables a
   in Vars.existsX' v
        $ FOL.orfL (succL a l)
        $ \l' -> FOL.andf [trans a l l', Vars.primeT v (domain a l')]

cpreEnv :: Arena -> SymSt -> Loc -> Term
cpreEnv a d l =
  let v = variables a
   in Vars.existsI v
        $ FOL.impl (validInput a l)
        $ Vars.forallX' v
        $ FOL.andfL (succL a l)
        $ \l' ->
            FOL.andf [trans a l l', Vars.primeT v (domain a l')]
              `FOL.impl` Vars.primeT v (SymSt.get d l')

cpreSys :: Arena -> SymSt -> Loc -> Term
cpreSys a d l =
  let v = variables a
   in Vars.forallI v
        $ FOL.impl (validInput a l)
        $ Vars.existsX' v
        $ FOL.orfL (succL a l)
        $ \l' ->
            FOL.andf [trans a l l', Vars.primeT v (domain a l'), Vars.primeT v (SymSt.get d l')]

loopArena :: Arena -> Loc -> (Arena, Loc)
loopArena arena l =
  let (arena0, l') = addLoc arena (Locs.name (locations arena) l ++ "'")
      arena1 = setDomain arena0 l' $ domain arena0 l
      (arena2, sink) = addSink arena1
      arena' = setTrans arena2 l' sink FOL.true
   in ( arena'
          { transRel =
              Map.mapKeys
                (\loc ->
                   if loc == l
                     then l'
                     else loc)
                <$> transRel arena'
          , predRel = Map.insert l Set.empty . Map.insert l' (preds arena l) $ predRel arena'
          }
      , l')

--
-- Sanitize
--
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

--
-- Simplification
--
simplifyArena :: Config -> Arena -> IO Arena
simplifyArena cfg arena = do
  let filt mp = Map.filter (/= FOL.false) <$> mapM (SMT.simplify cfg) mp
  newDom <- filt (aDomain arena)
  newTransRel <- mapM filt $ transRel arena
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
