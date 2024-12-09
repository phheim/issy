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
  , boundedVar
  , loopArena
  , simplifySG
  , setTrans
  , redirectTransTo
  , createLocsFor
  , addLoc
  , addSink
  , empty
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
import Issy.Logic.FOL (Symbol, Term, andf, false, frees, impl, orf, symbols, true)
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
domain arena l = Map.findWithDefault false l (aDomain arena)

trans :: Arena -> Loc -> Loc -> Term
trans arena src trg =
  Map.findWithDefault false trg $ Map.findWithDefault Map.empty src $ transRel arena

transList :: Arena -> [(Loc, Loc, Term)]
transList =
  concatMap (\(src, sucs) -> map (\(trg, term) -> (src, trg, term)) (Map.toList sucs))
    . Map.toList
    . transRel

succs :: Arena -> Loc -> Set Loc
succs arena src =
  Set.fromList
    $ map fst
    $ filter ((/= false) . snd)
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
    `Set.union` Set.unions (map symbols (concatMap Map.elems (Map.elems (transRel arena))))

boundedVar :: Arena -> Symbol -> Bool
boundedVar _ _ = False --TODO: Implement: Maybe into variables!!!

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
  | trans == false = arena
  | not (frees trans `Set.isSubsetOf` Vars.allSymbols (variables arena)) =
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
  let (arena0, sink) = addLoc arena "sink" --TODO: maybe generate unique name?
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

transTerms :: Arena -> Loc -> (Loc -> Term) -> [Term]
transTerms arena src next =
  let vars = variables arena
   in [ andf [trans arena src trg, Vars.primeT vars (domain arena trg), Vars.primeT vars (next trg)]
      | trg <- succL arena src
      ]

validInput :: Arena -> Loc -> Term
validInput arena src = Vars.existsX' (variables arena) $ orf $ transTerms arena src (const true)

cpreEnv :: Arena -> SymSt -> Loc -> Term
cpreEnv arena st src =
  let vars = variables arena
   in Vars.existsI vars
        $ andf
            [validInput arena src, Vars.forallX' vars (andf (transTerms arena src (SymSt.get st)))]

cpreSys :: Arena -> SymSt -> Loc -> Term
cpreSys arena st src =
  let vars = variables arena
   in Vars.forallI vars
        $ validInput arena src `impl` Vars.existsX' vars (orf (transTerms arena src (SymSt.get st)))

loopArena :: Arena -> Loc -> (Arena, Loc)
loopArena arena l =
  let (arena', l') = addLoc arena (Locs.name (locations arena) l ++ "'")
   in ( arena'
          { aDomain = Map.insert l (domain arena' l) (aDomain arena')
          , transRel =
              Map.insert
                l'
                (Map.singleton l' true)
                (Map.mapKeys
                   (\loc ->
                      if loc == l
                        then l'
                        else l)
                   <$> transRel arena')
          , predRel = Map.insert l Set.empty . Map.insert l' (preds arena l) $ predRel arena'
          }
      , l')

simplifyArena :: Config -> Arena -> IO Arena
simplifyArena cfg arena = do
  let filt mp = Map.filter (/= FOL.false) <$> mapM (SMT.simplify cfg) mp
  newDom <- filt (aDomain arena)
  newTransRel <- mapM filt $ transRel arena
  arena <- pure $ arena {aDomain = newDom, transRel = newTransRel}
  let newPredRel =
        Map.mapWithKey (\l -> Set.filter ((/= FOL.false) . trans arena l)) (predRel arena)
  pure $ arena {predRel = newPredRel}

simplifySG :: Config -> (Arena, Objective) -> IO (Arena, Objective)
simplifySG cfg (arena, obj) = do
  arena <- simplifyArena cfg arena
  let notReachable = locSet arena `Set.difference` reachables arena (initialLoc obj)
    -- TODO: maybe properly remove the locations from the arena
  arena <- pure $ foldl (\a l -> setDomain a l FOL.false) arena notReachable
  let wc =
        Obj.mapWC
          (`Set.difference` notReachable)
          (\rank -> foldl (\r l -> Map.insert l 0 r) rank notReachable)
          (winningCond obj)
  pure (arena, obj {winningCond = wc})
