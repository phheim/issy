---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Games.SymbolicArena
-- Description : Data structure for symbolic arenas
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the data structure for symbolic arenas of symbolic games.
-- This includes more complex modification and operations used in the game solving.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Games.SymbolicArena
  ( Arena
  , -- Access
    variables
  , locations
  , locSet
  , locName
  , domain
  , trans
  , transList
  , succs
  , preds
  , predSet
  , usedSymbols
  , -- Construction
    empty
  , addLoc
  , createLocsFor
  , setDomain
  , setTrans
  , -- Analysis
    check
  , cyclicIn
  , -- Modifications
    addConstants
  , addSink
  , redirectTransTo
  , removeAttrEnv
  , removeAttrSys
  , simplifySG
  , -- Predecessors
    pre
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
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.Locations as Locs
import Issy.Games.Objectives (Objective(..))
import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Reasoning as FOLR
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- Arena
---------------------------------------------------------------------------------------------------
-- | Opaque representation of a symbolic arena.
data Arena = Arena
  { variables :: Variables
    -- ^ The variable context of an arena.
  , locations :: Locs.Store
    -- ^ The location context of an arena.
  , aDomain :: Map Loc Term
  , transRel :: Map Loc (Map Loc Term)
  , predRel :: Map Loc (Set Loc)
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- Access
---------------------------------------------------------------------------------------------------
-- | The locations of an arena.
locSet :: Arena -> Set Loc
locSet = Locs.toSet . locations

-- | The name of a location.
locName :: Arena -> Loc -> String
locName = Locs.name . locations

-- | The domain of a location. The domain restricts (symbolically) what state variable
-- values are allowed in a location.
domain :: Arena -> Loc -> Term
domain arena l = Map.findWithDefault FOL.false l (aDomain arena)

-- | The transition relation from one to another location in an arena.
trans :: Arena -> Loc -> Loc -> Term
trans arena src trg =
  Map.findWithDefault FOL.false trg $ Map.findWithDefault Map.empty src $ transRel arena

-- | all (no-false) transitions in an arena.
transList :: Arena -> [(Loc, Loc, Term)]
transList =
  concatMap (\(src, sucs) -> map (\(trg, term) -> (src, trg, term)) (Map.toList sucs))
    . Map.toList
    . transRel

-- | Compute all the successors of a location.
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

-- | Compute all the predecessors of a location.
preds :: Arena -> Loc -> Set Loc
preds arena l = Map.findWithDefault Set.empty l (predRel arena)

-- | Compute all the predecessors of a set of locations.
predSet :: Arena -> Set Loc -> Set Loc
predSet arena ls = Set.unions $ map (preds arena) $ Set.toList ls

-- | All symbols, including variables, function names, and location names, that are used
-- in the arena. This can be used to generate fresh symbols, e.g. for auxiliary variables,
-- such that they are really fresh.
usedSymbols :: Arena -> Set Symbol
usedSymbols arena =
  Vars.allSymbols (variables arena)
    `Set.union` Set.unions (map FOL.symbols (concatMap Map.elems (Map.elems (transRel arena))))

---------------------------------------------------------------------------------------------------
-- Construction
---------------------------------------------------------------------------------------------------
-- | The arena without any location with a given variable context.
empty :: Variables -> Arena
empty vars =
  Arena
    { variables = vars
    , locations = Locs.empty
    , aDomain = Map.empty
    , transRel = Map.empty
    , predRel = Map.empty
    }

-- | Add a location with a given name to the arena.
addLoc :: Arena -> String -> (Arena, Loc)
addLoc arena name =
  let (newLoc, newStore) = Locs.add (locations arena) name
   in (arena {locations = newStore}, newLoc)

-- | Add locations for a some collection abstract elements to an arena. This
-- method can be used e.g. to compute some kind of products.
createLocsFor ::
     (Foldable t, Ord a) => Arena -> (a -> String) -> (a -> Term) -> t a -> (Arena, a -> Loc)
createLocsFor arena name dom =
  second (flip (Map.findWithDefault (error "assert: lookup non-mapped element")))
    . foldl
        (\(a, mp) e ->
           let (a', l) = addLoc a (name e)
            in (setDomain a' l (dom e), Map.insert e l mp))
        (arena, Map.empty)

-- | Set the domain of a given location. Undefined if the location does not exists.
setDomain :: Arena -> Loc -> Term -> Arena
setDomain arena l dom
  | l `elem` Locs.toSet (locations arena) = arena {aDomain = Map.insert l dom (aDomain arena)}
  | otherwise = error "assert: try to set domain of undefined location!"

-- | Set the transition from one to another location. Undefined if the locations or
-- the free variables in the terms do not exists. Does not check if the arena
-- is non-blocking, this has to be done with 'check'.
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

---------------------------------------------------------------------------------------------------
-- Analysis
---------------------------------------------------------------------------------------------------
-- | Check if the arena is non-blocking and conforms to the definition.
check :: Config -> Arena -> IO (Maybe String)
check cfg a = go $ Set.toList $ locSet a
  where
    v = variables a
    go =
      \case
        [] -> pure Nothing
        l:lr -> do
                -- Check non-blocking condition from original symbolic game
                -- structure definition. The other one is unnecessary restrictive
                -- and now been remove.
          c <-
            SMT.valid cfg
              $ Vars.forallX v
              $ FOL.impl (domain a l)
              $ Vars.existsI v
              $ Vars.existsX' v
              $ FOL.orfL (Set.toList (locSet a)) $ \l' ->
              FOL.andf [Vars.primeT v (domain a l'), trans a l l']
          if c
            then go lr
            else pure $ Just $ locName a l ++ " might be blocking!"

-- | Check if the arena is cyclic in a location, i.e. the location might
-- be reachable from itself.
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
-- Modifications
---------------------------------------------------------------------------------------------------
-- | Add state variables that are guaranteed not to change
-- to the arena. This is undefined if a variable already exists.
addConstants :: [(Symbol, Sort)] -> Arena -> Arena
addConstants cvars arena =
  let newVars = foldl (uncurry . Vars.addStateVar) (variables arena) cvars
      eqCond = FOL.andfL cvars (\(v, s) -> FOL.var v s `FOL.equal` FOL.var (Vars.prime v) s)
   in arena
        {variables = newVars, transRel = Map.map (\t -> FOL.andf [t, eqCond]) <$> transRel arena}

-- | Add a sink location, i.e. a location that loops on itself with no other outgoing transition.
-- The self-loop will impose no restrictions on the variables.
addSink :: Arena -> (Arena, Loc)
addSink arena =
  let sinkName = FOL.uniquePrefix "sink" $ Set.map (locName arena) $ locSet arena
      (arena0, sink) = addLoc arena sinkName
      arena1 = setDomain arena0 sink FOL.true
   in (setTrans arena1 sink sink FOL.true, sink)

-- | Redirect all transition from one location into the target location.
redirectTransTo :: Arena -> Loc -> Loc -> Arena
redirectTransTo arena src trg =
  arena
    { transRel = Map.insert src (Map.singleton trg FOL.true) $ transRel arena
    , predRel =
        Map.insertWith Set.union trg (Set.singleton src) $ Set.filter (/= src) <$> predRel arena
    }

-- | Remove the result of an system attractor computation, i.e. the fixpoint
-- of applying the system enforceable predecessors, from states of the arena
-- by modifying the domain. This is usually used for parity game solving.
-- Note that this method might try to simplify the arena with an SMT-solver.
removeAttrEnv :: Config -> SymSt -> Arena -> IO Arena
removeAttrEnv conf st arena =
  simplifyArena conf
    $ foldl
        (\arena l -> setDomain arena l (FOL.andf [domain arena l, FOL.neg (SymSt.get st l)]))
        arena
        (locSet arena)

-- | As 'removeAttrSys' but for the system player.
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

-- | Apply simplifications to an symbolic game. Note that during this process the location
-- context might change, i.e. the old objective cannot be used anymore.
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

simplifyArena :: Config -> Arena -> IO Arena
simplifyArena cfg arena = do
  let filt mp = Map.filter (/= FOL.false) <$> mapM (SMT.simplify cfg) mp
  newDom <- filt (aDomain arena)
  let newTransRel = Map.map (Map.filter (/= FOL.false)) $ transRel arena
  arena <- pure $ arena {aDomain = newDom, transRel = newTransRel}
  let newPredRel =
        Map.mapWithKey (\l' -> Set.filter (\l -> trans arena l l' /= FOL.false)) (predRel arena)
  pure $ arena {predRel = newPredRel}

---------------------------------------------------------------------------------------------------
-- (Enforceable) Predecessors
---------------------------------------------------------------------------------------------------
-- | The possible predecessor of a symbolic state in a location.
pre :: Arena -> SymSt -> Loc -> Term
pre a d l =
  let v = variables a
      f = Vars.existsI v $ FOL.andf [validInput a l, sysPre a l (SymSt.get d)]
   in FOL.andf [f, domain a l]

-- | Compute the environment enforceable predecessors, i.e. the possible states in a
-- single location from which the environment player can always enforce to reach
-- the given symbolic state.
cpreEnv :: Arena -> SymSt -> Loc -> Term
cpreEnv a d l =
  let v = variables a
      f =
        Vars.existsI v
          $ FOL.andf
              [ validInput a l
              , Vars.forallX' v
                  $ FOL.andfL (succL a l) $ \l' ->
                  FOL.andf [trans a l l', Vars.primeT v (domain a l')]
                    `FOL.impl` Vars.primeT v (SymSt.get d l')
              ]
   in FOL.andf [f, domain a l]

-- | Like 'cpreEnv' but for the system player.
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
        $ FOL.orfL (succL a l) $ \l' ->
        FOL.andf [trans a l l', Vars.primeT v (domain a l'), Vars.primeT v (d l')]

---------------------------------------------------------------------------------------------------
-- Loop- and Subarena
---------------------------------------------------------------------------------------------------
-- | Compute the loop arena (see POPL'24 and TACAS'26 papers for more details) in
-- a given location. The returned location is the copy location of the aforementioned one.
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

-- | Compute the so induced sub-arena which results from restricting the arena to
-- a given set of location (without border locations).
-- Return a mapping from the original locations to the new ones, as well as
-- the set of old locations (!) with the border locations that the arena
-- has been restricted too.
inducedSubArena :: Arena -> Set Loc -> (Arena, (Loc -> Loc, Set Loc))
inducedSubArena arena locs
  | not (locs `Set.isSubsetOf` locSet arena) =
    error "assert: can only induced sub-arena on subset of locations!"
  | otherwise =
    let locsC = Set.unions (Set.map (succs arena) locs) `Set.union` locs
        (arena0, oldToNew) =
          createLocsFor (empty (variables arena)) (locName arena) (domain arena) locsC
        -- Equality constraint
        eqTrans =
          FOL.andfL (Vars.stateVarL (variables arena)) $ \v ->
            let s = Vars.sortOf (variables arena) v
             in FOL.var v s `FOL.equal` FOL.var (Vars.prime v) s
        -- Add transitions
        arena1 =
          foldl (\ar old -> setTrans ar (oldToNew old) (oldToNew old) eqTrans) arena0
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
        mOldToNew l
          | l `elem` locsC = oldToNew l
          | otherwise = error "assert: cannot map location"
     in (arena2, (mOldToNew, locsC))

-- | Compute the independent program variables, i.e. the program variables that
-- remain constant or do not matter otherwise.
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

---------------------------------------------------------------------------------------------------
-- Synthesis
---------------------------------------------------------------------------------------------------
-- | Synthesize assignments to the variables that mirror the step of an enforceable
-- predecessors. Since the locations are modeled as an integer program counter,
-- this method gets the name of the location variable as well as the constants for the
-- locations.
syntCPre ::
     Config -> Arena -> Symbol -> (Loc -> Integer) -> Loc -> Term -> SymSt -> IO [(Symbol, Term)]
syntCPre conf arena locVar toLoc loc cond targ = do
  lgd conf ["Synthesize in", locName arena loc, "on", SymSt.toString (locName arena) targ]
  let vs = variables arena
  let transTerms = map (trans arena loc) $ succL arena loc
  let eqHints =
        Map.fromSet
          (\v -> Set.toList (Set.unions (map (FOLR.equalitiesFor v) transTerms)))
          (Vars.stateVars' vs)
  let preCond = FOL.andf [validInput arena loc, cond, domain arena loc]
  let postCond =
        FOL.orfL (succL arena loc) $ \loc' ->
          FOL.andf
            [ FOL.equal (FOL.ivarT locVar) (FOL.intConst (toLoc loc'))
            , trans arena loc loc'
            , Vars.primeT vs (domain arena loc')
            , Vars.primeT vs (SymSt.get targ loc')
            ]
  let skolemVars = (locVar, FOL.SInt) : map (\v -> (v, Vars.sortOf vs v)) (Vars.stateVarL' vs)
  skolems <- FOLR.skolemize conf skolemVars eqHints preCond postCond
  when (any ((`Map.notMember` skolems) . fst) skolemVars)
    $ error "assert: found unmapped skolem variable"
  pure
    $ map
        (\(var, _) ->
           if var == locVar
             then (var, skolems ! var)
             else (Vars.unprime var, skolems ! var))
        skolemVars
---------------------------------------------------------------------------------------------------
