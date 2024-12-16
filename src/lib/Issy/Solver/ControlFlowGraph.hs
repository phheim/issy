{-# LANGUAGE LambdaCase, RecordWildCards #-}

module Issy.Solver.ControlFlowGraph
  ( ProgTrans
  , CFG
  , -- Creation
    empty
  , goalCFG
  , loopCFG
  , mkCFG
  , -- Transition Modification
    setLemmas
  , mapCFG
  , addUpd
  , redirectGoal
  , -- Strucutual Changes 
    integrate
  , setInitialCFG
  , -- Processing
    simplify
  , -- Printing
    printCFG
  ) where

import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map

import Issy.Base.SymbolicState (SymSt, get)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.GameInterface
import Issy.Solver.LemmaFinding (LemSyms(..), Lemma, prime)

newtype CFGLoc =
  CFGLoc Int
  deriving (Eq, Ord, Show)

--Invariant: all in locMap have to mapped in cfgTrans!
data CFG = CFG
  { cfgTrans :: Map CFGLoc ProgTrans
  , cfgLocCnt :: Int
  , cfgLocInit :: CFGLoc
  , locMap :: Map Loc CFGLoc
  }

setInitialCFG :: CFG -> Loc -> CFG
setInitialCFG cfg l = cfg {cfgLocInit = mapLoc cfg l}

mapLoc :: CFG -> Loc -> CFGLoc
mapLoc cfg l =
  case locMap cfg !? l of
    Just cl -> cl
    Nothing -> error $ "assert: mapLoc expects everything to be mapped " ++ show l

addLoc :: CFG -> Loc -> CFG
addLoc cfg@CFG {..} l
  | l `Map.member` locMap = error "assert: cannot add exisiting locations"
  | otherwise =
    cfg
      { cfgTrans = Map.insert (CFGLoc cfgLocCnt) (PT []) cfgTrans
      , cfgLocCnt = cfgLocCnt + 1
      , locMap = Map.insert l (CFGLoc cfgLocCnt) locMap
      }

data Statement
  = CondJump Term CFGLoc
  -- ^ This jumps after reading in the successor location
  | CondAssign Term (Map Symbol Term) CFGLoc
  -- ^ This jumps before reading in the successor location
  | CondCopy Term [(Symbol, Symbol)]
  -- Dummies
  | DummyCopy Term LemSyms
  | DummyGoal Term
  deriving (Eq, Ord, Show)

newtype ProgTrans =
  PT [Statement]
  deriving (Eq, Ord, Show)

mapTrans :: (CFGLoc -> [Statement] -> [Statement]) -> CFG -> CFG
mapTrans f cfg = cfg {cfgTrans = Map.mapWithKey (\l (PT st) -> PT (f l st)) (cfgTrans cfg)}

empty :: CFG
empty = CFG {cfgTrans = Map.empty, cfgLocCnt = 0, cfgLocInit = CFGLoc 0, locMap = Map.empty}

append :: Loc -> [Statement] -> CFG -> CFG
append l stmts cfg =
  cfg {cfgTrans = Map.adjust (\(PT pt) -> PT (pt ++ stmts)) (mapLoc cfg l) (cfgTrans cfg)}

mapCFG :: (Term -> Term) -> CFG -> CFG
mapCFG m = mapTrans (const (map go))
  where
    go =
      \case
        CondJump cond l -> CondJump (m cond) l
        CondAssign cond asgn l -> CondAssign (m cond) (fmap m asgn) l
        DummyGoal cond -> DummyGoal (m cond)
        st -> st

setLemmas :: [Symbol] -> [(LemSyms, Lemma)] -> CFG -> CFG
setLemmas states col = mapTrans (const (map go))
  where
    mapping = Map.fromList col
    go =
      \case
        DummyCopy cond lems ->
          case mapping !? lems of
            Nothing -> error $ "assert: " ++ show lems ++ " not mapped"
            Just lemma -> CondCopy cond $ map (\v -> (prime lemma ++ v, v)) states
        st -> st

-- OLD:
-- go [] (tran g l)
-- Invariant should be covered by attractor!
-- go cs = 
-- \case
--  TIf p tt tf -> go (p : cs) tt ++ go (neg p : cs) tf
--  TSys upds -> map (redUpds cs) upds
-- redUpds cs (u, l) =
-- (andf (reverse (mapTermM u (oldAttr `get` l) : cs)), u, mapLoc cfg l)
makeTrans :: CFG -> Game -> SymSt -> CFGLoc -> [(Term, Map Symbol Term, CFGLoc)]
makeTrans _ _ _ _ = error "TODO IMPLEMENT"

addUpd :: SymSt -> Game -> Loc -> CFG -> CFG
addUpd st g l cfg =
  append
    l
    (map (\(cond, asg, l') -> CondAssign cond asg l') (makeTrans cfg g st (mapLoc cfg l)))
    cfg

mkCFG :: [Loc] -> CFG
mkCFG = foldl addLoc empty

goalCFG :: SymSt -> CFG
goalCFG st =
  foldl
    (\cfg (l, cond) -> append l [DummyGoal cond] cfg)
    (mkCFG (SymSt.locations st))
    (SymSt.toList st)

loopCFG :: (Loc, Loc) -> SymSt -> LemSyms -> Term -> CFG
loopCFG (l, l') st lSyms stepTerm =
  let cfg = addLoc (goalCFG st) l'
   in append l' [CondJump (FOL.orf [st `get` l, stepTerm]) (mapLoc cfg l)]
        $ append l [DummyCopy FOL.true lSyms] cfg

redirectGoal :: Game -> SymSt -> CFG -> CFG
redirectGoal g symSt cfg = mapTrans (concatMap . go) cfg
  where
    go l =
      \case
        DummyGoal cond ->
          map (\(c, asg, l') -> CondAssign (FOL.andf [cond, c]) asg l') $ makeTrans cfg g symSt l
        st -> [st]

goalToJump :: (CFGLoc -> Maybe CFGLoc) -> CFG -> CFG
goalToJump mp = mapTrans (map . go)
  where
    go l =
      \case
        DummyGoal cond ->
          case mp l of
            Nothing -> DummyGoal cond
            Just l' -> CondJump cond l'
        st -> st

-- TODO: this need for sure something that maps some parts of the main stuff to the sub initial location!!!
integrate :: CFG -> CFG -> CFG
integrate sub main =
  let merged =
        CFG
          { cfgTrans =
              Map.union (cfgTrans main)
                $ Map.mapKeys (\(CFGLoc l) -> CFGLoc (l + offset))
                $ Map.map (\(PT stmts) -> PT (map go stmts))
                $ cfgTrans sub
          , cfgLocCnt = offset + cfgLocCnt sub
          , cfgLocInit = cfgLocInit main
          , locMap = locMap main
          }
   in goalToJump
        (\(CFGLoc l) ->
           if l >= offset
             then Just (CFGLoc (l + offset))
             else Nothing)
        merged
  where
    offset = cfgLocCnt main
    go =
      \case
        CondJump c (CFGLoc l) -> CondJump c (CFGLoc (l + offset))
        CondAssign c u (CFGLoc l) -> CondAssign c u (CFGLoc (l + offset))
        st -> st

--
-- Simplification
--
totalize :: [Statement] -> [Statement]
totalize = go []
  where
    go cond =
      \case
        CondJump c l:sr -> CondJump (FOL.andf (c : cond)) l : go (FOL.neg c : cond) sr
        CondAssign c a l:sr -> CondAssign (FOL.andf (c : cond)) a l : go (FOL.neg c : cond) sr
        CondCopy c a:sr -> CondCopy (FOL.andf (c : cond)) a : go cond sr
        _ -> error "assert: dummies should not appear here anymore"

mergeTotalUp :: [Statement] -> [Statement]
mergeTotalUp = id -- TODO IMPLEMENT: merge subsequent updates, if no copy is there

simplifySt :: Config -> Statement -> IO Statement
simplifySt ctx =
  \case
    CondJump c l -> do
      c <- SMT.simplify ctx c
      pure $ CondJump c l
    CondAssign c a l -> do
      c <- SMT.simplify ctx c
      a <- mapM (SMT.simplify ctx) a
      pure $ CondAssign c a l
    CondCopy c a -> do
      c <- SMT.simplify ctx c
      pure $ CondCopy c a
    _ -> error "assert: dummies should not appear here anymore"

emptyCond :: Statement -> Bool
emptyCond =
  \case
    CondJump c _ -> c == FOL.false
    CondAssign c _ _ -> c == FOL.false
    CondCopy c _ -> c == FOL.false
    _ -> error "assert: dummies should not appear here anymore"

simplifyTr :: Config -> ProgTrans -> IO ProgTrans
simplifyTr ctx (PT stmts) = do
  stmts <- pure $ totalize stmts
  stmts <- mapM (simplifySt ctx) stmts
  stmts <- pure $ filter (not . emptyCond) stmts
  stmts <- pure $ mergeTotalUp stmts
  PT <$> mapM (simplifySt ctx) stmts

simplify :: Config -> CFG -> IO CFG
simplify ctx cfg = do
  newTrans <- mapM (simplifyTr ctx) (cfgTrans cfg)
  pure $ cfg {cfgTrans = newTrans}

--
-- Printing
--
-- TODO: add variable declarations!
--
printCFG :: Variables -> CFG -> String
printCFG _ cfg =
  unlines
    $ ["int main() {", "goto " ++ preRead (cfgLocInit cfg) ++ ";"]
        ++ map (\(l, PT st) -> printLoc l st) (Map.toList (cfgTrans cfg))
        ++ ["}"]

printLoc :: CFGLoc -> [Statement] -> String
printLoc l stmts =
  unlines $ [preRead l ++ ":", "  read();", postRead l ++ ":"] ++ map printST stmts ++ ["abort();"]

preRead :: CFGLoc -> String
preRead (CFGLoc i) = "loc" ++ show i ++ "_pre"

postRead :: CFGLoc -> String
postRead (CFGLoc i) = "loc" ++ show i ++ "_post"

printST :: Statement -> String
printST =
  \case
    CondJump cond loc -> " if (" ++ printTerm cond ++ ") goto " ++ postRead loc ++ ";"
    CondAssign cond asgn loc ->
      unlines
        $ [" if (" ++ printTerm cond ++ ") {"]
            ++ map (\(v, t) -> "    " ++ v ++ " = " ++ printTerm t ++ ";") (Map.toList asgn)
            ++ ["    goto " ++ preRead loc ++ ";", "}"]
    CondCopy cond asgn ->
      unlines
        $ [" if (" ++ printTerm cond ++ ") {"]
            ++ map (\(v, v') -> "    " ++ v ++ " = " ++ v' ++ ";") asgn
            ++ ["}"]
    _ -> error "assert: dummies should not appear here anymore"

printTerm :: Term -> String
printTerm = smtLib2
