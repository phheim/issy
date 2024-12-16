{-# LANGUAGE LambdaCase, RecordWildCards #-}

module Issy.Solver.ControlFlowGraph
  ( ProgTrans(PTCopyDummy, PTUnmapped)
  , CFG
  , CFGLoc
  , empty
  , addLoc
  , goalCFG
  , jump
  , ite
  , mapUnmapped
  , removePTDummy
  , mapCFG
  , addUpd
  , integrate
  , process
  , mapLoc
  , setInitialCFG
  , redirectGoal
  , mkCFG
  , printCFG
  ) where

import Control.Monad (foldM)
import Data.Map.Strict (Map, (!), (!?))
import qualified Data.Map.Strict as Map

import Issy.Base.SymbolicState hiding (map)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config)
import Issy.Logic.FOL hiding (ite)
import qualified Issy.Logic.SMT as SMT (simplify)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.GameInterface
import Issy.Solver.LemmaFinding

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

empty :: CFG
empty = CFG {cfgTrans = Map.empty, cfgLocCnt = 0, cfgLocInit = CFGLoc 0, locMap = Map.empty}

addLoc :: CFG -> Loc -> CFG
addLoc cfg@CFG {..} l =
  case locMap !? l of
    Just _ -> error "Assertion: Cannot add exisiting locations"
    Nothing ->
      cfg
        { cfgTrans = Map.insert (CFGLoc cfgLocCnt) PTUnmapped cfgTrans
        , cfgLocCnt = cfgLocCnt + 1
        , locMap = Map.insert l (CFGLoc cfgLocCnt) locMap
        }

data ProgTrans
  = PTIf Term ProgTrans ProgTrans
  | PTJump CFGLoc
  | PTUnmapped
  | PTGoal
  | PTUpdates [(Term, Map Symbol Term, CFGLoc)]
  -- PTUpdates includes READS!!!!
  -- Acceleration related stuff
  | PTCopyDummy LemSyms ProgTrans
  | PTCopy [(Symbol, Symbol)] ProgTrans

jump :: CFGLoc -> ProgTrans
jump = PTJump

ite :: Term -> ProgTrans -> ProgTrans -> ProgTrans
ite = PTIf

mapCFG :: (Term -> Term) -> CFG -> CFG
mapCFG m cfg = cfg {cfgTrans = fmap go (cfgTrans cfg)}
  where
    go =
      \case
        PTIf p tt tf -> PTIf (m p) (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUnmapped
        PTGoal -> PTGoal
        PTUpdates upds -> PTUpdates $ map (\(g, u, l) -> (m g, m <$> u, l)) upds
        PTCopy assgn t -> PTCopy assgn (go t)
        PTCopyDummy l t -> PTCopyDummy l (go t)

mapUnmapped :: Loc -> ProgTrans -> CFG -> CFG
mapUnmapped l pt cfg = cfg {cfgTrans = Map.adjust go (mapLoc cfg l) (cfgTrans cfg)}
  where
    go =
      \case
        PTUpdates upds -> PTUpdates upds
        PTIf p tt tf -> PTIf p (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> pt
        PTGoal -> PTGoal
        PTCopyDummy l t -> PTCopyDummy l (go t)
        PTCopy asgn t -> PTCopy asgn (go t)

removePTDummy :: [Symbol] -> [(LemSyms, Lemma)] -> CFG -> CFG
removePTDummy cells col cfg = cfg {cfgTrans = fmap go (cfgTrans cfg)}
  where
    mapping = Map.fromList col
    go =
      \case
        PTIf p tt tf -> PTIf p (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUnmapped
        PTGoal -> PTGoal
        PTUpdates upds -> PTUpdates upds
        PTCopy assgn t -> PTCopy assgn (go t)
        PTCopyDummy l t ->
          case mapping !? l of
            Nothing -> error ("Assertion: " ++ show l ++ " not mapped")
            Just lemma -> PTCopy (map (\v -> (prime lemma ++ v, v)) cells) (go t)

mapLoc :: CFG -> Loc -> CFGLoc
mapLoc cfg l =
  case locMap cfg !? l of
    Just cl -> cl
    Nothing -> error ("Assertion: mapLoc expects everything to be mapped " ++ show l)

setInitialCFG :: CFG -> Loc -> CFG
setInitialCFG cfg l = cfg {cfgLocInit = mapLoc cfg l}

mapGoal :: (Loc -> ProgTrans) -> CFG -> CFG
mapGoal m cfg =
  Map.foldlWithKey
    (\cfg l cl -> cfg {cfgTrans = Map.adjust (go l) cl (cfgTrans cfg)})
    cfg
    (locMap cfg)
  where
    go l =
      \case
        PTUpdates upds -> PTUpdates upds
        PTCopy asgn t -> PTCopy asgn (go l t)
        PTIf p tt tf -> PTIf p (go l tt) (go l tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUnmapped
        PTGoal -> m l
        PTCopyDummy ls t -> PTCopyDummy ls (go l t)

-- Invariant should be covered by attractor!
makeTrans :: CFG -> Game -> SymSt -> Loc -> ProgTrans
makeTrans cfg g oldAttr l = PTUpdates $ go [] (error "TODO: FIXME") --(tran g l)
  where
    go cs = error "TODO: FIXME"
      -- \case
      --  TIf p tt tf -> go (p : cs) tt ++ go (neg p : cs) tf
      --  TSys upds -> map (redUpds cs) upds
    redUpds cs (u, l) = (andf (reverse (mapTermM u (oldAttr `get` l) : cs)), u, mapLoc cfg l)

addUpd :: SymSt -> Game -> Loc -> CFG -> CFG
addUpd symSt g l cfg = cfg {cfgTrans = Map.adjust go (mapLoc cfg l) (cfgTrans cfg)}
  where
    PTUpdates updsN = makeTrans cfg g symSt l
    go =
      \case
        PTIf p tt tf -> PTIf p (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUpdates updsN
        PTGoal -> PTGoal
        PTCopyDummy l t -> PTCopyDummy l (go t)
        PTCopy a t -> PTCopy a (go t)
        PTUpdates upds ->
          let cond = orf $ map (\(c, _, _) -> neg c) upds
           in PTUpdates $ foldl (addUpd cond) upds updsN
    addUpd c us (g, u, l) =
      case us of
        [] -> [(g, u, l)]
        (g', u', l'):ur
          | u == u' && l == l' -> (orf [g', andf [c, g]], u, l) : ur
          | otherwise -> (g', u', l') : addUpd c ur (g, u, l)

-- DO NOT READ BEFORE GOAL
goalCFG :: SymSt -> CFG
goalCFG st =
  foldl
    (\cfg (l, t) -> mapUnmapped l (PTIf t PTGoal PTUnmapped) cfg)
    (mkCFG (SymSt.locations st))
    (SymSt.toList st)

redirectGoal :: Game -> SymSt -> CFG -> CFG
redirectGoal g symSt cfg = mapGoal (makeTrans cfg g symSt) cfg

integrate :: CFG -> CFG -> CFG
integrate sub main =
  let sub0 = mapGoal (PTJump . mapLoc main) sub
      iSub = cfgLocCnt sub0
      iMain = cfgLocCnt main
   in CFG
        { cfgTrans =
            cfgTrans main
              `Map.union` Map.fromList
                            ((\(CFGLoc i, t) -> (CFGLoc (i + iMain), go iMain t))
                               <$> Map.toList (cfgTrans sub0))
        , cfgLocCnt = iSub + iMain
        , cfgLocInit = cfgLocInit main
        , locMap = locMap main
        }
  where
    go add =
      \case
        PTIf p tt tf -> PTIf p (go add tt) (go add tf)
        PTJump (CFGLoc cl) -> PTJump (CFGLoc (cl + add))
        PTUnmapped -> PTUnmapped
        PTGoal -> PTGoal
        PTCopyDummy ls t -> PTCopyDummy ls (go add t)
        PTCopy asgn t -> PTCopy asgn (go add t)
        PTUpdates upds -> PTUpdates $ map (\(g, u, CFGLoc cl) -> (g, u, CFGLoc (cl + add))) upds

process :: Config -> CFG -> IO CFG
process ctx cfg =
  foldM
    (\cfg cl -> do
       pt <- go (cfgTrans cfg ! cl)
       return cfg {cfgTrans = Map.insert cl pt (cfgTrans cfg)})
    cfg
    (Map.keys $ cfgTrans cfg)
  where
    go =
      \case
        PTIf p tt tf -> do
          p <- SMT.simplify ctx p
          if p == true
            then go tt
            else if p == false
                   then go tf
                   else do
                     tt <- go tt
                     tf <- go tf
                     return $ PTIf p tt tf
        PTJump cl -> return $ PTJump cl
        PTUnmapped -> return PTUnmapped
        PTGoal -> return PTGoal
        PTCopyDummy ls t -> do
          t <- go t
          return $ PTCopyDummy ls t
        PTCopy asgn t -> do
          t <- go t
          return $ PTCopy asgn t
        PTUpdates upds -> do
          upds <-
            mapM
              (\(g, u, l) -> do
                 g <- SMT.simplify ctx g
                 return (g, u, l))
              upds
          return $ PTUpdates $ filter (\(g, _, _) -> g /= false) upds

mkCFG :: [Loc] -> CFG
mkCFG = foldl addLoc empty

printCFG :: Game -> CFG -> String
printCFG g cfg =
  unlines
    $ ("read" ++ concatMap (" " ++) (inputL g) ++ ";")
        : ("goto " ++ wCFGL (cfgLocInit cfg) ++ ";")
        : map (\(cl, t) -> wCFGL cl ++ ": " ++ go t) (Map.toList (cfgTrans cfg))
  where
    wCFGL (CFGLoc i) = show i
    go =
      \case
        PTIf p tt tf -> "if " ++ smtLib2 p ++ " {" ++ go tt ++ "} else {" ++ go tf ++ "}"
        PTCopy assgn t ->
          "[" ++ concatMap (\(v, t) -> " " ++ v ++ ":=" ++ t) assgn ++ " ]; " ++ go t
        PTJump cl -> "goto " ++ wCFGL cl ++ ";"
        PTUnmapped -> "abort();"
        PTGoal -> error "Assertion: Found PTGoal"
        PTCopyDummy _ _ -> error "Assertion: Found PTCopyDummy"
        PTUpdates upds ->
          "read "
            ++ concatMap (" " ++) (inputL g)
            ++ "; "
            ++ "case {"
            ++ concatMap
                 (\(g, u, l) ->
                    "if "
                      ++ smtLib2 g
                      ++ " ["
                      ++ concatMap (\(v, t) -> " " ++ v ++ " := " ++ smtLib2 t) (Map.toList u)
                      ++ "] goto "
                      ++ wCFGL l
                      ++ ";")
                 upds
            ++ "otherwise abort() };"
