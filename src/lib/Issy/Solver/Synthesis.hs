---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Synthesis
  ( SyBo
  , -- Book keeping
    empty
  , normSyBo
  , loopSyBo
  , returnOn
  , enforceTo
  , enforceFromTo
  , callOn
  , callOnSt
  , replaceUF
  , fromStayIn
  , -- Extraction
    extractProg
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad (unless)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Exit (die)

import qualified Issy.Base.Locations as Locs
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Solver.GameInterface

---------------------------------------------------------------------------------------------------
-- Bookkeeping
---------------------------------------------------------------------------------------------------
data SyBo
  = SyBoNone
  | SyBoNorm Arena [(Loc, Term, BookType)]
  | SyBoLoop Arena LoopSyBo

data LoopSyBo = LoopSyBo
  { loopLoc :: Loc
  , loopLoc' :: Loc
  , loopTrans :: [(Loc, Term, BookType)]
        -- ^ in loop game locations
  , loopToMain :: Map Loc Loc
        -- ^ maps loop locations EXCEPT loopLoc' to old locations
  , loopPrime :: Symbol
  }

data BookType
  = Enforce SymSt
  | Return
  | SubProg SyBo

normSyBo :: Config -> Arena -> SyBo
normSyBo conf arena
  | generateProgram conf = SyBoNorm arena []
  | otherwise = SyBoNone

loopSyBo :: Config -> Arena -> Loc -> Loc -> Symbol -> Map Loc Loc -> SyBo
loopSyBo conf arena loc loc' prime newToOld
  | generateProgram conf =
    SyBoLoop arena
      $ LoopSyBo
          {loopLoc = loc, loopLoc' = loc', loopTrans = [], loopPrime = prime, loopToMain = newToOld}
  | otherwise = SyBoNone

fromStayIn :: Config -> Arena -> SymSt -> SymSt -> SyBo
fromStayIn conf arena src trg = enforceFromTo src trg $ normSyBo conf arena

addTrans :: Loc -> Term -> BookType -> SyBo -> SyBo
addTrans loc cond tran =
  \case
    SyBoNone -> SyBoNone
    SyBoNorm arena trans -> SyBoNorm arena $ (loc, cond, tran) : trans
    SyBoLoop arena prog -> SyBoLoop arena $ prog {loopTrans = (loc, cond, tran) : loopTrans prog}

chainOn :: (Loc -> Term -> SyBo -> SyBo) -> SymSt -> SyBo -> SyBo
chainOn f st =
  \case
    SyBoNone -> SyBoNone
    init ->
      let retList = filter ((/= FOL.false) . snd) $ SymSt.toList st
       in foldl (\a (loc, cond) -> f loc cond a) init retList

returnOn :: SymSt -> SyBo -> SyBo
returnOn = chainOn (\loc cond -> addTrans loc cond Return)

enforceTo :: Loc -> Term -> SymSt -> SyBo -> SyBo
enforceTo loc cond = addTrans loc cond . Enforce

enforceFromTo :: SymSt -> SymSt -> SyBo -> SyBo
enforceFromTo src trg = chainOn (\loc cond -> enforceTo loc cond trg) src

callOn :: Loc -> Term -> SyBo -> SyBo -> SyBo
callOn loc cond = addTrans loc cond . SubProg

callOnSt :: SymSt -> SyBo -> SyBo -> SyBo
callOnSt src sub = chainOn (\loc cond -> callOn loc cond sub) src

replaceUF :: Symbol -> [Symbol] -> Term -> SyBo -> SyBo
replaceUF name argVars body = mapTerms $ FOL.replaceUF name argVars body

mapTerms :: (Term -> Term) -> SyBo -> SyBo
mapTerms f =
  \case
    SyBoNone -> SyBoNone
    SyBoNorm arena trans -> SyBoNorm arena $ map mapTrans trans
    SyBoLoop arena prog -> SyBoLoop arena $ prog {loopTrans = map mapTrans (loopTrans prog)}
  where
    mapTrans (loc, cond, pt) =
      case pt of
        Enforce st -> (loc, f cond, Enforce (SymSt.map f st))
        Return -> (loc, f cond, Return)
        SubProg sub -> (loc, f cond, SubProg (mapTerms f sub))

empty :: SyBo
empty = SyBoNone

symbols :: SyBo -> Set Symbol
symbols =
  \case
    SyBoNone -> Set.empty
    SyBoNorm arena trans ->
      Set.unions
        $ usedSymbols arena
            : map (\(_, cond, tran) -> FOL.symbols cond `Set.union` symbolsBT tran) trans
    SyBoLoop arena prog ->
      Set.unions
        $ usedSymbols arena
            : Set.map (loopPrime prog ++) (stateVars arena)
            : map (\(_, cond, tran) -> FOL.symbols cond `Set.union` symbolsBT tran) (loopTrans prog)

symbolsBT :: BookType -> Set Symbol
symbolsBT =
  \case
    Enforce st -> Set.unions $ map (FOL.symbols . snd) $ SymSt.toList st
    Return -> Set.empty
    SubProg prog -> symbols prog

---------------------------------------------------------------------------------------------------
-- Extraction
---------------------------------------------------------------------------------------------------
data Stmt
  = InfLoop Stmt
  | Cond Term Stmt
  | Sequence [Stmt]
  | Assign Symbol Term
  | Break
  | Continue
  | Abort
  | Read

extractProg :: Config -> Loc -> SyBo -> IO String
extractProg conf init sybo = do
  conf <- pure $ setName "Synth" conf
  let locVar = FOL.uniquePrefix "prog_counter" $ symbols sybo
  prog <- extractPG conf locVar sybo
  prog <- pure $ Sequence [Assign locVar (toLoc init), prog]
  pure $ printProg prog

---------------------------------------------------------------------------------------------------
-- Translation to program
---------------------------------------------------------------------------------------------------
extractPG :: Config -> Symbol -> SyBo -> IO Stmt
extractPG conf locVar =
  \case
    SyBoNone -> error "assert: this should not be there when extracting a program"
    SyBoNorm arena trans -> do
      trans <- mapM (extractTT conf locVar arena Nothing) $ reverse trans
      pure $ InfLoop $ Sequence $ trans ++ [Abort]
    SyBoLoop arena prog -> do
      let loopBack = Cond (isLoc locVar (loopLoc' prog)) $ Assign locVar (toLoc (loopLoc prog))
      let copyVars =
            Cond (isLoc locVar (loopLoc prog))
              $ Sequence
              $ map (\v -> Assign (loopPrime prog ++ v) (FOL.Var v (sortOf arena v)))
              $ Vars.stateVarL
              $ vars arena
      let mapLoc l = Map.findWithDefault (error "assert: unreachable code") l $ loopToMain prog
      trans <- mapM (extractTT conf locVar arena (Just mapLoc)) $ reverse $ loopTrans prog
      pure $ InfLoop $ Sequence $ loopBack : copyVars : trans ++ [Abort]

extractTT :: Config -> Symbol -> Arena -> Maybe (Loc -> Loc) -> (Loc, Term, BookType) -> IO Stmt
extractTT conf locVar arena mapLoc (loc, cond, pt) = do
  cond <- SMT.simplify conf cond
  unless (FOL.quantifierFree cond)
    $ die
    $ "synthesis failure: could not qelim" ++ SMTLib.toString cond
  let condStmt = Cond $ FOL.andf [isLoc locVar loc, cond]
   in case pt of
        Return ->
          case mapLoc of
            Nothing -> pure $ condStmt Break
            Just mapLoc -> pure $ condStmt $ Sequence [Assign locVar (toLoc (mapLoc loc)), Break]
        SubProg sub -> do
          sub <- extractPG conf locVar sub
          pure $ condStmt $ Sequence [sub, Continue]
        Enforce _ -> do
          assign <-
            error
              "TODO: compute next statments via skolemeization, ensure that primed variables stay the same, they are not to be changed"
          pure $ condStmt $ Sequence [Read, assign, Continue]

isLoc :: Symbol -> Loc -> Term
isLoc locVar l = FOL.Var locVar FOL.SInt `FOL.equal` toLoc l

toLoc :: Loc -> Term
toLoc = FOL.Const . FOL.CInt . Locs.toNumber

---------------------------------------------------------------------------------------------------
-- Printing
---------------------------------------------------------------------------------------------------
printProg :: Stmt -> String
printProg = error "TODO IMPLEMENT"
---------------------------------------------------------------------------------------------------
