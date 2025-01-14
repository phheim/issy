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
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import Data.Set (Set)
import qualified Data.Set as Set
import System.Exit (die)

import qualified Issy.Base.Locations as Locs
import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Base.Variables (Variables)
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL (Sort, Symbol, Term)
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

getVars :: SyBo -> Variables
getVars =
  \case
    SyBoNone -> error "assert: unreachable code"
    SyBoNorm arena _ -> vars arena
    SyBoLoop arena _ -> vars arena

---------------------------------------------------------------------------------------------------
-- Extraction
---------------------------------------------------------------------------------------------------
data Prog
  = InfLoop Prog
  | Declare Symbol Sort
  | Cond Term Prog
  | Sequence [Prog]
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
  pure $ printProg (getVars sybo) prog

---------------------------------------------------------------------------------------------------
-- Translation to program
---------------------------------------------------------------------------------------------------
extractPG :: Config -> Symbol -> SyBo -> IO Prog
extractPG conf locVar =
  \case
    SyBoNone -> error "assert: this should not be there when extracting a program"
    SyBoNorm arena trans -> do
      trans <- mapM (extractTT conf locVar arena Nothing) $ reverse trans
      pure $ InfLoop $ Sequence $ trans ++ [Abort]
    SyBoLoop arena prog -> do
      let loopBack = Cond (isLoc locVar (loopLoc' prog)) $ Assign locVar (toLoc (loopLoc prog))
      let copyVarDecs =
            map (\v -> Declare (loopPrime prog ++ v) (sortOf arena v)) $ Vars.stateVarL $ vars arena
      let copyVars =
            Cond (isLoc locVar (loopLoc prog))
              $ Sequence
              $ map (\v -> Assign (loopPrime prog ++ v) (Vars.mk (vars arena) v))
              $ Vars.stateVarL
              $ vars arena
      let mapLoc l = Map.findWithDefault (error "assert: unreachable code") l $ loopToMain prog
      trans <- mapM (extractTT conf locVar arena (Just mapLoc)) $ reverse $ loopTrans prog
      let loop = InfLoop $ Sequence $ loopBack : copyVars : trans ++ [Abort]
      pure $ Sequence $ copyVarDecs ++ [loop]

extractTT :: Config -> Symbol -> Arena -> Maybe (Loc -> Loc) -> (Loc, Term, BookType) -> IO Prog
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
        Enforce target -> do
          assigns <- extractCPre conf arena locVar loc cond target
          assigns <- pure $ map (uncurry Assign) $ filter (uncurry isProperAssign) assigns
          pure $ condStmt $ Sequence $ [Read] ++ assigns ++ [Continue]

extractCPre :: Config -> Arena -> Symbol -> Loc -> Term -> SymSt -> IO [(Symbol, Term)]
extractCPre conf arena locVar loc cond targ = do
  targ <- pure $ SymSt.restrictTo (succs arena loc) targ
    -- Get new symbols
  let syms = Set.insert locVar $ usedSymbols arena `Set.union` SymSt.symbols targ
  let skolemPref = FOL.uniquePrefix "skolem_" syms
  let copyPref = FOL.uniquePrefix "copy_" syms
    -- Build type and arguments for skolem functions
  let vs = vars arena
  let inputSL = (\v -> (v, Vars.sortOf vs v)) <$> Vars.inputL vs
  let stateSL = (\v -> (v, Vars.sortOf vs v)) <$> Vars.stateVarL vs
  let stateSLC = map (first (copyPref ++)) stateSL
  let newSL = getNewVars vs targ
  let args = stateSL ++ inputSL ++ newSL
  let argsC = stateSLC ++ inputSL ++ newSL
    -- Build skolem functions for variables and location
  let skolem var = FOL.unintFunc (skolemPref ++ var) (Vars.sortOf vs var) args
  let skolemC var = FOL.unintFunc (skolemPref ++ var) (Vars.sortOf vs var) argsC
  let skolemL = FOL.unintFunc (skolemPref ++ locVar) FOL.SInt args
  let skolemLC = FOL.unintFunc (skolemPref ++ locVar) FOL.SInt argsC
    -- Build skolem constraints and skolem results
  let genSkolems l =
        FOL.equal skolemLC (toLoc l)
          : map (\v -> Vars.mk vs v `FOL.equal` skolemC v) (Vars.stateVarL vs)
  let skolemsRes = (locVar, skolemL) : map (\v -> (v, skolem v)) (Vars.stateVarL vs)
    -- Build new target with skolem functions
  targ <- pure $ SymSt.mapWithLoc (\l term -> FOL.andf (genSkolems l ++ [term])) targ
  let res = FOL.removePref copyPref $ cpre Sys arena targ loc
    -- Find skolem functions
  res <- SMT.simplifyUF conf $ Vars.forallX vs $ cond `FOL.impl` res
  model <- SMT.satModel conf res
  case model of
    Nothing -> die "synthesis failure: could not compute skolem function!"
    Just model ->
      mapM
        (\(v, f) -> do
           f <- SMT.simplify conf (FOL.setModel model f)
           pure (v, f))
        skolemsRes

getNewVars :: Variables -> SymSt -> [(Symbol, Sort)]
getNewVars vars =
  filter (\(v, _) -> not (Vars.isInput vars v || Vars.isStateVar vars v))
    . Set.toList
    . Set.fromList
    . concatMap (Map.toList . FOL.bindings . snd)
    . SymSt.toList

isLoc :: Symbol -> Loc -> Term
isLoc locVar l = FOL.Var locVar FOL.SInt `FOL.equal` toLoc l

toLoc :: Loc -> Term
toLoc = FOL.Const . FOL.CInt . Locs.toNumber

isProperAssign :: Symbol -> Term -> Bool
isProperAssign name =
  \case
    FOL.Var vname _ -> name /= vname
    _ -> True

---------------------------------------------------------------------------------------------------
-- Printing
---------------------------------------------------------------------------------------------------
printProg :: Variables -> Prog -> String
printProg vars prog =
  unlines $ makeHead vars ++ ["void main() {"] ++ indent (printStmt prog) ++ ["}"]

makeHead :: Variables -> [String]
makeHead vars =
  let inputDecl = map (\v -> Declare v (Vars.sortOf vars v)) $ Vars.inputL vars
      stateDecl = map (\v -> Declare v (Vars.sortOf vars v)) $ Vars.stateVarL vars
   in concatMap printStmt (inputDecl ++ stateDecl) ++ ["void read_inputs() { /* INSERT HERE */ }"]

printStmt :: Prog -> [String]
printStmt =
  \case
    Declare var FOL.SInt -> ["int " ++ var ++ " = 0;"]
    Declare var FOL.SReal -> ["double " ++ var ++ " = 0.0;"]
    Declare var FOL.SBool -> ["bool " ++ var ++ " = false;"]
    Declare _ _ -> error "assert: this should really not be reached"
    InfLoop prog -> "for(;;)" : indent (printStmt prog)
    Cond term prog -> ("if (" ++ printTerm term ++ ")") : indent (printStmt prog)
    Sequence prog -> ["{"] ++ indent (concatMap printStmt prog) ++ ["}"]
    Assign var term -> [var ++ " = " ++ printTerm term ++ ";"]
    Break -> ["break;"]
    Continue -> ["continue;"]
    Abort -> ["abort();"]
    Read -> ["read_inputs();"]

indent :: [String] -> [String]
indent = map ("    " ++)

printTerm :: Term -> String
printTerm =
  \case
    FOL.Var v _ -> v
    FOL.Func (FOL.CustomF {}) _ -> error "assert: unreachable code"
    FOL.QVar _ -> error "assert: unreachable code"
    FOL.Quant {} -> error "assert: unreachable code"
    FOL.Lambda _ _ -> error "assert: unreachable code"
    FOL.Const (FOL.CInt n) -> show n
    FOL.Const (FOL.CReal r) -> "(" ++ show (numerator r) ++ ".0 / " ++ show (denominator r) ++ ".0)"
    FOL.Const (FOL.CBool b)
      | b -> "true"
      | otherwise -> "false"
    FOL.Func (FOL.PredefF name) args ->
      case (name, args) of
        ("abs", [arg]) -> "(abs(" ++ printTerm arg ++ "))"
        ("not", [arg]) -> "(!(" ++ printTerm arg ++ "))"
        ("=", args) -> mulOp "==" args
        ("mod", args) -> mulOp "%" args
        ("and", args) -> mulOp "&&" args
        ("or", args) -> mulOp "||" args
        (name, arg)
          | name `elem` ["+", "*", "-", "/", "<=", ">=", "<", ">"] -> mulOp name args
          | otherwise ->
            error
              $ "assert: cannot convert " ++ name ++ " with " ++ show (length arg) ++ " arguments"
  where
    mulOp op =
      \case
        [] -> error "assert: found empty function"
        x:xr -> "(" ++ printTerm x ++ " " ++ concatMap (\y -> (op ++ " ") ++ printTerm y) xr ++ ")"
---------------------------------------------------------------------------------------------------
