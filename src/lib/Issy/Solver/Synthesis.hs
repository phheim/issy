---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Synthesis
-- Description : Synthesis and bookkeeping
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the methods to do synthesis. This includes bookkeeping the
-- necessary steps in the computation, as well as extracting a program from this stored
-- information.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Synthesis
  ( SyBo
  , -- Creation
    empty
  , normSyBo
  , loopSyBo
  , summarySyBo
  , fromStayIn
  , -- Add steps
    enforceTo
  , enforceFromTo
  , callOn
  , callOnSt
  , returnOn
  , -- Modify
    mapTerms
  , replaceUF
  , -- Program
    Prog(..)
  , extractProg
  , printProg
  , generateProg
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (generateProgram)
import qualified Issy.Games.Locations as Locs
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.Reasoning (skolemize)
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Solver.GameInterface

---------------------------------------------------------------------------------------------------
-- Bookkeeping
---------------------------------------------------------------------------------------------------
-- | Opaque bookkeeping data structure data stores information of the steps in the game solving.
data SyBo
  = SyBoNone
  -- ^ Indicates that no bookkeeping is done.
  | SyBoNorm Arena [(Loc, Term, BookType)]
  -- ^ Conditionals in an arena. They are evaluate from the start
  -- of the list and for given locations and guards
  | SyBoLoop Arena LoopSyBo
  -- ^ Loop arena book-keeping
  | SyBoSummary SummarySyBo
  -- ^ Enforcement summary book-keeping

data SummarySyBo = SummarySyBo
  { metaVars :: [(Symbol, Sort)]
  , preCond :: Term
  -- ^ condition on the state variables
  -- which this summary can be called and for which
  -- we need to compute the Skolem functions
  , metaCond :: Term
  -- ^ condition on the Skolem function for the meta variables that has to
  -- hold for all states which satisfy 'preCond'
  , subProg :: SyBo
  -- ^ program that archive the sub condition. Note that this should only
  -- contain the constrains that the meta variables do not change
  }

data LoopSyBo = LoopSyBo
  { loopLoc :: Loc
  -- ^ location of the loop game
  , loopLoc' :: Loc
  -- ^ copied location of the loop game
  , loopTrans :: [(Loc, Term, BookType)]
  , loopToMain :: Map Loc Loc
  -- ^ maps loop locations EXCEPT loopLoc' to old locations
  , loopPrime :: Symbol
  -- ^ priming of the variables that are kept constant
  }

-- | Actions that can be recorded
data BookType
  = Enforce SymSt
  -- ^ enforce the given symbolic state
  | SubProg SyBo
  -- ^ execute a sub-program/arena, like a loop arena part
  | Return
  -- ^ return to a higher level, i.e. the part that called a sub program

---------------------------------------------------------------------------------------------------
-- | Create the bookkeeping data structure that is always empty (and remain so).
-- This should only be used if no bookkeeping should be done.
empty :: SyBo
empty = SyBoNone

-- | Create the bookkeeping data structure for a normal arena.
normSyBo :: Config -> Arena -> SyBo
normSyBo conf arena
  | generateProgram conf = SyBoNorm arena []
  | otherwise = SyBoNone

-- | Create the bookkeeping for a loop arena. This methods needs
-- the loop arena, the location, the shadow location, the symbol used for priming the
-- constant variables for the step relation, as well as a mapping from location back to
-- locations from the original arena from which the loop-arena has been derived from.
loopSyBo :: Config -> Arena -> Loc -> Loc -> Symbol -> Map Loc Loc -> SyBo
loopSyBo conf arena loc loc' prime newToOld
  | generateProgram conf =
    SyBoLoop arena
      $ LoopSyBo
          {loopLoc = loc, loopLoc' = loc', loopTrans = [], loopPrime = prime, loopToMain = newToOld}
  | otherwise = SyBoNone

-- | Create the bookkeeping for enforcement summaries. This method needs the meta variables, 
-- skolemization information to instantiate those, and the book kept information from the
-- summaries computation. The first part of the term pair is a condition on the state 
-- variables where the summary can be called on and where we need to compute the Skolem
-- function. The second part is the condition for the Skolem functions for the meta variables 
-- that has to hold for all states which satisfy the precondition.
summarySyBo :: [(Symbol, Sort)] -> (Term, Term) -> SyBo -> SyBo
summarySyBo _ _ SyBoNone = SyBoNone
summarySyBo metaVars (preCond, metaCond) subProg =
  SyBoSummary
    $ SummarySyBo {metaVars = metaVars, preCond = preCond, metaCond = metaCond, subProg = subProg}

---------------------------------------------------------------------------------------------------
-- | Append an enforcement step from a given location and term into a symbolic to the actions
-- inside a book kept data structure.
enforceTo :: Loc -> Term -> SymSt -> SyBo -> SyBo
enforceTo loc cond = addTrans loc cond . Enforce

-- | Like 'enforceTo' but where the starting condition is an entire symbolic state.
enforceFromTo :: SymSt -> SymSt -> SyBo -> SyBo
enforceFromTo src trg = chainOn (\loc cond -> enforceTo loc cond trg) src

-- | Append calling a sub-part given a location and term as a guard.
callOn :: Loc -> Term -> SyBo -> SyBo -> SyBo
callOn loc cond = addTrans loc cond . SubProg

-- | Like 'callOn' but where the guard is an entire symbolic state.
callOnSt :: SymSt -> SyBo -> SyBo -> SyBo
callOnSt src sub = chainOn (\loc cond -> callOn loc cond sub) src

-- | When in a symbolic state, return to the caller.
returnOn :: SymSt -> SyBo -> SyBo
returnOn = chainOn (\loc cond -> addTrans loc cond Return)

-- | Create a new book keeping data structure that from a source symbolic state enforces to stay
-- in a target symbolic state.
fromStayIn :: Config -> Arena -> SymSt -> SymSt -> SyBo
fromStayIn conf arena src trg = enforceFromTo src trg $ normSyBo conf arena

addTrans :: Loc -> Term -> BookType -> SyBo -> SyBo
addTrans loc cond tran =
  \case
    SyBoNone -> SyBoNone
    SyBoNorm arena trans -> SyBoNorm arena $ (loc, cond, tran) : trans
    SyBoLoop arena prog -> SyBoLoop arena $ prog {loopTrans = (loc, cond, tran) : loopTrans prog}
    SyBoSummary _ -> error "assert: summaries have to be called immediatley"

chainOn :: (Loc -> Term -> SyBo -> SyBo) -> SymSt -> SyBo -> SyBo
chainOn f st =
  \case
    SyBoNone -> SyBoNone
    init ->
      let retList = filter ((/= FOL.false) . snd) $ SymSt.toList st
       in foldl (\a (loc, cond) -> f loc cond a) init retList

---------------------------------------------------------------------------------------------------
-- | Map all terms that appear in a book keeping data structure.
mapTerms :: (Term -> Term) -> SyBo -> SyBo
mapTerms f =
  \case
    SyBoNone -> SyBoNone
    SyBoNorm arena trans -> SyBoNorm arena $ map mapTrans trans
    SyBoLoop arena prog -> SyBoLoop arena $ prog {loopTrans = map mapTrans (loopTrans prog)}
    SyBoSummary sum -> SyBoSummary $ sum {subProg = mapTerms f (subProg sum)}
  where
    mapTrans (loc, cond, pt) =
      case pt of
        Enforce st -> (loc, f cond, Enforce (SymSt.map f st))
        Return -> (loc, f cond, Return)
        SubProg sub -> (loc, f cond, SubProg (mapTerms f sub))

-- | Instantiate an uninterpreted function in a book keeping data structure
-- with a concrete body. This is usually used to instantiate the step relation
-- after acceleration. For further details how this instantiation works see
-- 'FOL.replaceUF'.
replaceUF :: Symbol -> [Symbol] -> Term -> SyBo -> SyBo
replaceUF name argVars body = mapTerms $ FOL.replaceUF name argVars body

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
    SyBoSummary sum ->
      Set.unions
        [ Set.fromList (map fst (metaVars sum))
        , FOL.symbols (preCond sum)
        , FOL.symbols (metaCond sum)
        , symbols (subProg sum)
        ]

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
    SyBoLoop _ _ -> error "assert: as this is meant to be called, this is proably bad"
    SyBoSummary _ -> error "assert: as this is meant to be called, this is proably bad"

---------------------------------------------------------------------------------------------------
-- Programs
---------------------------------------------------------------------------------------------------
-- | Representation of an abstract program that represents a system player strategy.
-- Note that the evaluation what a step is in e.g. an arena depends on the occurrence of
-- a read. The current state is considered at a read, then the input variables are updated,
-- and then some computation done (that changes the state). The update state (i.e. the primed
-- state variables) are those just before the next read. To be sound, a read must always occur.
data Prog
  = Abort
  -- ^ A placeholder that should never be reached.
  -- If this is reached that means that either there is a bug in the synthesis tool
  -- or the assumptions of the specification have been violated.
  | Read
  -- ^ Read and set the input variables and evaluate the state.
  | InfLoop Prog
  -- ^ An infinite loop for a program part.
  | Break
  -- ^ Break out of a loop.
  | Continue
  -- ^ Restart a loop at the start of the loop body.
  | Declare Symbol Sort
  -- ^ A declaration of a variable.
  | Cond Term Prog
  -- ^ A condition for a program part.
  | Sequence [Prog]
  -- ^ Sequence of program parts.
  | Assign Symbol Term
  -- ^ Assignment to a variable.

-- | Tie together 'extractProg' and 'printProg' to compute a program and print
-- it as a C program.
generateProg :: Config -> Loc -> SyBo -> IO String
generateProg conf init sybo = uncurry printProg <$> extractProg conf init sybo

---------------------------------------------------------------------------------------------------
-- Translation to program
---------------------------------------------------------------------------------------------------
-- | Compute an abstract program out of a bookkeeping data structure. This is very
-- computation heavy and might include Skolem function computation.
extractProg :: Config -> Loc -> SyBo -> IO (Variables, Prog)
extractProg conf init sybo = do
  conf <- pure $ setName "Synth" conf
  let locVar = FOL.uniquePrefix "prog_counter" $ symbols sybo
  prog <- extractPG conf locVar sybo
  prog <- pure $ Sequence [Declare locVar FOL.SInt, Assign locVar (toLoc init), prog]
  pure (getVars sybo, prog)

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
    SyBoSummary sum -> do
      lgd conf ["Skolemize", SMTLib.toString (metaCond sum)]
      skolems <- skolemize conf (metaVars sum) (preCond sum) (metaCond sum)
      let metaDec = map (uncurry Declare) $ metaVars sum
      let metaCopy = map (\(v, _) -> Assign v (skolems ! v)) $ metaVars sum
      subProg <- extractPG conf locVar $ subProg sum
      pure $ Sequence $ metaDec ++ metaCopy ++ [subProg]

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
          assigns <- syntCPre conf arena locVar Locs.toNumber loc cond target
          assigns <- pure $ map (uncurry Assign) $ filter (uncurry isProperAssign) assigns
          pure $ condStmt $ Sequence $ [Read] ++ assigns ++ [Continue]

isLoc :: Symbol -> Loc -> Term
isLoc locVar l = FOL.var locVar FOL.SInt `FOL.equal` toLoc l

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
-- | Print an abstract program as a C program.
printProg :: Variables -> Prog -> String
printProg vars prog =
  unlines $ makeHead vars ++ ["void main() {"] ++ indent (printStmt prog) ++ ["}"]

makeHead :: Variables -> [String]
makeHead vars =
  let inputDecl = map (\v -> Declare v (Vars.sortOf vars v)) $ Vars.inputL vars
      stateDecl = map (\v -> Declare v (Vars.sortOf vars v)) $ Vars.stateVarL vars
   in ["#include <stdlib.h>"]
        ++ concatMap printStmt inputDecl
        ++ ["void read_inputs() { /* INSERT HERE */ }"]
        ++ concatMap printStmt stateDecl

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
indent = map ("  " ++)

printTerm :: Term -> String
printTerm =
  \case
    FOL.Var v _ -> v
    FOL.Func (FOL.CustomF name _ _) _ -> error $ "assert: unreachable code, found " ++ name
    FOL.QVar _ -> error "assert: unreachable code"
    FOL.Quant {} -> error "assert: unreachable code"
    FOL.Lambda _ _ -> error "assert: unreachable code"
    FOL.Const (FOL.CInt n) -> show n
    FOL.Const (FOL.CReal r) -> "(" ++ show (numerator r) ++ ".0 / " ++ show (denominator r) ++ ".0)"
    FOL.Const (FOL.CBool b)
      | b -> "true"
      | otherwise -> "false"
    FOL.Func func args ->
      case (SMTLib.funcToString func, args) of
        ("abs", [arg]) -> "(abs(" ++ printTerm arg ++ "))"
        ("-", [arg]) -> "(- (" ++ printTerm arg ++ "))"
        ("not", [arg]) -> "(!(" ++ printTerm arg ++ "))"
        ("ite", [c, th, el]) ->
          "(" ++ printTerm c ++ " ? " ++ printTerm th ++ " : " ++ printTerm el ++ ")"
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
