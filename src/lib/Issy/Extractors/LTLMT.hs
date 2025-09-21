-- TODO Document and restructure places
--
{-# LANGUAGE LambdaCase #-}

module Issy.Extractors.LTLMT
  ( specToLTLMT
  , toFormula
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Base.Objectives as Obj
import qualified Issy.Base.Variables as Vars
import Issy.Base.Variables (Type(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.FOL (Constant(..), Function(..), Sort(..), Term(..))
import Issy.Logic.Temporal (BOp(..), Formula(..), UOp(..))
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Specification as Spec
import Issy.Specification (Specification)
import qualified Issy.SymbolicArena as SG

specToLTLMT :: Specification -> String
specToLTLMT = uncurry formulaToLTLMT . toFormula

toFormula :: Specification -> (Variables, TL.Formula Term)
toFormula spec =
  let prefix = FOL.uniquePrefix "loc_var_" $ Vars.allSymbols $ Spec.variables spec
      gamesAndLocVar =
        zipWith (curry (first ((prefix ++) . show))) [(1 :: Int) ..] $ Spec.games spec
      locVars = map fst gamesAndLocVar
      formula =
        TL.And $ map (uncurry gameToFormula) gamesAndLocVar ++ map TL.toFormula (Spec.formulas spec)
      newVars =
        foldl (\vars loc -> Vars.addStateVar vars loc FOL.SInt) (Spec.variables spec) locVars
   in (newVars, formula)

gameToFormula :: Symbol -> (SG.Arena, Objective) -> TL.Formula Term
gameToFormula locVar (arena, obj) =
  let holdLoc =
        TL.globally
          $ TL.Or
          $ map (\l -> TL.And [TL.Atom (encLoc l), TL.Atom (SG.domain arena l)])
          $ Set.toList
          $ SG.locSet arena
      transEff =
        TL.globally
          $ TL.Or
          $ map (\(l, l', p) -> TL.And [TL.Atom (encLoc l), TL.Atom (encLoc' l'), TL.Atom p])
          $ SG.transList arena
   in TL.And [Obj.toTemporalLogic encLoc obj, holdLoc, transEff]
  where
    locNums = Map.fromList $ zip (Set.toList $ SG.locSet arena) [1 ..]
    encLoc loc = FOL.ivarT locVar `FOL.equal` FOL.intConst (locNums ! loc)
    encLoc' = Vars.primeT (SG.variables arena) . encLoc

formulaToLTLMT :: Variables -> TL.Formula Term -> String
formulaToLTLMT vars term =
  "property \""
    ++ printFormula vars term
    ++ "\"\n"
    ++ concatMap
         (\v -> variableToLTLMT v (Vars.typeOf vars v))
         (Vars.inputL vars ++ Vars.stateVarL vars)

variableToLTLMT :: Symbol -> Type -> String
variableToLTLMT name =
  \case
    TInput sort -> unlines [printName name, printSort sort, "    owner: environment"]
    TState sort -> unlines [printName name, printSort sort, "    owner: system"]
  where
    printName =
      \case
        'y':nr -> "  - name: yy" ++ nr
        name -> "  - name: " ++ name
    printSort =
      \case
        SInt -> "    type: Int"
        SReal -> "    type: Real"
        SBool -> "    type: Bool"
        SFunc _ _ -> error "function not supported here"

-- TODO: Move to Utils and check usage!
paraInbetween :: String -> [String] -> String
paraInbetween sep elems = enclose '(' (inbetween sep elems)

-- TODO: Move to Utils and check usage!
inbetween :: String -> [String] -> String
inbetween sep =
  \case
    [] -> []
    [s] -> s
    s:sr -> s ++ sep ++ inbetween sep sr

-- TODO: Move to Utils and check usage!
enclose :: Char -> String -> String
enclose c str =
  case c of
    '(' -> "(" ++ str ++ ")"
    ')' -> "(" ++ str ++ ")"
    '[' -> "[" ++ str ++ "]"
    ']' -> "[" ++ str ++ "]"
    '{' -> "{" ++ str ++ "}"
    '}' -> "{" ++ str ++ "}"
    _ -> c : str ++ [c]

reencodeStates :: Variables -> Symbol -> Symbol
reencodeStates vars name
  | not (Vars.isStateVar vars name) = name
  | head name == 'y' && Vars.isPrimed name = Vars.unprime ('y' : name)
  | head name == 'y' = "y(y" ++ name ++ ")"
  | Vars.isPrimed name = Vars.unprime name
  | otherwise = "y(" ++ name ++ ")"

printFormula :: Variables -> TL.Formula Term -> String
printFormula vars = go
  where
    go =
      \case
        Atom t -> enclose '[' $ toPythonZ3 $ FOL.mapSymbol (reencodeStates vars) t
        And fs -> paraInbetween " & " $ map go fs
        Or fs -> paraInbetween " | " $ map go fs
        Not f -> enclose '(' $ "! " ++ go f
        UExp Next f -> enclose '(' $ "X " ++ go f
        UExp Globally f -> enclose '(' $ "G " ++ go f
        UExp Eventually f -> enclose '(' $ "F " ++ go f
        BExp Until f g -> go $ And [BExp WeakUntil f g, UExp Eventually g]
        BExp WeakUntil f g -> enclose '(' $ go f ++ " W " ++ go g
        BExp Release f g -> enclose '(' $ go f ++ " R " ++ go g

toPythonZ3 :: Term -> String
toPythonZ3 = go
  where
    go =
      \case
        Var var _ -> var
        Const (CInt n) -> show n
        Const (CBool b)
          | b -> "True"
          | otherwise -> "False"
        Const (CReal r) -> "(" ++ show (numerator r) ++ ".0 / " ++ show (denominator r) ++ ".0)"
        Func FAnd fs -> "And" ++ paraInbetween ", " (map go fs)
        Func FOr fs -> "Or" ++ paraInbetween ", " (map go fs)
        Func FDistinct _ -> error "TODO"
        Func FNot [f] -> "Not(" ++ go f ++ ")"
        Func FImply [a, b] -> "Implies(" ++ go a ++ ", " ++ go b ++ ")"
        Func FIte [a, b, c] -> "If(" ++ go a ++ ", " ++ go b ++ ", " ++ go c ++ ")"
        Func FAdd fs -> paraInbetween " + " $ map go fs
        Func FMul fs -> paraInbetween " * " $ map go fs
        Func FEq [a, b] -> "(" ++ go a ++ ") == (" ++ go b ++ ")"
        Func FLt [a, b] -> "(" ++ go a ++ ") < (" ++ go b ++ ")"
        Func FLte [a, b] -> "(" ++ go a ++ ") <= (" ++ go b ++ ")"
        Func FAbs [_] -> error "TODO"
        Func FToReal [_] -> error "TODO"
        Func FMod [_, _] -> error "TODO"
        Func FDivInt [_, _] -> error "TODO"
        Func FDivReal [_, _] -> error "TODO"
        Func _ _ -> error "assert: found unkown function pattern"
        QVar _ -> error "for now we do not support quantifiers here"
        Quant {} -> error "for now we do not support quantifiers here"
        Lambda _ _ -> error "for now we do not support lambdas here"
