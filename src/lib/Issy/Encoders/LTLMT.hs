{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Encoders.LTLMT
  ( specToLTLMT
  , toFormula
  ) where

import Issy.Prelude

import Issy.Encoders.ToFormula (toFormula)
import qualified Issy.Games.Variables as Vars
import Issy.Games.Variables (Type(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.FOL (Constant(..), Function(..), Sort(..), Term(..))
import qualified Issy.Logic.RPLTL as RPLTL
import Issy.Logic.Temporal (BOp(..), Formula(..), UOp(..))
import qualified Issy.Logic.Temporal as TL
import Issy.Specification (Specification)
import Issy.Utils.Extra (enclose, paraInbetween)

specToLTLMT :: Specification -> String
specToLTLMT = uncurry formulaToLTLMT . second RPLTL.pushBoolF . toFormula

formulaToLTLMT :: Variables -> TL.Formula Term -> String
formulaToLTLMT vars term =
  "property: \""
    ++ printFormula vars term
    ++ "\"\n"
    ++ "variables:\n"
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

reencodeStates :: Variables -> Symbol -> Symbol
reencodeStates vars name
  | not (Vars.isStateVar vars name) && not (Vars.isStateVar vars (Vars.unprime name)) = name
  | head name == 'y' && Vars.isPrimed name = Vars.unprime ('y' : name)
  | head name == 'y' = "y(y" ++ name ++ ")"
  | Vars.isPrimed name = Vars.unprime name
  | otherwise = "y(" ++ name ++ ")"

printFormula :: Variables -> TL.Formula Term -> String
printFormula vars = go
  where
    trueConstVar = head $ Vars.stateVarL vars
    go =
      \case
        Atom t -> enclose '[' $ toPythonZ3 $ FOL.mapSymbol (reencodeStates vars) t
        And [] -> enclose '[' $ trueConstVar ++ "==" ++ trueConstVar -- There are no boolean constants!
        And [f] -> go f
        And fs -> paraInbetween " & " $ map go fs
        Or [] -> go $ Not $ And []
        Or [f] -> go f
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
        Const (CReal r) -> "(" ++ show (numerator r) ++ ".0 / " ++ show (denominator r) ++ ".0)"
        Const (CBool _) ->
          error "boolean constants are not supported by Syntheos parser in SMT context"
        Func FAdd fs -> paraInbetween " + " $ map go fs
        Func FMul fs -> paraInbetween " * " $ map go fs
        Func FEq [a, b] -> "(" ++ go a ++ ") == (" ++ go b ++ ")"
        Func FLt [a, b] -> "(" ++ go a ++ ") < (" ++ go b ++ ")"
        Func FLte [a, b] -> "(" ++ go a ++ ") <= (" ++ go b ++ ")"
        Func _ _ ->
          error "assert: other function patterns are not supported by Syntheos as it seems"
        QVar _ -> error "for now we do not support quantifiers here"
        Quant {} -> error "for now we do not support quantifiers here"
        Lambda _ _ -> error "for now we do not support lambdas here"
