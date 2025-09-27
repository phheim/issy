-- TODO Document and restructure places
--
{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Encoders.LTLMT
  ( specToLTLMT
  , toFormula
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.SymbolicArena as SG
import qualified Issy.Games.Variables as Vars
import Issy.Games.Variables (Type(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.FOL (Constant(..), Function(..), Sort(..), Term(..))
import Issy.Logic.Temporal (BOp(..), Formula(..), UOp(..))
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Specification as Spec
import Issy.Specification (Specification)

specToLTLMT :: Specification -> String
specToLTLMT = uncurry formulaToLTLMT . shiftInTime . toFormula

-- | 'shiftInTime' adapts the formula such that unpriming it matches the different 
-- semantic in shifting in time.
shiftInTime :: (Variables, TL.Formula Term) -> (Variables, TL.Formula Term)
shiftInTime (vars, formula) =
  let inputPref = FOL.uniquePrefix "intial_value_" $ Vars.allSymbols vars
      mapping = map (\v -> (Vars.prime v, inputPref ++ v, Vars.sortOf vars v)) $ Vars.stateVarL vars
      inputEnc = map (\(var, init, sort) -> FOL.var var sort `FOL.equal` FOL.var init sort) mapping
      newVars = foldl (\vars (_, init, sort) -> Vars.addInput vars init sort) vars mapping
   in (newVars, And (map Atom inputEnc ++ [TL.next formula]))

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
