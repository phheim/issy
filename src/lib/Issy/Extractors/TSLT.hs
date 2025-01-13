{-# LANGUAGE LambdaCase #-}

module Issy.Extractors.TSLT
  ( rpgToTSLT
  ) where

import Data.Fixed (Nano, showFixed)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Base.Variables as Vars
import Issy.Logic.FOL
import Issy.RPG
import qualified Issy.RPG as RPG

sortOf :: Game -> Symbol -> Sort
sortOf = Vars.sortOf . variables

encConst :: Bool -> Constant -> String
encConst upd =
  \case
    CInt n -> "i" ++ show n ++ "()"
    CReal r -> "r" ++ showFixed True (fromRational r :: Nano) ++ "()"
    CBool True
      | upd -> "i1()"
      | otherwise -> "true"
    CBool False
      | upd -> "i0()"
      | otherwise -> "false"

encOp :: (a -> String) -> String -> String -> [a] -> String
encOp encA op neut =
  \case
    [] -> neut
    [x] -> "(" ++ encA x ++ ")"
    x:xr -> "(" ++ encA x ++ " " ++ op ++ " " ++ encOp encA op neut xr ++ ")"

encVar :: Bool -> Symbol -> Sort -> String
encVar check v =
  \case
    SBool
      | check -> "(eq i_" ++ v ++ " i1())"
      | otherwise -> "i_" ++ v
    SInt -> "i_" ++ v
    SReal -> "r_" ++ v
    _ -> error "Not supported"

encTerm :: Bool -> Term -> String
encTerm upd =
  \case
    QVar _ -> error "Not supported"
    Quant {} -> error "Not supported"
    Lambda _ _ -> error "Not supported"
    Var v s -> encVar True v s
    Const c -> encConst upd c
    Func f args ->
      case f of
        CustomF {} -> error "Not supported"
        PredefF n
          | n == "or" && not upd -> encOp (encTerm upd) "||" "false" args
          | n == "and" && not upd -> encOp (encTerm upd) "&&" "true" args
          | n == "not" && not upd -> "(! " ++ encTerm upd (head args) ++ ")"
          | n == "-" && length args == 1 -> "(sub i0() " ++ encTerm upd (head args) ++ ")"
          | n == "+" ->
            if length args <= 2
              then op "add" args
              else "(add "
                     ++ encTerm upd (head args)
                     ++ " "
                     ++ encTerm upd (Func (PredefF "+") (tail args))
                     ++ ")"
          | n == "-" -> op "sub" args
          | n == "=" -> op "eq" args
          | n == "<" -> op "lt" args
          | n == ">" -> op "gt" args
          | n == "<=" -> op "le" args
          | n == ">=" -> op "ge" args
          | n == "*" -> op "mul" args
          | otherwise -> error (n ++ " not supported yet")
  where
    op name args = "(" ++ name ++ concatMap ((" " ++) . encTerm upd) args ++ ")"

encLoc :: Game -> Loc -> String
encLoc _ l = "[loc  <- i" ++ show (Locs.toNumber l) ++ "()]"

encTrans :: Game -> Transition -> String
encTrans g =
  \case
    TIf p tt tf ->
      let encP = encTerm False p
       in "("
            ++ encP
            ++ " -> "
            ++ encTrans g tt
            ++ ") && ((! "
            ++ encP
            ++ " ) -> "
            ++ encTrans g tf
            ++ ")"
    TSys upds -> concatMap ((++ " || ") . encUpd) upds ++ "false"
  where
    encUpd (u, l) =
      "("
        ++ concatMap
             (\(v, t) -> "[" ++ encVar False v (sortOf g v) ++ " <- " ++ encTerm True t ++ "] && ")
             (Map.toList u)
        ++ "X "
        ++ encLoc g l
        ++ ")"

encState :: Game -> String
encState g =
  "//-- State: "
    ++ concatMap (\v -> encVar False v (sortOf g v) ++ ", ") (Vars.stateVarL (variables g))
    ++ "loc"

encInputs :: Game -> String
encInputs g =
  case Vars.inputL (variables g) of
    [] -> ""
    i:ir -> "//-- Inputs: " ++ encV i ++ concatMap ((", " ++) . encV) ir
  where
    encV v = encVar False v (sortOf g v)

encGame :: Loc -> Game -> String
encGame init g =
  unlines
    $ [ encState g
      , encInputs g
      , "guarantee {"
      , encTerm False (RPG.inv g init)
      , " -> "
      , encLoc g init ++ ";"
      ]
        ++ map
             (\l ->
                "G ("
                  ++ encLoc g l
                  ++ " -> "
                  ++ encTerm False (RPG.inv g l)
                  ++ " && ("
                  ++ encTrans g (trans g l)
                  ++ "));")
             (Set.toList (locations g))
        ++ ["}"]

encCond :: Game -> String -> Set Loc -> String
encCond g op loc =
  let locs = Set.toList loc
   in "guarantee { " ++ op ++ "(" ++ concatMap (\l -> encLoc g l ++ " || ") locs ++ "false);}"

rpgToTSLT :: Game -> Objective -> String
rpgToTSLT g obj =
  unlines
    [ encGame (initialLoc obj) g
    , case winningCond obj of
        Reachability reach -> encCond g "F" reach
        Safety safe -> encCond g "G" safe
        Buechi fset -> encCond g "G F" fset
        CoBuechi fset -> encCond g "F G" fset
        _ -> error "Not supported"
    ]
