{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration.LemmaFinding
  ( Constraint
  , LemSyms(..)
  , Lemma
  , prime
  , resolve
  , replaceLemma
  ) where

import Data.Bifunctor (second)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Heuristics
import Issy.Utils.Logging

-------------------------------------------------------------------------------
type Constraint = [Term]

-- Add primed stuff to lemma
data LemSyms =
  LemSyms Symbol Symbol Symbol
  deriving (Eq, Ord, Show)

data Lemma =
  Lemma Term Term Term Symbol

prime :: Lemma -> Symbol
prime (Lemma _ _ _ p) = p

mapL :: (Term -> Term) -> Lemma -> Lemma
mapL m (Lemma b s c prime) = Lemma (m b) (m s) (m c) prime

data LemInst =
  LemInst Constraint Lemma

-------------------------------------------------------------------------------
-- Instantiation
-------------------------------------------------------------------------------
primeT :: Variables -> Symbol -> Term -> Term
primeT vars prim =
  mapSymbol
    (\s ->
       if Vars.isStateVar vars s
         then prim ++ s
         else s)

extInt :: Symbol -> Integer -> Symbol
extInt prefix i = prefix ++ "_" ++ show i ++ "_"

replaceLemma :: Variables -> Lemma -> LemSyms -> Term -> Term
replaceLemma vars (Lemma b s c prime) (LemSyms bs ss cs) = go
  where
    go =
      \case
        Quant q t f -> Quant q t (go f)
        Lambda t f -> Lambda t (go f)
        Func fun args ->
          case fun of
            CustomF n _ _
              | n == bs ->
                let m = Map.fromList $ zip (Vars.stateVarL vars) args
                 in mapTermM m b
              | n == cs ->
                let m = Map.fromList $ zip (Vars.stateVarL vars) args
                 in mapTermM m c
              | n == ss ->
                let m =
                      Map.fromList
                        $ zip (Vars.stateVarL vars ++ map (prime ++) (Vars.stateVarL vars)) args
                 in mapTermM m s
              | otherwise -> Func fun $ map go args
            _ -> Func fun $ map go args
        QVar k -> QVar k
        Const c -> Const c
        Var v t -> Var v t

-------------------------------------------------------------------------------
-- Lemma generation
-------------------------------------------------------------------------------
imap :: (Integer -> a -> b) -> [a] -> [b]
imap m = zipWith m [1 ..]

varcl :: Symbol -> Symbol -> Symbol -> Symbol
varcl prefix subname cell = prefix ++ "_" ++ subname ++ "_" ++ cell

varcn :: Symbol -> Symbol -> Symbol
varcn prefix subname = prefix ++ "_" ++ subname ++ "_"

numbers :: Variables -> [Symbol]
numbers vars = filter (isNumber . Vars.sortOf vars) $ Vars.stateVarL vars

rankingFunc :: Variables -> Symbol -> (Term, [Term])
rankingFunc vars prf =
  let constVar =
        if any ((== SReal) . Vars.sortOf vars) (Vars.stateVars vars)
          then rvarT (varcn prf "c")
          else ivarT (varcn prf "c")
      cellL = filter (not . Vars.isBounded vars) $ numbers vars
   in ( addT
          (constVar
             : [br "a" c (br "b" c (Vars.mk vars c) (func "-" [Vars.mk vars c])) zeroT | c <- cellL])
      , [ constVar `leqT` Const (CInt 5)
        , Const (CInt (-5)) `leqT` constVar
        , addBools (bvarT . varcl prf "a" <$> cellL) 2 -- Might want to remove again!
        , orf (bvarT . varcl prf "a" <$> cellL) -- necessary to enforce possible step!
        ])
  where
    br n c = ite (bvarT (varcl prf n c))

rankLemma :: Variables -> Symbol -> (Lemma, [Term])
rankLemma vars prf =
  let prim = prf ++ "_nv_"
      (r, conR) = rankingFunc vars prf
      (diff, conD) =
        if any ((== SReal) . Vars.sortOf vars) (Vars.stateVars vars)
          then let eps = rvarT (varcn prf "epislon")
                in (eps, [func ">" [eps, zeroT], eps `leqT` oneT])
          else (oneT, [])
   in (Lemma (r `leqT` zeroT) (addT [diff, primeT vars prim r] `leqT` r) true prim, conR ++ conD)

invc :: Integer -> Variables -> Symbol -> (Term, [Term])
invc restr vars prf =
  let constVar = ivarT (varcn prf "c")
      cellL = numbers vars
   in ( addT [br "a" c (br "b" c (Vars.mk vars c) (func "-" [Vars.mk vars c])) zeroT | c <- cellL]
          `leqT` constVar
      , [ addBools (bvarT . varcl prf "a" <$> cellL) restr
        , constVar `leqT` Const (CInt 5)
        , Const (CInt (-5)) `leqT` constVar
        ])
  where
    br n c = ite (bvarT (varcl prf n c))

addBools :: [Term] -> Integer -> Term
addBools bools bound = addT (map (\b -> ite b oneT zeroT) bools) `leqT` Const (CInt bound)

constCompInv :: Integer -> Variables -> Symbol -> (Term, [Term])
constCompInv rest vars prf =
  let cellL = numbers vars
   in ( andf (map comp cellL)
      , addBools [orf [neg (vara c), neg (varb c)] | c <- cellL] rest
          : map (geqT oneT . varc) cellL
          ++ --THOSE are STRANGE!
           map (leqT (Const (CInt (-1))) . varc) cellL)
  where
    vara = bvarT . varcl prf "a"
    varb = bvarT . varcl prf "b"
    varc = ivarT . varcl prf "c"
    comp c =
      let cc = varc c
          var = Vars.mk vars c
          br n = ite (bvarT (varcl prf n c))
       in br "a" (br "b" true (func "=" [cc, var])) (br "b" (cc `leqT` var) (var `leqT` cc))

genInstH :: Int -> Variables -> Symbol -> LemInst
genInstH limit vars pref =
  let (ccomp, cinvc) = templateConfig limit
      act = bvarT (pref ++ "_act")
      (Lemma bi si ci prime, cnr) = rankLemma vars (pref ++ "_r_")
      (invs, cnis) = unzip $ imap (\i l -> invc l vars (extInt pref i)) cinvc
      (inv0, cni0) = constCompInv ccomp vars (pref ++ "_i0_")
      inv = andf (inv0 : invs)
   in LemInst
        (cnr ++ cni0 ++ concat cnis)
        (Lemma
           (andf [act, bi, inv])
           (andf [act, si, primeT vars prime inv])
           (andf [act, ci, inv])
           prime)

genInst :: Int -> Variables -> Symbol -> LemSyms -> Constraint -> Term -> (Constraint, Term, Lemma)
genInst limit vars pref l cons f =
  let LemInst consL li = genInstH limit vars pref
      rep = replaceLemma vars li l
   in (consL ++ map rep cons, rep f, li)

skolemize :: Int -> Variables -> Set Symbol -> Term -> Term
skolemize limit vars metas =
  mapTerm
    (\v s ->
       if v `elem` metas && (s == SBool || limit2skolemNum limit) --TODO: HACKY
         then Just $ Vars.unintPredTerm vars v
         else Nothing)

instantiate ::
     Int -> Variables -> Constraint -> Term -> [LemSyms] -> (Constraint, Term, [(LemSyms, Lemma)])
instantiate limit vars cons f ls =
  let syms = Set.unions (Vars.stateVars vars : symbols f : (symbols <$> cons))
      pref = uniquePrefix "p" syms
   in foldl
        (\(c, f, col) (l, i) ->
           let (c', f', li) = genInst limit vars (extInt pref i) l c f
            in (c', f', (l, li) : col))
        (cons, f, [])
        (zip ls [1 ..])

-------------------------------------------------------------------------------
-- Search
-------------------------------------------------------------------------------
resolveQE ::
     Config -> Int -> Variables -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveQE cfg limit vars cons f ls =
  let (cons', f', _) = instantiate limit vars cons f ls
      meta = Set.toList (frees (andf cons'))
      query = exists meta (andf (f' : cons'))
   in do
        cfg <- pure $ setName "Resolve QE" cfg
        lg cfg ["Try qelim on", SMTLib.toString query]
        resQE <- SMT.trySimplify cfg (Just (limit2to limit)) query
        case resQE of
          Just res -> do
            lg cfg ["Qelim yielded", SMTLib.toString res]
            return (res, [])
          Nothing -> do
            lg cfg ["Qelim failed and try later"]
            return (false, [])

resolveBoth ::
     Config -> Int -> Variables -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveBoth cfg limit vars cons f ls =
  let (cons', f', col) = instantiate limit vars cons f ls
      meta = frees (andf cons')
      theta = andf (f' : cons')
      sk = skolemize limit vars meta
      query = exists (Set.toList meta) theta
   in do
        cfg <- pure $ setName "Resolve QE+SK" cfg
        lg cfg ["Try Qelim on", SMTLib.toString query]
        resQE <- SMT.trySimplify cfg (Just (limit2to limit)) query
        case resQE of
          Just res -> do
            lg cfg ["Qelim yielded", SMTLib.toString res]
            thetaSk <-
              fromMaybe (sk theta) <$> SMT.trySimplifyUF cfg (Just (limit2to limit)) (sk theta)
            let querySk = Vars.forallX vars $ res `impl` thetaSk
            resSAT <- SMT.trySatModel cfg (Just (limit2toextract limit)) querySk
            case resSAT of
              Nothing -> do
                lg cfg ["Finding Model", "TO"]
                return (false, [])
              Just Nothing -> do
                lg cfg ["Finding Model", "UNSAT"]
                return (false, [])
              Just (Just m) -> do
                lg cfg ["Finding Model:", strM show SMTLib.toString (modelToMap m)]
                return (res, map (second (mapL (setModel m . sk))) col)
          Nothing -> do
            lg cfg ["Qelim failed and try later"]
            return (false, [])

resolve ::
     Config -> Int -> Variables -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolve cfg
  | generateProgram cfg = resolveBoth cfg
  | otherwise = resolveQE cfg
-------------------------------------------------------------------------------
