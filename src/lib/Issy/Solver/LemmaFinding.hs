{-# LANGUAGE LambdaCase, RecordWildCards #-}

module Issy.Solver.LemmaFinding
  ( Constraint
  , LemSyms(..)
  , Lemma(..)
  , TypedCells(..)
  , resolve
  , replaceLemma
  ) where

import Data.Bifunctor (second)
import qualified Data.Map.Strict as Map (fromList)
import Data.Maybe (fromMaybe)
import Data.Set (Set, unions)
import qualified Data.Set as Set (fromList, toList)

import Issy.Config (Config, generateProgram, setName, skolemizeOnly)
import Issy.Logic.FOL
import Issy.Logic.SMT
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Heuristics
import Issy.Utils.Logging

-------------------------------------------------------------------------------
type Constraint = [Term]

-- Add primed stuff to lemma
data LemSyms =
  LemSyms Symbol Symbol Symbol
  deriving (Eq, Ord, Show)

data Lemma =
  Lemma Term Term Term Symbol

mapL :: (Term -> Term) -> Lemma -> Lemma
mapL m (Lemma b s c prime) = Lemma (m b) (m s) (m c) prime

data TypedCells = TypedCells
  { cells :: [Symbol]
  , ty :: Symbol -> Sort
  , bounded :: [Symbol]
  }

cellsS :: TypedCells -> Set Symbol
cellsS = Set.fromList . cells

data LemInst =
  LemInst Constraint Lemma

-------------------------------------------------------------------------------
-- Instantiation
-------------------------------------------------------------------------------
primeT :: TypedCells -> Symbol -> Term -> Term
primeT tyc prim =
  mapSymbol
    (\s ->
       if s `elem` cells tyc
         then prim ++ s
         else s)

extInt :: Symbol -> Integer -> Symbol
extInt prefix i = prefix ++ "_" ++ show i ++ "_"

replaceLemma :: TypedCells -> Lemma -> LemSyms -> Term -> Term
replaceLemma tyc (Lemma b s c prime) (LemSyms bs ss cs) = rec
  where
    rec =
      \case
        Quant q t f -> Quant q t (rec f)
        Lambda t f -> Lambda t (rec f)
        Func n args
          | n == UnintF bs ->
            let m = Map.fromList (zip (cells tyc) args)
             in mapTermM m b
          | n == UnintF cs ->
            let m = Map.fromList (zip (cells tyc) args)
             in mapTermM m c
          | n == UnintF ss ->
            let m = Map.fromList (zip (cells tyc ++ map (prime ++) (cells tyc)) args)
             in mapTermM m s
          | otherwise -> Func n (rec <$> args)
        QVar k -> QVar k
        Const c -> Const c
        Var v t -> Var v t

-------------------------------------------------------------------------------
-- Lemma generation
-------------------------------------------------------------------------------
imap :: (Integer -> a -> b) -> [a] -> [b]
imap m xs = uncurry m <$> zip [1 ..] xs

varcl :: Symbol -> Symbol -> Symbol -> Symbol
varcl prefix subname cell = prefix ++ "_" ++ subname ++ "_" ++ cell

varcn :: Symbol -> Symbol -> Symbol
varcn prefix subname = prefix ++ "_" ++ subname ++ "_"

rankingFunc :: TypedCells -> Symbol -> (Term, [Term])
rankingFunc (TypedCells {..}) prf =
  let constVar =
        if any ((== SReal) . ty) cells
          then rvarT (varcn prf "c")
          else ivarT (varcn prf "c")
      cellL = filter (isNumber . ty) $ filter (`notElem` bounded) cells
   in ( addT
          (constVar
             : [br "a" c (br "b" c (Var c (ty c)) (func "-" [Var c (ty c)])) zeroT | c <- cellL])
      , [ constVar `leqT` Const (CInt 5)
        , Const (CInt (-5)) `leqT` constVar
        , addBools (bvarT . varcl prf "a" <$> cellL) 2 -- Might want to remove again!
        , orf (bvarT . varcl prf "a" <$> cellL) -- necessary to enforce possible step!
        ])
  where
    br n c = ite (bvarT (varcl prf n c))

rankLemma :: TypedCells -> Symbol -> (Lemma, [Term])
rankLemma tyc@(TypedCells {..}) prf =
  let prim = prf ++ "_nv_"
      (r, conR) = rankingFunc tyc prf
      (diff, conD) =
        if any ((== SReal) . ty) cells
          then let eps = rvarT (varcn prf "epislon")
                in (eps, [func ">" [eps, zeroT], eps `leqT` oneT])
          else (oneT, [])
   in (Lemma (r `leqT` zeroT) (addT [diff, primeT tyc prim r] `leqT` r) true prim, conR ++ conD)

invc :: Integer -> TypedCells -> Symbol -> (Term, [Term])
invc restr (TypedCells {..}) prf =
  let constVar = ivarT (varcn prf "c")
      cellL = filter (isNumber . ty) cells
   in ( addT [br "a" c (br "b" c (Var c (ty c)) (func "-" [Var c (ty c)])) zeroT | c <- cellL]
          `leqT` constVar
      , [ addBools (bvarT . varcl prf "a" <$> cellL) restr
        , constVar `leqT` Const (CInt 5)
        , Const (CInt (-5)) `leqT` constVar
        ])
  where
    br n c = ite (bvarT (varcl prf n c))

addBools :: [Term] -> Integer -> Term
addBools bools bound = addT (map (\b -> ite b oneT zeroT) bools) `leqT` Const (CInt bound)

constCompInv :: Integer -> TypedCells -> Symbol -> (Term, [Term])
constCompInv rest (TypedCells {..}) prf =
  let cellL = filter (isNumber . ty) cells
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
          var = Var c (ty c)
          br n = ite (bvarT (varcl prf n c))
       in br "a" (br "b" true (func "=" [cc, var])) (br "b" (cc `leqT` var) (var `leqT` cc))

genInstH :: Int -> TypedCells -> Symbol -> LemInst
genInstH limit tyc pref =
  let (ccomp, cinvc) = templateConfig limit
      act = bvarT (pref ++ "_act")
      (Lemma bi si ci prime, cnr) = rankLemma tyc (pref ++ "_r_")
      (invs, cnis) = unzip $ imap (\i l -> invc l tyc (extInt pref i)) cinvc
      (inv0, cni0) = constCompInv ccomp tyc (pref ++ "_i0_")
      inv = andf (inv0 : invs)
   in LemInst
        (cnr ++ cni0 ++ concat cnis)
        (Lemma
           (andf [act, bi, inv])
           (andf [act, si, primeT tyc prime inv])
           (andf [act, ci, inv])
           prime)

genInst :: Int -> TypedCells -> Symbol -> LemSyms -> Constraint -> Term -> (Constraint, Term, Lemma)
genInst limit tyc pref l cons f =
  let LemInst consL li = genInstH limit tyc pref
      rep = replaceLemma tyc li l
   in (consL ++ map rep cons, rep f, li)

skolemize :: Int -> TypedCells -> Set Symbol -> Term -> Term
skolemize limit (TypedCells {..}) metas =
  mapTerm
    (\v s ->
       if v `elem` metas && (s == SBool || limit2skolemNum limit) --TODO: HACKY
         then Just (Func (CustomF v (map ty cells) s) ((\v -> Var v (ty v)) <$> cells))
         else Nothing)

instantiate ::
     Int -> TypedCells -> Constraint -> Term -> [LemSyms] -> (Constraint, Term, [(LemSyms, Lemma)])
instantiate limit tyc cons f ls =
  let syms = unions (cellsS tyc : symbols f : (symbols <$> cons))
      pref = uniquePrefix "p" syms
   in foldl
        (\(c, f, col) (l, i) ->
           let (c', f', li) = genInst limit tyc (extInt pref i) l c f
            in (c', f', (l, li) : col))
        (cons, f, [])
        (zip ls [1 ..])

-------------------------------------------------------------------------------
-- Search
-------------------------------------------------------------------------------
resolveQE ::
     Config -> Int -> TypedCells -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveQE cfg limit tyc cons f ls =
  let (cons', f', _) = instantiate limit tyc cons f ls
      meta = Set.toList (frees (andf cons'))
      query = exists meta (andf (f' : cons'))
   in do
        cfg <- pure $ setName "Resolve QE" cfg
        lg cfg ["Try qelim on", smtLib2 query]
        resQE <- simplifyTO cfg (Just (limit2to limit)) query
        case resQE of
          Just res -> do
            lg cfg ["Qelim yielded", smtLib2 res]
            return (res, [])
          Nothing -> do
            lg cfg ["Qelim failed and try later"]
            return (false, [])

resolveSk ::
     Config -> Int -> TypedCells -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveSk cfg limit tyc cons f ls = do
  cfg <- pure $ setName "Resolve SK" cfg
  let (cons', f', col) = instantiate limit tyc cons f ls
  let meta = frees (andf cons')
  let theta = andf (f' : cons')
  let sk = skolemize limit tyc meta
  thetaSk <- fromMaybe (sk theta) <$> trySimplifyUF cfg (limit2to limit) (sk theta)
  let query = forAll (cells tyc) (exists (Set.toList meta) theta `impl` thetaSk)
  lg cfg ["Try sat on", smtLib2 query]
  resSAT <- satModelTO cfg (Just (limit2toextract limit)) query
  case resSAT of
    Nothing -> do
      lg cfg ["Finding Model", "TO"]
      return (false, [])
    Just Nothing -> do
      lg cfg ["Finding Model", "UNSAT"]
      return (false, [])
    Just (Just m) -> do
      lg cfg ["Finding Model", strM show smtLib2 (modelToMap m)]
      res <- simplify cfg (setModel m (sk f'))
      return (res, map (second (mapL (setModel m . sk))) col)

resolveBoth ::
     Config -> Int -> TypedCells -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveBoth cfg limit tyc cons f ls =
  let (cons', f', col) = instantiate limit tyc cons f ls
      meta = frees (andf cons')
      theta = andf (f' : cons')
      sk = skolemize limit tyc meta
      query = exists (Set.toList meta) theta
   in do
        cfg <- pure $ setName "Resolve QE+SK" cfg
        lg cfg ["Try Qelim on", smtLib2 query]
        resQE <- simplifyTO cfg (Just (limit2to limit)) query
        case resQE of
          Just res -> do
            lg cfg ["Qelim yielded", smtLib2 res]
            thetaSk <- fromMaybe (sk theta) <$> trySimplifyUF cfg (limit2to limit) (sk theta)
            let querySk = forAll (cells tyc) (res `impl` thetaSk)
            resSAT <- satModelTO cfg (Just (limit2toextract limit)) querySk
            case resSAT of
              Nothing -> do
                lg cfg ["Finding Model", "TO"]
                return (false, [])
              Just Nothing -> do
                lg cfg ["Finding Model", "UNSAT"]
                return (false, [])
              Just (Just m) -> do
                lg cfg ["Finding Model:", strM show smtLib2 (modelToMap m)]
                return (res, map (second (mapL (setModel m . sk))) col)
          Nothing -> do
            lg cfg ["Qelim failed and try later"]
            return (false, [])

resolve ::
     Config -> Int -> TypedCells -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolve cfg
  | skolemizeOnly cfg = resolveSk cfg
  | generateProgram cfg = resolveBoth cfg
  | otherwise = resolveQE cfg
-------------------------------------------------------------------------------
