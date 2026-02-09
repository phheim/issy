---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Acceleration.LemmaFinding
-- Description : Uninterpreted function lemma finding
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the finding of lemmas for uninterpreted function based acceleration.
-- This includes instantiating the respective constraints with templates using quantifier
-- elimination and skolemization to instantiate those.
---------------------------------------------------------------------------------------------------
module Issy.Solver.Acceleration.LemmaFinding
  ( Constraint
  , LemSyms(..)
  , Lemma(..)
  , resolve
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (generateProgram)
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration.Base (primeT)
import Issy.Solver.Acceleration.Heuristics (Heur)
import qualified Issy.Solver.Acceleration.Heuristics as H

---------------------------------------------------------------------------------------------------
-- | A shorthand for constraints. This is done to match the description in the POPL'24 paper.
-- A constraint should only contain close-terms, i.e. terms without free variables (but
-- maybe with uninterpreted function symbols).
type Constraint = [Term]

-- | Type for lemma symbols
data LemSyms =
  LemSyms Symbol Symbol Symbol Symbol
  -- ^ The lemma symbols are the base symbol, step relation symbol, conclusion symbol and
  -- priming symbol for the state variable copy.
  deriving (Eq, Ord, Show)

primeOf :: LemSyms -> Symbol
primeOf (LemSyms _ _ _ prime) = prime

symbolsOf :: LemSyms -> Set Symbol
symbolsOf (LemSyms bs ss cs prime) = Set.fromList [bs, ss, cs, prime]

-- | Type for an uninterpreted function lemma
data Lemma =
  Lemma Term Term Term
  -- ^ The parts of a simple lemma, with base, step relation and conclusion.

mapL :: (Term -> Term) -> Lemma -> Lemma
mapL m (Lemma b s c) = Lemma (m b) (m s) (m c)

data LemInst =
  LemInst Constraint Lemma

---------------------------------------------------------------------------------------------------
-- Instantiation
---------------------------------------------------------------------------------------------------
extInt :: Symbol -> Integer -> Symbol
extInt prefix i = prefix ++ "_" ++ show i ++ "_"

replaceLemma :: Variables -> Lemma -> LemSyms -> Term -> Term
replaceLemma vars (Lemma b s c) (LemSyms bs ss cs prime) =
  let vs = Vars.stateVarL vars
   in FOL.replaceUF ss (vs ++ map (prime ++) vs) s . FOL.replaceUF cs vs c . FOL.replaceUF bs vs b

---------------------------------------------------------------------------------------------------
-- Lemma generation
---------------------------------------------------------------------------------------------------
imap :: (Integer -> a -> b) -> [a] -> [b]
imap m = zipWith m [1 ..]

varcl :: Symbol -> Symbol -> Symbol -> Symbol
varcl prefix subname cell = prefix ++ "_" ++ subname ++ "_" ++ cell

varcn :: Symbol -> Symbol -> Symbol
varcn prefix subname = prefix ++ "_" ++ subname ++ "_"

numbers :: Variables -> [Symbol]
numbers vars = filter (FOL.isNumber . Vars.sortOf vars) $ Vars.stateVarL vars

rankingFunc :: Variables -> Symbol -> (Term, [Term])
rankingFunc vars prf =
  let constVar =
        if any ((== FOL.SReal) . Vars.sortOf vars) (Vars.stateVars vars)
          then FOL.rvarT (varcn prf "c")
          else FOL.ivarT (varcn prf "c")
      cellL = filter (not . Vars.isBounded vars) $ numbers vars
   in ( FOL.addT
          (constVar
             : [ br "a" c (br "b" c (Vars.mk vars c) (FOL.invT (Vars.mk vars c))) FOL.zeroT
               | c <- cellL
               ])
      , [ constVar `FOL.leqT` FOL.intConst 5
        , FOL.intConst (-5) `FOL.leqT` constVar
        , addBools (FOL.bvarT . varcl prf "a" <$> cellL) 2 -- Might want to remove again!
        , FOL.orf (FOL.bvarT . varcl prf "a" <$> cellL) -- necessary to enforce possible step!
        ])
  where
    br n c = FOL.ite (FOL.bvarT (varcl prf n c))

rankLemma :: Variables -> Symbol -> Symbol -> (Lemma, [Term])
rankLemma vars prime prf =
  let (r, conR) = rankingFunc vars prf
      (diff, conD) =
        if any ((== FOL.SReal) . Vars.sortOf vars) (Vars.stateVars vars)
          then let eps = FOL.rvarT (varcn prf "epislon")
                in (eps, [eps `FOL.gtT` FOL.zeroT, eps `FOL.leqT` FOL.oneT])
          else (FOL.oneT, [])
   in ( Lemma (r `FOL.leqT` FOL.zeroT) (FOL.addT [diff, primeT vars prime r] `FOL.leqT` r) FOL.true
      , conR ++ conD)

invc :: Integer -> Variables -> Symbol -> (Term, [Term])
invc restr vars prf =
  let constVar = FOL.ivarT (varcn prf "c")
      cellL = numbers vars
   in ( FOL.addT
          [br "a" c (br "b" c (Vars.mk vars c) (FOL.invT (Vars.mk vars c))) FOL.zeroT | c <- cellL]
          `FOL.leqT` constVar
      , [ addBools (FOL.bvarT . varcl prf "a" <$> cellL) restr
        , constVar `FOL.leqT` FOL.intConst 5
        , FOL.intConst (-5) `FOL.leqT` constVar
        ])
  where
    br n c = FOL.ite (FOL.bvarT (varcl prf n c))

addBools :: [Term] -> Integer -> Term
addBools bools bound =
  FOL.addT (map (\b -> FOL.ite b FOL.oneT FOL.zeroT) bools) `FOL.leqT` FOL.Const (FOL.CInt bound)

constCompInv :: Integer -> Variables -> Symbol -> (Term, [Term])
constCompInv rest vars prf =
  let cellL = numbers vars
   in ( FOL.andf (map comp cellL)
      , addBools [FOL.orf [FOL.neg (vara c), FOL.neg (varb c)] | c <- cellL] rest
          : map (FOL.geqT FOL.oneT . varc) cellL
          ++ --THOSE are STRANGE!
           map (FOL.leqT (FOL.intConst (-1)) . varc) cellL)
  where
    vara = FOL.bvarT . varcl prf "a"
    varb = FOL.bvarT . varcl prf "b"
    varc = FOL.ivarT . varcl prf "c"
    comp c =
      let cc = varc c
          var = Vars.mk vars c
          br n = FOL.ite (FOL.bvarT (varcl prf n c))
       in br
            "a"
            (br "b" FOL.true (cc `FOL.equal` var))
            (br "b" (cc `FOL.leqT` var) (var `FOL.leqT` cc))

genInstH :: Heur -> Variables -> Symbol -> Symbol -> LemInst
genInstH heur vars prime pref =
  let (ccomp, cinvc) = H.templatePattern heur
      act = FOL.bvarT (pref ++ "_act")
      (Lemma bi si ci, cnr) = rankLemma vars prime (pref ++ "_r_")
      (invs, cnis) = unzip $ imap (\i l -> invc l vars (extInt pref i)) cinvc
      (inv0, cni0) = constCompInv ccomp vars (pref ++ "_i0_")
      inv = FOL.andf (inv0 : invs)
   in LemInst
        (cnr ++ cni0 ++ concat cnis)
        (Lemma
           (FOL.andf [act, bi, inv])
           (FOL.andf [act, si, primeT vars prime inv])
           (FOL.andf [act, ci, inv]))

genInst :: Heur -> Variables -> Symbol -> LemSyms -> Constraint -> Term -> (Constraint, Term, Lemma)
genInst heur vars pref l cons f =
  let LemInst consL li = genInstH heur vars (primeOf l) pref
      rep = replaceLemma vars li l
   in (consL ++ map rep cons, rep f, li)

skolemize :: Variables -> Set Symbol -> Term -> Term
skolemize vars metas =
  FOL.mapTerm
    (\v _ ->
       if v `elem` metas
         then Just $ Vars.unintPredTerm vars v
         else Nothing)

instantiate ::
     Heur -> Variables -> Constraint -> Term -> [LemSyms] -> (Constraint, Term, [(LemSyms, Lemma)])
instantiate heur vars cons f ls =
  let syms =
        Set.unions $ Vars.stateVars vars : FOL.symbols f : map FOL.symbols cons ++ map symbolsOf ls
      pref = FOL.uniquePrefix "p" syms
   in foldl
        (\(c, f, col) (l, i) ->
           let (c', f', li) = genInst heur vars (extInt pref i) l c f
            in (c', f', (l, li) : col))
        (cons, f, [])
        (zip ls [1 ..])

---------------------------------------------------------------------------------------------------
-- Search
---------------------------------------------------------------------------------------------------
resolveQE ::
     Config -> Heur -> Variables -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveQE cfg heur vars cons f ls =
  let (cons', f', _) = instantiate heur vars cons f ls
      meta = Set.toList (FOL.frees (FOL.andf cons'))
      query = FOL.exists meta (FOL.andf (f' : cons'))
   in do
        cfg <- pure $ setName "ResQE" cfg
        lg cfg ["Try qelim on", SMTLib.toString query]
        resQE <- SMT.trySimplify cfg (H.lemmaResolveTO heur) query
        case resQE of
          Just res -> do
            lg cfg ["Qelim yielded", SMTLib.toString res]
            return (res, [])
          Nothing -> do
            lg cfg ["Qelim failed and try later"]
            return (FOL.false, [])

resolveBoth ::
     Config -> Heur -> Variables -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolveBoth cfg heur vars cons f ls =
  let (cons', f', col) = instantiate heur vars cons f ls
      meta = FOL.frees $ FOL.andf cons'
      theta = FOL.andf $ f' : cons'
      sk = skolemize vars meta
      query = FOL.exists (Set.toList meta) theta
   in do
        cfg <- pure $ setName "ResSK" cfg
        lg cfg ["Try Qelim on", SMTLib.toString query]
        resQE <- SMT.trySimplify cfg (H.lemmaResolveTO heur) query
        case resQE of
          Just res -> do
            lg cfg ["Qelim yielded", SMTLib.toString res]
            thetaSk <-
              fromMaybe (sk theta) <$> SMT.trySimplifyUF cfg (H.lemmaResolveTO heur) (sk theta)
            let querySk = Vars.forallX vars $ res `FOL.impl` thetaSk
            resSAT <- SMT.trySatModel cfg (H.lemmaResolveTO heur) querySk
            case resSAT of
              Nothing -> do
                lg cfg ["Finding Model", "TO"]
                return (FOL.false, [])
              Just Nothing -> do
                lg cfg ["Finding Model", "UNSAT"]
                return (FOL.false, [])
              Just (Just m) -> do
                lg cfg ["Finding Model:", strM show SMTLib.toString (FOL.modelToMap m)]
                return (res, map (second (mapL (FOL.setModel m . sk))) col)
          Nothing -> do
            lg cfg ["Qelim failed and try later"]
            return (FOL.false, [])

-- | Try to instantiate uninterpreted lemmas under a constraint and with a term that should
-- where these lemmas will be instantiated. The later is usually the conclusion that will
-- be added in the attractor.
resolve ::
     Config -> Heur -> Variables -> Constraint -> Term -> [LemSyms] -> IO (Term, [(LemSyms, Lemma)])
resolve cfg
  | generateProgram cfg = resolveBoth cfg
  | otherwise = resolveQE cfg
---------------------------------------------------------------------------------------------------
