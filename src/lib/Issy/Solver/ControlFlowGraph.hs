---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
-- TODO: Rename
module Issy.Solver.ControlFlowGraph
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
import Data.Map.Strict (Map)

import Issy.Base.SymbolicState (SymSt)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Config (Config, generateProgram)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import Issy.Solver.GameInterface

---------------------------------------------------------------------------------------------------
-- Bookkeeping
---------------------------------------------------------------------------------------------------
data SyBo
  = SyBoNone
  | SyBoNorm [(Loc, Term, ProgType)]
  | SyBoLoop LoopSyBo
  deriving (Eq, Ord, Show)

data LoopSyBo = LoopSyBo
  { loopLoc :: Loc
  , loopLoc' :: Loc
  , loopTrans :: [(Loc, Term, ProgType)]
        -- ^ in loop game locations
  , loopToMain :: Map Loc Loc
        -- ^ maps loop locations EXCEPT loopLoc' to old locations
  , loopPrime :: Symbol
  } deriving (Eq, Ord, Show)

data ProgType
  = Enforce SymSt
  | Return
  | SubProg SyBo
  deriving (Eq, Ord, Show)

--TODO: Optimize toward SyBoNone
normSyBo :: Config -> Arena -> SyBo
normSyBo conf _
  | generateProgram conf = SyBoNorm []
  | otherwise = SyBoNone

loopSyBo :: Config -> Arena -> Loc -> Loc -> Symbol -> Map Loc Loc -> SyBo
loopSyBo conf _ loc loc' prime newToOld
  | generateProgram conf =
    SyBoLoop
      $ LoopSyBo
          {loopLoc = loc, loopLoc' = loc', loopTrans = [], loopPrime = prime, loopToMain = newToOld}
  | otherwise = SyBoNone

fromStayIn :: Config -> Arena -> SymSt -> SymSt -> SyBo
fromStayIn conf arena src trg = enforceFromTo src trg $ normSyBo conf arena

addTrans :: Loc -> Term -> ProgType -> SyBo -> SyBo
addTrans loc cond tran =
  \case
    SyBoNone -> SyBoNone
    SyBoNorm trans -> SyBoNorm $ (loc, cond, tran) : trans
    SyBoLoop prog -> SyBoLoop $ prog {loopTrans = (loc, cond, tran) : loopTrans prog}

chainOn :: (Loc -> Term -> a -> a) -> SymSt -> a -> a
chainOn f st init =
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
    SyBoNorm trans -> SyBoNorm $ map mapTrans trans
    SyBoLoop prog -> SyBoLoop $ prog {loopTrans = map mapTrans (loopTrans prog)}
  where
    mapTrans (loc, cond, pt) =
      case pt of
        Enforce st -> (loc, f cond, Enforce (SymSt.map f st))
        Return -> (loc, f cond, Return)
        SubProg sub -> (loc, f cond, SubProg (mapTerms f sub))

empty :: SyBo
empty = SyBoNone

---------------------------------------------------------------------------------------------------
-- Extraction
---------------------------------------------------------------------------------------------------
data Stmt
  = InfLoop [Stmt]
  | Cond Term Stmt
  | Assign Symbol Term
  | Break
  | Continue
  | Abort
  | Read

extractProg :: Config -> Loc -> SyBo -> IO String
extractProg conf _ sybo = do
  prog <- extractPG conf sybo
  pure $ printProg prog

---------------------------------------------------------------------------------------------------
-- Translation to program
---------------------------------------------------------------------------------------------------
locVar :: Term
locVar = error "TODO IMPLEMENT"

locNum :: Loc -> Term
locNum = error "TODO IMPLEMENT"

extractPG :: Config -> SyBo -> IO Stmt
extractPG conf =
  \case
    SyBoNone -> error "assert: this should not be there when extracting a program"
    SyBoNorm trans -> do
      trans <- mapM (\(loc, cond, tr) -> extractTT conf loc cond tr) trans
      pure $ InfLoop $ reverse $ Abort : trans
    SyBoLoop prog -> error "TODO"
           -- pure $ 
           --     InfLoop $ Cond (locVar `FOL.equal` locNum loc') (error "TODO: set locVar to locNum loc") :
           --               Cond (locVar `FOL.equal` locNum loc ) (error "TODO: copy variables according to used loop prime, maybe this has to part of the loop game too!!!") :
           --               error "TODO: Map transitions, on return go back to old location type"

extractTT :: Config -> Loc -> Term -> ProgType -> IO Stmt
extractTT conf loc cond =
  \case
    Return -> error "TODO: condition; maybe map location to old location type; then break;"
    SubProg prog -> error "TODO: condition; insert sub program; then continue;"
    Enforce _ -> error "TODO: condition; then read inputs; then skolmeize; then continue"

---------------------------------------------------------------------------------------------------
-- Printing
---------------------------------------------------------------------------------------------------
printProg :: Stmt -> String
printProg = error "TODO: IMPLEMENT"
---------------------------------------------------------------------------------------------------
