-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Monitor.State
  ( State
  , -- Creation and normalization 
    initSt
  , trueSt
  , falseSt
  , normSt
  , simpleNormSt
  , isSafeSt
  , isTrue
  , isFalse
  , -- Expansion operations
    ExpansionState
  , toExpansionState
  , fromExpansionState
  , normESt
  , replaceSt
  , replacesSt
  , pickFreeSt
  , pickUpdSt
  , setUpdSt
  , expandSt
  , shiftSt
  , -- Rules operation
    Domain(..)
  , fset
  , eset
  , impD
  , current
  , dedInv
  , weaks
  , reorganise
  , invalidate
  , addImp
  , mapFs
  , addFacts
  , newImps
  , filterDom
  , -- Pretty printing
    stateToString
  ) where

-------------------------------------------------------------------------------
import Data.List (partition)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import Issy.Monitor.Formula (Formula)
import qualified Issy.Monitor.Formula as MF
import Issy.Utils.Logging

-------------------------------------------------------------------------------
data State = State
  { ea :: [Formula]
  , fa :: [Formula]
  , eg :: [Formula]
  , fg :: [Formula]
  , impA :: Set (Formula, Formula)
  , impG :: Set (Formula, Formula)
  } deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Initialization and normalisation
-------------------------------------------------------------------------------
initSt :: [Formula] -> [Formula] -> State
initSt assume guarantee =
  normSt $ State {ea = [], fa = assume, eg = [], fg = guarantee, impA = Set.empty, impG = Set.empty}

falseSt :: State
falseSt =
  State {ea = [], fa = [], eg = [MF.FFalse], fg = [MF.FFalse], impA = Set.empty, impG = Set.empty}

trueSt :: State
trueSt =
  State {ea = [MF.FFalse], fa = [MF.FFalse], eg = [], fg = [], impA = Set.empty, impG = Set.empty}

genericNormSt :: ([Formula] -> [Formula]) -> State -> State
genericNormSt norm st =
  let ea' = norm (ea st)
      fa' = norm (fa st)
      eg' = norm (eg st)
      fg' = norm (fg st)
   in if ea' == [MF.FFalse] || fa' == [MF.FFalse] || null (fg' ++ eg')
        then trueSt
        else if fg' == [MF.FFalse] || eg' == [MF.FFalse]
               then if null (fa' ++ ea')
                      then falseSt
                      else falseSt {ea = ea', fa = fa', impA = impA st}
               else st {ea = ea', fa = fa', eg = eg', fg = fg'}

normSt :: State -> State
normSt = genericNormSt $ MF.normAnd . map MF.toplevelCNF

simpleNormSt :: State -> State
simpleNormSt = genericNormSt MF.normAndLight

isSafeSt :: State -> Bool
isSafeSt st =
  all MF.notTemporal (ea st)
    && all MF.notTemporal (fa st)
    && all MF.isSafe (eg st)
    && all MF.isSafe (fg st)

isFalse :: State -> Bool
isFalse st = null (ea st ++ fa st) && (MF.FFalse `elem` (eg st ++ fg st))

isTrue :: State -> Bool
isTrue st = null (eg st ++ fg st) || (MF.FFalse `elem` ea st) || (MF.FFalse `elem` fa st)

-------------------------------------------------------------------------------
-- Expanions
-------------------------------------------------------------------------------
newtype ExpansionState =
  ExpansionState State
  deriving (Eq, Ord, Show)

toExpansionState :: State -> ExpansionState
toExpansionState st = ExpansionState $ st {impA = Set.empty, impG = Set.empty}

fromExpansionState :: State -> ExpansionState -> State
fromExpansionState oldSt (ExpansionState expSt) = expSt {impA = impA oldSt, impG = impG oldSt}

mapES :: (State -> State) -> ExpansionState -> ExpansionState
mapES mp (ExpansionState st) = ExpansionState (mp st)

normESt :: ExpansionState -> ExpansionState
normESt = mapES normSt

mapFormulas :: (Formula -> Formula) -> State -> State
mapFormulas fm st =
  State
    { ea = fm <$> ea st
    , fa = fm <$> fa st
    , eg = fm <$> eg st
    , fg = fm <$> fg st
    , impA = impA st
    , impG = impG st
    }

replaceSt :: (Term, Bool) -> ExpansionState -> ExpansionState
replaceSt asg = mapES $ simpleNormSt . mapFormulas (MF.replaceT asg)

replacesSt :: [(Term, Bool)] -> ExpansionState -> ExpansionState
replacesSt asgs =
  mapES $ \st -> simpleNormSt $ foldl (\st asg -> mapFormulas (MF.replaceT asg) st) st asgs

stateFormulas :: State -> [Formula]
stateFormulas st = concat [ea st, fa st, eg st, fg st]

pickFreeSt :: ExpansionState -> Maybe Term
pickFreeSt (ExpansionState st) =
  case concatMap MF.currentTerms (stateFormulas st) of
    [] -> Nothing
    (term, _):_ -> Just term

pickUpdSt :: ExpansionState -> Maybe (Symbol, Term)
pickUpdSt (ExpansionState st) =
  case concatMap MF.currentUpdates (stateFormulas st) of
    [] -> Nothing
    upd:_ -> Just upd

setUpdSt :: (Symbol, Term) -> Bool -> ExpansionState -> ExpansionState
setUpdSt upd pol = mapES $ simpleNormSt . mapFormulas (MF.replaceU upd pol)

expandSt :: ExpansionState -> ExpansionState
expandSt = mapES $ mapFormulas MF.expand

shiftSt :: ExpansionState -> ExpansionState
shiftSt = mapES $ mapFormulas MF.shift

-------------------------------------------------------------------------------
-- Rule access and modification operations
-------------------------------------------------------------------------------
data Domain
  = Assumptions
  | Guarantees
  deriving (Eq, Ord, Show)

fset :: Domain -> State -> [Formula]
fset Assumptions = fa
fset Guarantees = fg

eset :: Domain -> State -> [Formula]
eset Assumptions = ea
eset Guarantees = eg

impD :: Domain -> State -> Set (Formula, Formula)
impD Assumptions = impA
impD Guarantees = impG

current :: Domain -> State -> [Formula]
current dom st =
  case dom of
    Assumptions -> go $ eset Assumptions st
    Guarantees -> go $ eset Assumptions st ++ eset Guarantees st
  where
    go =
      \case
        [] -> []
        MF.FGlobally f:fr
          | MF.notTemporal f -> f : go fr
          | otherwise -> go fr
        f:fr
          | MF.notTemporal f -> f : go fr
          | otherwise -> go fr

dedInv :: Domain -> State -> [Formula]
dedInv dom =
  filter MF.notTemporal . map (\(prem, conc) -> MF.for [MF.fnot prem, conc]) . Set.toList . impD dom

weaks :: Domain -> State -> [(Formula, Formula)]
weaks dom = go . fset dom
  where
    go =
      \case
        [] -> []
        MF.FWeak f g:fr
          | MF.notTemporal f && MF.notTemporal g -> (f, g) : go fr
          | otherwise -> go fr
        _:fr -> go fr

reorganise :: State -> State
reorganise st =
  let (conA, fa') = partition consolidate (fa st)
      (conG, fg') = partition consolidate (fg st)
   in st {ea = ea st ++ conA, fa = fa', eg = eg st ++ conG, fg = fg'}

consolidate :: Formula -> Bool
consolidate =
  \case
    MF.FGlobally f -> MF.notTemporal f
    MF.FWeak f g -> MF.notTemporal f && MF.notTemporal g
    f -> MF.notTemporal f

invalidate :: Domain -> State -> State
invalidate Assumptions _ = trueSt
invalidate Guarantees st = st {eg = [MF.FFalse], fg = [MF.FFalse], impG = Set.empty}

addImp :: Config -> String -> Domain -> State -> (Formula, Formula) -> IO State
addImp _ _ _ st (_, MF.FTrue) = pure st
addImp _ _ _ st (MF.FFalse, _) = pure st
addImp cfg ruleName dom st impC =
  let imp = norm impC
   in case dom of
        Assumptions
          | imp `elem` impA st -> pure st
          | otherwise -> do
            lg cfg [ruleName, "add to impA", strImp imp]
            let impA' = Set.insert imp (impA st)
            let impG' = Set.insert imp (impG st)
            pure $ st {impA = impA', impG = impG'}
        Guarantees
          | imp `elem` impG st -> pure st
          | otherwise -> do
            lg cfg [ruleName, "add to impG", strImp imp]
            let impG' = Set.insert imp (impG st)
            pure $ st {impG = impG'}
  where
    strImp = strP MF.toString MF.toString
    --
    norm =
      \case
        (MF.FTrue, MF.FOr [a, b])
          | MF.notTemporal a -> (MF.fnot a, b)
          | MF.notTemporal b -> (MF.fnot b, a)
          | otherwise -> (MF.FTrue, MF.FOr [a, b])
        imp -> imp

mapFs :: Domain -> State -> (Formula -> Formula) -> State
mapFs dom st mp =
  case dom of
    Assumptions -> st {fa = map mp (fa st)}
    Guarantees -> st {fg = map mp (fg st)}

addFacts :: [Term] -> State -> State
addFacts facts st = st {fg = map (MF.fpred True) facts ++ fg st}

newImps :: State -> State -> Set (Domain, Formula, Formula)
newImps stOld stNew =
  let diffD dom = Set.map (\(f, g) -> (dom, f, g)) $ impD dom stNew `Set.difference` impD dom stOld
   in diffD Assumptions `Set.union` diffD Guarantees

filterDom :: Domain -> Set (Domain, Formula, Formula) -> Set (Formula, Formula)
filterDom dom = Set.map (\(_, f, g) -> (f, g)) . Set.filter (\(d, _, _) -> d == dom)

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------
stateToString :: State -> String
stateToString st =
  "State {"
    ++ partL ea "ea"
    ++ partL fa "fa"
    ++ partL eg "eg"
    ++ partL fg "fg"
    ++ partS (impD Assumptions) "impA"
    ++ partS (impD Guarantees) "impG"
    ++ " }"
  where
    partL op opname = " " ++ opname ++ " = " ++ strL MF.toString (op st)
    partS op opname = " " ++ opname ++ " = " ++ strS (strP MF.toString MF.toString) (op st)
-------------------------------------------------------------------------------
