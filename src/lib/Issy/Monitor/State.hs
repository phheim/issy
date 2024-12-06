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

import Data.List (partition)

-------------------------------------------------------------------------------
import Data.Set (Set, difference, union)
import qualified Data.Set as Set (empty, filter, insert, map, toList)

-------------------------------------------------------------------------------
import Issy.Config (Config)
import Issy.Logic.FOL
import Issy.Monitor.Formula
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
falseSt = State {ea = [], fa = [], eg = [FFalse], fg = [FFalse], impA = Set.empty, impG = Set.empty}

trueSt :: State
trueSt = State {ea = [FFalse], fa = [FFalse], eg = [], fg = [], impA = Set.empty, impG = Set.empty}

genericNormSt :: ([Formula] -> [Formula]) -> State -> State
genericNormSt norm st =
  let ea' = norm (ea st)
      fa' = norm (fa st)
      eg' = norm (eg st)
      fg' = norm (fg st)
   in if ea' == [FFalse] || fa' == [FFalse] || null (fg' ++ eg')
        then trueSt
        else if fg' == [FFalse] || eg' == [FFalse]
               then if null (fa' ++ ea')
                      then falseSt
                      else falseSt {ea = ea', fa = fa', impA = impA st}
               else st {ea = ea', fa = fa', eg = eg', fg = fg'}

normSt :: State -> State
normSt = genericNormSt $ normAnd . map toplevelCNF

simpleNormSt :: State -> State
simpleNormSt = genericNormSt normAndLight

isSafeSt :: State -> Bool
isSafeSt st =
  all notTemporal (ea st) && all notTemporal (fa st) && all isSafe (eg st) && all isSafe (fg st)

isFalse :: State -> Bool
isFalse st = null (ea st ++ fa st) && (FFalse `elem` (eg st ++ fg st))

isTrue :: State -> Bool
isTrue st = null (eg st ++ fg st) || (FFalse `elem` ea st) || (FFalse `elem` fa st)

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
replaceSt asg = mapES (simpleNormSt . mapFormulas (replaceT asg))

replacesSt :: [(Term, Bool)] -> ExpansionState -> ExpansionState
replacesSt asgs =
  mapES $ \st -> simpleNormSt $ foldl (\st asg -> mapFormulas (replaceT asg) st) st asgs

stateFormulas :: State -> [Formula]
stateFormulas st = concat [ea st, fa st, eg st, fg st]

pickFreeSt :: ExpansionState -> Maybe Term
pickFreeSt (ExpansionState st) =
  case concatMap currentTerms (stateFormulas st) of
    [] -> Nothing
    (term, _):_ -> Just term

pickUpdSt :: ExpansionState -> Maybe (Symbol, Term)
pickUpdSt (ExpansionState st) =
  case concatMap currentUpdates (stateFormulas st) of
    [] -> Nothing
    upd:_ -> Just upd

setUpdSt :: (Symbol, Term) -> Bool -> ExpansionState -> ExpansionState
setUpdSt upd pol = mapES $ simpleNormSt . mapFormulas (replaceU upd pol)

expandSt :: ExpansionState -> ExpansionState
expandSt = mapES $ mapFormulas expand

shiftSt :: ExpansionState -> ExpansionState
shiftSt = mapES $ mapFormulas shift

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

--TODO: refine? Add assumptions stuff to guaratnees?
current :: Domain -> State -> [Formula]
current dom = go . eset dom
  where
    go =
      \case
        [] -> []
        FGlobally f:fr
          | notTemporal f -> f : go fr
          | otherwise -> go fr
        f:fr
          | notTemporal f -> f : go fr
          | otherwise -> go fr

dedInv :: Domain -> State -> [Formula]
dedInv dom =
  filter notTemporal . map (\(prem, conc) -> for [fnot prem, conc]) . Set.toList . impD dom

weaks :: Domain -> State -> [(Formula, Formula)]
weaks dom = go . fset dom
  where
    go =
      \case
        [] -> []
        FWeak f g:fr
          | notTemporal f && notTemporal g -> (f, g) : go fr
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
    FGlobally f -> notTemporal f
    FWeak f g -> notTemporal f && notTemporal g
    f -> notTemporal f

invalidate :: Domain -> State -> State
invalidate Assumptions _ = trueSt
invalidate Guarantees st = st {eg = [FFalse], fg = [FFalse], impG = Set.empty}

addImp :: Config -> String -> Domain -> State -> (Formula, Formula) -> IO State
addImp _ _ _ st (_, FTrue) = pure st
addImp _ _ _ st (FFalse, _) = pure st
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
    strImp = strP formulaToString formulaToString
    --
    norm =
      \case
        (FTrue, FOr [a, b])
          | notTemporal a -> (fnot a, b)
          | notTemporal b -> (fnot b, a)
          | otherwise -> (FTrue, FOr [a, b])
        imp -> imp

mapFs :: Domain -> State -> (Formula -> Formula) -> State
mapFs dom st mp =
  case dom of
    Assumptions -> st {fa = map mp (fa st)}
    Guarantees -> st {fg = map mp (fg st)}

addFacts :: [Term] -> State -> State
addFacts facts st = st {fg = map (fpred True) facts ++ fg st}

newImps :: State -> State -> Set (Domain, Formula, Formula)
newImps stOld stNew =
  let diffD dom = Set.map (\(f, g) -> (dom, f, g)) $ impD dom stNew `difference` impD dom stOld
   in diffD Assumptions `union` diffD Guarantees

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
    partL op opname = " " ++ opname ++ " = " ++ strL formulaToString (op st)
    partS op opname = " " ++ opname ++ " = " ++ strS (strP formulaToString formulaToString) (op st)
-------------------------------------------------------------------------------
