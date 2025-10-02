---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Specification
-- Description : Data structure for mixed-formula-game specifications
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Specification
  ( Specification
  , -- access
    variables
  , formulas
  , games
  , -- construction
    empty
  , addFormula
  , addGame
  , specFromSymbolicGame
  , -- checking
    checkSpecification
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Prelude

import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.SymbolicArena as SG
import qualified Issy.Logic.Temporal as TL

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
-- Invariant: only one non-safety part and all the same variables
data Specification = Specification
  { variables :: Variables
  , formulas :: [TL.Spec Term]
  , games :: [(SG.Arena, Objective)]
  , hadNonSafety :: Bool
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
empty :: Variables -> Specification
empty vars = Specification {variables = vars, formulas = [], games = [], hadNonSafety = False}

---------------------------------------------------------------------------------------------------
addFormula :: Specification -> TL.Spec Term -> Either String Specification
addFormula spec formula
  | variables spec /= TL.variables formula =
    error "assert: tried to add formula with different variables"
  | hadNonSafety spec && not (TL.isSafety formula) = Left "Found second non-safety formula"
  | otherwise =
    Right
      $ spec
          { formulas = formulas spec ++ [formula]
          , hadNonSafety = hadNonSafety spec || not (TL.isSafety formula)
          }

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
addGame :: Specification -> SG.Arena -> Objective -> Either String Specification
addGame spec arena obj
  | variables spec /= SG.variables arena =
    error "assert: tried to add formula with different variables"
  | hadNonSafety spec && not (Obj.isSafety obj) = Left "Found second non-safety game"
  | otherwise =
    Right
      $ spec
          { games = games spec ++ [(arena, obj)]
          , hadNonSafety = hadNonSafety spec || not (Obj.isSafety obj)
          }

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
checkSpecification :: Config -> Specification -> IO (Either String ())
checkSpecification conf = go (1 :: Int) . games
  where
    go _ [] = pure $ Right ()
    go n (g:gr) = do
      check <- SG.check conf (fst g)
      case check of
        Nothing -> go (n + 1) gr
        Just err -> pure $ Left $ "game number " ++ show n ++ " is invalid: " ++ err

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
specFromSymbolicGame :: SG.Arena -> Objective -> Specification
specFromSymbolicGame arena obj =
  case addGame (empty (SG.variables arena)) arena obj of
    Left err -> error $ "assert: found impossible error: " ++ err
    Right spec -> spec
---------------------------------------------------------------------------------------------------
