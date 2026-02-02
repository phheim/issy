---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Specification
-- Description : Data structure for mixed-formula-game specifications
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module provides the implementation of specifications that can be composed of multiple
-- RPLTL formulas and symbolic games.
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
  , specFromRPLTL
  , -- checking
    checkSpecification
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Prelude

import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.SymbolicArena as SG
import qualified Issy.Logic.Temporal as TL

---------------------------------------------------------------------------------------------------
-- | Represents a mixed-specification that can be composed of multiple RPLTL formulas and 
-- symbolic games. These sub-specifications are interpreted conjunctively. Note that all
-- sub-specifications need to range over the same set of variables (in the data structure, not
-- all variables need to necessarily appear in those). Also, at most one formula or game 
-- can be not safety.
data Specification = Specification
  { variables :: Variables
    -- ^ The shared variables of a specification
  , formulas :: [TL.Spec Term]
    -- ^ The formula sub-specifications of a specification
  , games :: [(SG.Arena, Objective)]
    -- ^ The game sub-specifications of a specification
  , hadNonSafety :: Bool
    -- ^ Indicates whether already one of the sub-specifications is
    -- not a safety one. If this flag is set, only safety sub-specifications 
    -- maybe be added to the whole specifications.
  } deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------------------------
-- | The empty specification (i.e. true) over a given set of variables
empty :: Variables -> Specification
empty vars = Specification {variables = vars, formulas = [], games = [], hadNonSafety = False}

-- | Adds a sub-formula-specification to the overall specification. This might fail
-- if the added sub-specification ranges over different variables then the overall
-- one or is non-safety while there is already a non-safety part present in the overall
-- specification.
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

-- | Adds a sub-game-specification to the overall specification. This might fail
-- if the added sub-specification ranges over different variables then the overall
-- one or is non-safety while there is already a non-safety part present in the overall
-- specification.
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

-- | Creates a specification from a single game-specification
specFromSymbolicGame :: SG.Arena -> Objective -> Specification
specFromSymbolicGame arena obj =
  case addGame (empty (SG.variables arena)) arena obj of
    Left err -> error $ "assert: found impossible error: " ++ err
    Right spec -> spec

-- | Creates a specification from a single game-specification
specFromRPLTL :: TL.Spec Term -> Specification
specFromRPLTL formula =
  case addFormula (empty (TL.variables formula)) formula of
    Left err -> error $ "assert: found impossible error: " ++ err
    Right spec -> spec

---------------------------------------------------------------------------------------------------
-- | Checks if a specification is consistent. At the moment this means checking that each
-- sub-game-specification is well-defined.
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
