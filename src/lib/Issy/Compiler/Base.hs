---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler.Base
-- Description : Base components for the issy-format to llissy-format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module contains the base components for the issy-to-llissy compiler. This
-- includes error, position, and token handling. It also includes the representation
-- of the specification AST.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Compiler.Base
  ( PRes
  , perr
  , perrGen
  , Pos
  , initPos
  , nextSymbol
  , nextLine
  , posStr
  , Token(..)
  , token
  , AstSpec
  , AstDef(..)
  , AstIO(..)
  , AstSort(..)
  , AstWC(..)
  , AstLogicStm(..)
  , AstTF(..)
  , AstGameStm(..)
  , AstTerm(..)
  , AstAtom(..)
  , AstGround(..)
  , BOP(..)
  , UOP(..)
  ) where

---------------------------------------------------------------------------------------------------
-- Positions
---------------------------------------------------------------------------------------------------
-- | The position inside an input string. It is composed of the line number and
-- the position within this line. The count of both positions starts with one.
data Pos = Pos
  { lineNum :: Int
  -- ^ the line number, starting from one
  , pos :: Int
  -- ^ the character count within the line
  } deriving (Eq, Ord, Show)

-- | 'initPos' is the initial position
initPos :: Pos
initPos = Pos {lineNum = 1, pos = 1}

-- | 'nextSymbol' is the next position within the same line
-- (i.e. for the next non-newline character)
nextSymbol :: Pos -> Pos
nextSymbol p = p {pos = pos p + 1}

-- | 'nextLine' is the position of the next line
nextLine :: Pos -> Pos
nextLine p = Pos {lineNum = lineNum p + 1, pos = 1}

-- | 'posStr' prints the position as an easy to read and interpretable string
posStr :: Pos -> String
posStr p = "[" ++ show (lineNum p) ++ ":" ++ show (pos p) ++ "]"

---------------------------------------------------------------------------------------------------
-- Errors
---------------------------------------------------------------------------------------------------
-- | Many steps of the compiler will either return some value or an error with an error message.
-- 'PRes' allows to write the respective return type compactly and uniformly.
type PRes a = Either String a

-- | 'perr' creates a compiler error at a specific position
perr :: Pos -> String -> Either String a
perr p msg = Left $ "Compiler error at " ++ posStr p ++ " : " ++ msg

-- | 'perrGen' creates a generic compiler error without a position
perrGen :: String -> Either String a
perrGen = Left . ("Compiler error : " ++)

---------------------------------------------------------------------------------------------------
-- Tokens
---------------------------------------------------------------------------------------------------
-- | Represents a token while parsing. A token has a value (which is a string)
-- and a position for error tracking.
data Token = Token
  { tpos :: Pos
  -- ^ 'tpos' is the position of the token. For multi-character tokens, e.g. keywords,
  -- this should be the location of the first character in the token
  , tval :: String
  -- ^ 'tval' is the content of the token, i.e. a sub-string of the overall input
  -- that represents this token
  } deriving (Eq, Ord, Show)

-- | Creates a token. The position of the token should be the position of
-- the first character of content string.
token :: Pos -> String -> Token
token p s = Token {tpos = p, tval = s}

---------------------------------------------------------------------------------------------------
-- Abstract Syntax Tree
---------------------------------------------------------------------------------------------------
-- | Representation of the full AST of a issy-format specification
type AstSpec = [AstDef]

-- | The AST representation of a definition in an specification
data AstDef
  = AstVar Pos AstIO AstSort String
  -- ^ this is a input or state variable definition
  | AstLogic Pos [AstLogicStm]
  -- ^ this is the definition of logic specification,
  -- the interpretation is that the conjunction of assumptions
  -- implies the conjunction of assertions
  | AstGame Pos AstWC String [AstGameStm]
  -- ^ this is the definition of a game specification
  | AstMacro Pos String AstTerm
  -- ^ this is a macro definition
  deriving (Eq, Ord, Show)

-- | AST enum for input and states
data AstIO
  = AInput
  -- ^ indicates an input
  | AState
  -- ^ indicates a state
  deriving (Eq, Ord, Show)

-- | AST enum for sorts
data AstSort
  = ABool
  -- ^ indicates a boolean sort
  | AInt
  -- ^ indicates a integer sort
  | AReal
  -- ^ indicates a real-value sort
  deriving (Eq, Ord, Show)

-- | AST enum for game winning conditions
data AstWC
  = ASafety
  -- ^ safety winning condition
  | AReachability
  -- ^ reachability winning condition
  | ABuechi
  -- ^ Büchi winning condition
  | ACoBuechi
  -- ^ co-Büchi winning condition
  | AParityMaxOdd
  -- ^ parity (max odd) winning condition
  deriving (Eq, Ord, Show)

-- | DOCUMENT
data AstLogicStm
  = AstAssert Pos AstTF
  -- ^ DOCUMENT
  | AstAssume Pos AstTF
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
data AstTF
  = AFAtom Pos AstAtom
  -- ^ DOCUMENT
  | AFUexp Pos UOP AstTF
  -- ^ DOCUMENT
  | AFBexp Pos BOP AstTF AstTF
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
data AstGameStm
  = ALoc Pos String Integer AstTerm
  -- ^ DOCUMENT
  | ATrans Pos String String AstTerm
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
data AstTerm
  = ATAtom Pos AstAtom
  -- ^ DOCUMENT
  | ATBexp Pos BOP AstTerm AstTerm
  -- ^ DOCUMENT
  | ATUexp Pos UOP AstTerm
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
data AstAtom
  = AABool Pos Bool
  -- ^ DOCUMENT
  | AAGround Pos AstGround
  -- ^ DOCUMENT
  | AAVar Pos String
  -- ^ DOCUMENT
  | AAKeep Pos [String]
  -- ^ DOCUMENT
  | AAHavoc Pos [String]
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
data AstGround
  = AConstInt Pos Integer
  -- ^ DOCUMENT
  | AConstReal Pos Rational
  -- ^ DOCUMENT
  | AConstBool Pos Bool
  -- ^ DOCUMENT
  | AGVar Pos String
  -- ^ DOCUMENT
  | AGBexp Pos BOP AstGround AstGround
  -- ^ DOCUMENT
  | AGUexp Pos UOP AstGround
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
newtype BOP =
  BOP String
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)

-- | DOCUMENT
newtype UOP =
  UOP String
  -- ^ DOCUMENT
  deriving (Eq, Ord, Show)
---------------------------------------------------------------------------------------------------
