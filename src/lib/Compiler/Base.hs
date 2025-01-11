{-# LANGUAGE LambdaCase #-}

module Compiler.Base where

--
-- Constants
--
isKeyword :: String -> Bool
isKeyword =
  flip
    elem
    [ "assume"
    , "assert"
    , "input"
    , "state"
    , "loc"
    , "from"
    , "with"
    , "game"
    , "formula"
    , "int"
    , "bool"
    , "real"
    , "def"
    , "F"
    , "X"
    , "G"
    , "U"
    , "W"
    , "R"
    , "Safety"
    , "Reachability"
    , "Buechi"
    , "CoBuechi"
    , "ParityMaxOdd"
    , "keep"
    , "havoc"
    ]

--
-- Error Handeling
--
type PRes a = Either String a

perr :: Pos -> String -> Either String a
perr p msg = Left $ "Compiler error [" ++ show (lineNum p) ++ ":" ++ show (pos p) ++ "] : " ++ msg

perrGen :: String -> Either String a
perrGen = Left . ("Compiler error : " ++)

--
-- Position Handeling
--
data Pos = Pos
  { lineNum :: Int
  , pos :: Int
  } deriving (Eq, Ord, Show)

initPos :: Pos
initPos = Pos {lineNum = 1, pos = 1}

nextSymbol :: Pos -> Pos
nextSymbol p = p {pos = pos p + 1}

nextLine :: Pos -> Pos
nextLine p = Pos {lineNum = lineNum p + 1, pos = 1}

--
-- Token
--
data Token = Token
  { tpos :: Pos
  , tval :: String
  } deriving (Eq, Ord, Show)

token :: Pos -> String -> Token
token p s = Token {tpos = p, tval = s}

--
-- AST
--
type AstSpec = [AstDef]

data AstDef
  = AstVar AstIO AstSort String
  | AstLogic [AstLogicStm]
  | AstGame AstWC String [AstGameStm]
  | AstDef String AstTerm
  deriving (Eq, Ord, Show)

data AstIO
  = AInput
  | AState
  deriving (Eq, Ord, Show)

data AstSort
  = ABool
  | AInt
  | AReal
  deriving (Eq, Ord, Show)

newtype AstWC =
  AstWC String
  deriving (Eq, Ord, Show)

data AstLogicStm
  = AstAssert AstTF
  | AstAssume AstTF
  deriving (Eq, Ord, Show)

data AstTF
  = AFAtom AstAtom
  | AFUexp UOP AstTF
  | AFBexp BOP AstTF AstTF
  deriving (Eq, Ord, Show)

data AstGameStm
  = ALoc String Integer AstTerm
  | ATrans String String AstTerm
  deriving (Eq, Ord, Show)

data AstTerm
  = ATAtom AstAtom
  | ATBexp BOP AstTerm AstTerm
  | ATUexp UOP AstTerm
  deriving (Eq, Ord, Show)

data AstAtom
  = AABool Bool
  | AAGround AstGround
  | AAVar String
  deriving (Eq, Ord, Show)

data AstGround
  = AConstInt Integer
  | AConstReal Rational
  | AGVar String
  | AGBexp BOP AstGround AstGround
  | AGUexp UOP AstGround
  deriving (Eq, Ord, Show)

newtype BOP =
  BOP String
  deriving (Eq, Ord, Show)

newtype UOP =
  UOP String
  deriving (Eq, Ord, Show)

termToTF :: AstTerm -> AstTF
termToTF =
  \case
    ATAtom atom -> AFAtom atom
    ATUexp op t -> AFUexp op (termToTF t)
    ATBexp op t1 t2 -> AFBexp op (termToTF t1) (termToTF t2)
