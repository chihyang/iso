module Data (module Data) where

-- Type
data BaseType =
  BTyUnit
  | BTyInt
  | BTyVar String
  | BTySum BaseType BaseType
  | BTyProd BaseType BaseType
  | BTyMu String BaseType
  deriving (Eq, Ord, Show)

data IsoType =
  ITyBase BaseType BaseType
  | ITyFun BaseType BaseType IsoType
  deriving (Eq, Ord, Show)

type ProgramType = Either BaseType IsoType

-- Syntax
data Value =
  ValUnit
  | ValInt Int
  | ValVar String
  | ValLInj Value
  | ValRInj Value
  | ValPair Value Value
  | ValAnn Value BaseType
  -- | ValFold Value
  deriving (Show)

data Exp =
  ExpVal Value
  | ExpLet Pattern Exp Exp
  deriving (Show)

data Pattern =
  PtSingleVar String
  | PtMultiVar [String]
  deriving (Show)

data Iso =
  IsoValue [Value] [Exp]
  | IsoVar String
  | IsoLam String BaseType BaseType Iso
  | IsoApp Iso Iso
  | IsoFix String Iso
  | IsoAnn Iso IsoType
  deriving (Show)

data Term =
  TmUnit
  | TmInt Int
  | TmVar String
  | TmLInj Term
  | TmRInj Term
  | TmPair Term Term
  | TmIsoApp Iso Term
  | TmLet Pattern Term Term
  | TmAnn Term BaseType
  -- | TmFold Term
  deriving (Show)

data Program =
  PgTm Term
  | PgIs Iso
  deriving (Show)

-- Value
data ProgramBaseValue =
  PBValUnit
  | PBValInt Int
  | PBValVar String
  | PBValLeft ProgramBaseValue
  | PBValRight ProgramBaseValue
  | PBValPair ProgramBaseValue ProgramBaseValue
  -- | PBValFold ProgramBaseValue
  deriving (Eq, Ord, Show)

data ProgramIsoValue =
  PIValBase [(ProgramBaseValue , ProgramBaseValue)] ValEnv
  | PIValLam String Iso ValEnv
  | PIValFix String Iso ValEnv
  deriving (Show)

data ProgramValue =
  PB ProgramBaseValue
  | PI ProgramIsoValue
  deriving (Show)

-- Value Environment
type ValEnv = [(String , ProgramValue)]
type TypEnv = [(String , ProgramType)]
