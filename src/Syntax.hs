module Syntax (module Syntax, module C) where

import Data.Complex as C
import qualified Data.List as L
import qualified Data.Map.Strict as Map
import Data.Tuple (swap)

type Scale = Complex Double

-- Type
data BaseType =
  BTyUnit
  | BTyInt
  | BTyList BaseType
  | BTyVar String
  | BTySum BaseType BaseType
  | BTyProd BaseType BaseType
  | BTyMu String BaseType
  deriving (Eq, Ord)
instance Show BaseType where
  show BTyUnit = "Unit"
  show BTyInt = "Int"
  show (BTyList t) = "[" ++ show t ++ "]"
  show (BTyVar var) = var
  show (BTySum lt rt) = "(" ++ show lt ++ " + " ++ show rt ++ ")"
  show (BTyProd lt rt) = "(" ++ show lt ++ " x " ++ show rt ++ ")"
  show (BTyMu var bodyT) = "Mu " ++ var ++ ". " ++ show bodyT

data IsoType =
  ITyBase BaseType BaseType
  | ITyFun BaseType BaseType IsoType
  deriving (Eq, Ord)
instance Show IsoType where
  show (ITyBase lt rt) = show lt ++ " <-> " ++ show rt
  show (ITyFun lt rt bodyT) = "(" ++ show lt ++ " <-> " ++ show rt ++ ") -> " ++ show bodyT

type ProgramType = Either BaseType IsoType

-- Syntax
data Value =
  ValUnit
  | ValInt Int
  | ValEmpty
  | ValCons Value Value
  | ValVar String
  | ValLInj Value
  | ValRInj Value
  | ValPair Value Value
  | ValAnn Value BaseType
  -- | ValFold Value
  deriving (Eq, Ord)
instance Show Value where
  show ValUnit = "unit"
  show (ValInt n) = show n
  show ValEmpty = "[]"
  show (ValCons v1 ValEmpty) = "[" ++ show v1 ++ "]"
  show (ValCons v1 v2) = show v1 ++ ":" ++ show v2
  show (ValVar var) = var
  show (ValLInj v) = "left " ++ show v
  show (ValRInj v) = "right " ++ show v
  show (ValPair l r) = "<" ++ show l ++ ", " ++ show r ++ ">"
  show (ValAnn v _) = show v

data Exp =
  ExpVal Value
  | ExpLet Pattern Iso Pattern Exp
  | ExpScale Scale Exp
  | ExpPlus [Exp]
  deriving (Eq)
instance Show Exp where
  show (ExpVal v) = show v
  show (ExpLet pat iso pat' body) =
    "let " ++ show pat ++ " = " ++ show iso ++ " " ++ show pat' ++ " in " ++ show body
  show (ExpPlus es) = "(" ++ L.intercalate " + " (map show es) ++ ")"
  show (ExpScale c e) = "(" ++ show c ++ ") * " ++ show e
instance Ord Exp where
  compare (ExpVal v) (ExpVal v') = compare v v'
  compare (ExpVal _) _ = LT
  compare (ExpLet _ _ _ _) (ExpVal _) = GT
  compare (ExpLet vars iso pat body) (ExpLet vars' iso' pat' body')
    | cv && ci && cp && body == body' = EQ
    | cv && ci && cp = compare body body'
    | cv && ci = compare pat pat'
    | cv = compare iso iso'
    | vars < vars' = LT
    | vars > vars' = GT where
        cv = vars == vars'
        ci = iso == iso'
        cp = pat == pat'
  compare (ExpLet _ _ _ _) _ = LT
  compare (ExpScale _ _) (ExpVal _) = GT
  compare (ExpScale _ _) (ExpLet _ _ _ _) = GT
  compare (ExpScale _ e) (ExpScale _ e') = compare e e'
  compare (ExpScale _ _) _ = LT
  compare (ExpPlus _) (ExpVal _) = GT
  compare (ExpPlus _) (ExpLet _ _ _ _) = GT
  compare (ExpPlus _) (ExpScale _ _) = GT
  compare (ExpPlus []) (ExpPlus []) = EQ
  compare (ExpPlus (_:_)) (ExpPlus []) = GT
  compare (ExpPlus []) (ExpPlus (_:_)) = LT
  compare (ExpPlus (e1:es1)) (ExpPlus (e2:es2))
    | compare e1 e2 == LT = LT
    | compare e1 e2 == EQ = compare (ExpPlus es1) (ExpPlus es2)
    | otherwise = GT

data Pattern =
  PtSingleVar String
  | PtMultiVar [String]
  deriving (Eq, Ord)
instance Show Pattern where
  show (PtSingleVar var) = var
  show (PtMultiVar vars) = show "<" ++ (L.intercalate ", " vars) ++ show ">"

data Iso =
  IsoValue [(Value, Exp)]
  | IsoVar String
  | IsoLam String BaseType BaseType Iso
  | IsoApp Iso Iso
  | IsoFix String BaseType BaseType Iso
  | IsoAnn Iso IsoType
  deriving (Eq, Ord)
instance Show Iso where
  show (IsoValue clauses) =
    "{" ++ (L.intercalate "; " (map (\(f,s) -> (show f) ++ " <-> " ++ (show s)) clauses)) ++ "}"
  show (IsoVar var) = var
  show (IsoLam var lhs rhs body) =
    "\\" ++
    var ++ " :: (" ++ show lhs ++ " <-> " ++ show rhs ++ ")" ++
    " ->" ++ show body
  show (IsoApp rator rand) = "[" ++ show rator ++ " " ++ show rand ++ "]"
  show (IsoFix var lhs rhs iso) =
    "fix " ++
    var ++ " :: (" ++ show lhs ++ " <-> " ++ show rhs ++ ")" ++
    " ->" ++ show iso
  show (IsoAnn iso _) = show iso

data Term =
  TmUnit
  | TmInt Int
  | TmEmpty
  | TmCons Term Term
  | TmVar String
  | TmLInj Term
  | TmRInj Term
  | TmPair Term Term
  | TmIsoApp Iso Term
  | TmLet Pattern Term Term
  | TmAnn Term BaseType
  -- | TmFold Term
  deriving (Eq, Ord)
instance Show Term where
  show TmUnit = "unit"
  show (TmInt n) = show n
  show TmEmpty = "[]"
  show (TmCons v1 TmEmpty) = "[" ++ show v1 ++ "]"
  show (TmCons v1 v2) = show v1 ++ ":" ++ show v2
  show (TmVar var) = var
  show (TmLInj v) = "left " ++ show v
  show (TmRInj v) = "right " ++ show v
  show (TmPair l r) = "<" ++ show l ++ ", " ++ show r ++ ">"
  show (TmIsoApp iso tm) = "(" ++ show iso ++ " " ++ show tm ++ ")"
  show (TmLet pat rhs body) =
    "let " ++ show pat ++ " = " ++ show rhs ++ "in " ++ show body
  show (TmAnn v _) = show v

data Program =
  PgTm Term
  | PgIs Iso
  deriving (Eq, Ord)
instance Show Program where
  show (PgTm tm) = show tm
  show (PgIs iso) = show iso

-- Value
data ProgramBaseValue =
  PBValUnit
  | PBValInt Int
  | PBValEmpty
  | PBValCons ProgramBaseValue ProgramBaseValue
  | PBValVar String
  | PBValLeft ProgramBaseValue
  | PBValRight ProgramBaseValue
  | PBValPair ProgramBaseValue ProgramBaseValue
  -- | PBValFold ProgramBaseValue
  deriving (Eq, Ord)
instance Show ProgramBaseValue where
  show PBValUnit = "unit"
  show (PBValInt n) = show n
  show PBValEmpty = "[]"
  show (PBValCons v PBValEmpty) = "[" ++ show v ++"]"
  show (PBValCons v vs) = "(" ++ show v ++ ":" ++ show vs ++ ")"
  show (PBValVar var) = var
  show (PBValLeft v) = "left " ++ show v
  show (PBValRight v) = "right " ++ show v
  show (PBValPair l r) = "<" ++ show l ++ ", " ++ show r ++ ">"

data ProgramIsoValue =
  PIValBase [(ProgramBaseValue , Exp)] ValEnv
  | PIValLam String Iso ValEnv
  deriving (Eq)
instance Show ProgramIsoValue where
  show (PIValBase pairs _) =
    "{" ++ (L.intercalate "; " (map (\(f,s) -> (show f) ++ " <-> " ++ (show s)) pairs)) ++ "}"
  show (PIValLam var iso _) = "\\" ++ var ++ " -> " ++ show iso

data ProgramValue =
  PB ProgramBaseValue
  | PI ProgramIsoValue
  | PQ EntangledValue
  deriving (Eq)
instance Show ProgramValue where
  show (PB v) = show v
  show (PI i) = show i
  show (PQ []) = ""
  show (PQ [(s,v)]) = show s ++ " * " ++ show v
  show (PQ ((s,v):vs)) = show s ++ " * " ++ show v ++ " + " ++ show (PQ vs)

{---------- Operations over entangled values ----------}
distrib1 :: (ProgramBaseValue -> ProgramBaseValue) -> EntangledValue -> EntangledValue
distrib1 f vs = [(fst v, f $ snd v) | v <- vs]

distrib2 :: (ProgramBaseValue -> ProgramBaseValue -> ProgramBaseValue) -> EntangledValue -> EntangledValue -> EntangledValue
distrib2 f vs1 vs2 = [(fst v1 * fst v2, f (snd v1) (snd v2)) | v1 <- vs1, v2 <- vs2]

toTable :: EntangledValue -> Map.Map ProgramBaseValue Scale
toTable vs = foldr f Map.empty vs where
  f (s, v) acc = if Map.member v acc then Map.adjust (+ s) v acc else Map.insert v s acc

mergeEnt :: EntangledValue -> EntangledValue -> EntangledValue
mergeEnt vs1 vs2 = L.map swap $ Map.toList $ toTable (vs1 ++ vs2)

scaleEnt :: Scale -> EntangledValue -> EntangledValue
scaleEnt s vs = map (\v -> (s * fst v, snd v)) vs

-- Value Environment
data ValEnv =
  EmptyVEnv
  | ExtendIsoVEnv String ProgramIsoValue ValEnv
  | ExtendBaseVEnv String EntangledValue ValEnv
  | ExtendIsoRecEnv [String] [Iso] ValEnv
  deriving (Eq, Show)

type TypEnv = [(String , ProgramType)]
type LinearEnv = [(String , Int)]
type Result a = Either String a
type EntangledValue = [(Scale, ProgramBaseValue)]
type Declaration = Either IsoType Iso
type Declarations = [(String, Either IsoType Iso)]
type Definitions = [(String, Iso)]

reportErr :: String -> String -> Result a
reportErr tag msg = Left $ tag ++ msg
