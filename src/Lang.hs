module Lang where

--import qualified Data.ByteString as B
import qualified Data.Map as M
import Control.Applicative ( Alternative((<|>)) )

type Name = String

-- Statics
data Type = TyUnit | TyInt | TyVar Name | TySum Type Type
  | TyProd Type Type | TyMu Name Type
  -- Iso Types
  | TyIsoZ Type Type | TyIsoS Type Type Type
  deriving (Eq, Show)

data Term = TmUnit | TmInt Int
  | TmInl Term | TmInr Term | TmCons Term Term | TmFold Term
  | TmVar Name | TmApp Term Term | TmLet Term Term Term
  -- Extra Constructs for parsing/typechecking
  | TmIso Iso | TmAnn Term Type | TmVarList [Name]
  deriving (Eq, Show)

data Iso = IsoClauses [(Term, Term)]
  | IsoFix Name Iso | IsoLam Name Iso
  | IsoVar Name | IsoApp Iso Iso
  deriving (Eq, Show)

-- Dynamics
data Stmt =
  StmtDef Name Term
  | StmtTerm Term
  deriving (Eq, Show)

newtype Prog = Prog { unProg :: [Stmt] } 

type Env = M.Map Name Return

data Return = RUnit | RInt Int
  | RInl Return | RInr Return
  | RCons Return Return | RFold Return
  | RClo Iso Env
  deriving (Eq, Show)


eval :: Term -> Env -> Maybe Return
eval TmUnit             _   = pure RUnit
eval (TmInt n)          _   = pure $ RInt n
eval (TmInl a)          env = RInl <$> eval a env
eval (TmInr b)          env = RInr <$> eval b env
eval (TmCons a b)       env = RCons <$> eval a env <*> eval b env
eval (TmFold a)         env = RFold <$> eval a env
eval (TmVar x)          env = applyEnv env x
eval (TmApp f a)        env = do
  arg <- eval a env
  fun <- eval f env
  case fun of
    RClo iso env' -> applyIso env' iso arg  
    _             -> error $ "eval: cannot apply non-iso function " ++ show iso
eval (TmIso f)      env = pure $ RClo f env
eval (TmAnn a _)        env = eval a env
eval (TmLet l r body)   env = do
  r'   <- eval r env
  env' <- match env l r'
  eval body env'

match :: Env -> Term -> Return -> Maybe Env
match env TmUnit       RUnit          = Just env
match env (TmInt n)    (RInt m)       = if n == m then Just env else Nothing
match env (TmInl a)    (RInl a')      = match env a a'
match env (TmInr b)    (RInr b')      = match env b b'
match env (TmCons a b) (RCons a' b') = do
  env' <- match env a a'
  match env' b b'
match env (TmFold a)   (RFold a')    = match env a a'
match env (TmVar x)    r             = pure $ extendEnv env x r
match _   _            _             = Nothing

initEnv :: Env
initEnv = M.empty

extendEnv :: Env -> Name -> Return -> Env
extendEnv env x v = M.insert x v env

applyEnv :: Env -> Name -> Maybe Return
applyEnv env x = M.lookup x env

applyClo :: Return -> Return -> Maybe Return
applyClo (RClo f env) arg = applyIso env f arg
applyClo r            _   = error $ "applyClo: Not a closure " ++ show r

applyIso :: Env -> Iso -> Return -> Maybe Return
applyIso env iso arg = case iso of
  IsoClauses [] -> error msg 
    where
      msg = "Cannot find a match for " ++ show arg
  IsoClauses ((l, r) : cs) -> tryFirst <|> tryRest
    where
      tryFirst = do
        env' <- match env l arg
        eval r env'
      tryRest = applyIso env (IsoClauses cs) arg
  IsoFix phi body ->
    let env' = extendEnv env phi (RClo iso env) 
     in applyIso env' body arg
  IsoLam phi body ->
    let env' = extendEnv env phi arg 
     in pure $ RClo body env'
  IsoVar var -> do
    f <- applyEnv env var
    applyClo f arg
  IsoApp f g -> do
    g' <- eval (TmIso g) env
    f' <- applyIso env f g'
    case f' of
      RClo h env' -> applyIso env' h arg
      _           -> error $ "applyIso: Unexpected result evaluating " ++ show iso
