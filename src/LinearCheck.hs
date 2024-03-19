module LinearCheck (linearCheck, linearCheckEnv) where

import Syntax

type LinearEnv = [(String , Int)]
type Result a = Either String a

linearCheck :: Program -> Result Program
linearCheck pg = linearCheckEnv [] pg

linearCheckEnv :: LinearEnv -> Program -> Result Program
linearCheckEnv env (PgTm tm) = do
  env' <- lcTm env tm
  if sameVars env' env
    then return (PgTm tm)
    else Left "Impossible case in linear check: an environment is not restored!"
linearCheckEnv env (PgIs iso) = do
  env' <- lcIso [] iso
  if sameVars env' env
    then return (PgIs iso)
    else Left "Impossible case in linear check: an environment is not restored!"

sameVars :: LinearEnv -> LinearEnv -> Bool
sameVars env env' = map fst env == map fst env'

{---------- Linear checking for Terms ----------}
lcTm :: LinearEnv -> Term -> Result LinearEnv
lcTm env TmUnit = return env
lcTm env (TmInt _) = return env
lcTm env (TmVar var) = increEnv env var
lcTm env (TmLInj tm) = lcTm env tm
lcTm env (TmRInj tm) = lcTm env tm
lcTm env (TmPair l r) = do
  env' <- lcTm env l
  lcTm env' r
lcTm env (TmIsoApp iso tm) = do
  env' <- lcIso env iso
  lcTm env' tm
lcTm env (TmLet pat rhs body) = do
  env' <- lcTm env rhs
  env'' <- extendPat env' pat
  env''' <- lcTm env'' body
  dropPat env''' pat
lcTm env (TmAnn tm _) = lcTm env tm

{---------- Linear checking for Isos ----------}
lcIso :: LinearEnv -> Iso -> Result LinearEnv
lcIso env (IsoValue pairs) = lcIsoPairs env pairs
lcIso env (IsoVar _) = return env
-- iso var binding is ignored
lcIso env (IsoLam _ _ _ body) = lcIso env body
lcIso env (IsoApp rator rand) = do
  env' <- lcIso env rand
  lcIso env' rator
lcIso _ (IsoFix _ _) = error $ "IsoFix is not supported yet!"
lcIso env (IsoAnn iso _) = lcIso env iso

lcIsoPairs :: LinearEnv -> [(Value, Exp)] -> Result LinearEnv
lcIsoPairs env [] = return env
lcIsoPairs env (hd:tl) = do
  env' <- lcIsoPair env hd
  lcIsoPairs env' tl

lcIsoPair :: LinearEnv -> (Value, Exp) -> Result LinearEnv
lcIsoPair env (v, e) = do
  let vars = lcVal env v
  env' <- extendPat env (PtMultiVar vars)
  lcExp env' e

{---------- Linear type checking for Values -----------}
lcVal :: LinearEnv -> Value -> [String]
lcVal _ ValUnit = []
lcVal _ (ValInt _) = []
lcVal _ (ValVar var) = [var]
lcVal env (ValLInj v) = lcVal env v
lcVal env (ValRInj v) = lcVal env v
lcVal env (ValPair l r) = lVars ++ rVars where
  lVars = lcVal env l
  rVars = lcVal env r
lcVal env (ValAnn v _) = lcVal env v

{---------- Linear type checking for Exps -----------}
lcExp :: LinearEnv -> Exp -> Result LinearEnv
lcExp env (ExpVal val) = lcValNoPat env val
lcExp env (ExpLet pat iso pat' body) = do
  env' <- lcIso env iso
  env'' <- lcRhsPat env' pat'
  env''' <- extendPat env'' pat
  env'''' <- lcExp env''' body
  dropPat env'''' pat

lcRhsPat :: LinearEnv -> Pattern -> Result LinearEnv
lcRhsPat env (PtSingleVar var) = increEnv env var
lcRhsPat env (PtMultiVar []) = return env
lcRhsPat env (PtMultiVar (var:vars)) = do
  env' <- increEnv env var
  lcRhsPat env' (PtMultiVar vars)

{-- Linear type checking for Values (Non-pattern) --}
lcValNoPat :: LinearEnv -> Value -> Result LinearEnv
lcValNoPat env ValUnit = return env
lcValNoPat env (ValInt _) = return env
lcValNoPat env (ValVar var) = increEnv env var
lcValNoPat env (ValLInj v) = lcValNoPat env v
lcValNoPat env (ValRInj v) = lcValNoPat env v
lcValNoPat env (ValPair l r) = do
  env' <- lcValNoPat env l
  lcValNoPat env' r
lcValNoPat env (ValAnn v _) = lcValNoPat env v

{-- Helper functions --}
increEnv :: LinearEnv -> String -> Result LinearEnv
increEnv [] var = Left $ show var ++ " not found!"
increEnv ((var',n):tl) var
  | var' == var =
      if n > 0
      then Left $ "Variable " ++ show var ++ " is used more than once!"
      else return ((var', (n + 1)):tl)
increEnv ((var',n):tl) var = do
  env' <- increEnv tl var
  return $ (var',n):env'

extendPat :: LinearEnv -> Pattern -> Result LinearEnv
extendPat env (PtSingleVar var) = return $ (var, 0):env
extendPat env (PtMultiVar vars) = return $ (map (\x -> (x , 0)) vars) ++ env

dropPat :: LinearEnv -> Pattern -> Result LinearEnv
dropPat (_:tl) (PtSingleVar _) = return tl
dropPat env (PtMultiVar []) = return env
dropPat (_:tl) (PtMultiVar (_:vars)) = dropPat tl (PtMultiVar vars)
dropPat env pat = Left $ "Environment " ++ show env ++ " doesn't have enough variables for" ++ show pat ++ "!"
