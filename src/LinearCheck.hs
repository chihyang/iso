{-# LANGUAGE TupleSections #-}
module LinearCheck (linearCheck, linearCheckEnv, linearCheckDefsPg) where

import Data.Foldable
import Syntax
import qualified Data.Set as Set
import Debug.Trace (trace)

moduleName :: String
moduleName = "Linear Check: "

linearCheckDefsPg :: (Definitions, Program) -> Result (Definitions, Program)
-- linearCheckDefsPg (defs, pg) | trace ("linearCheckDefsPg " ++ show defs ++ " " ++ show pg) False = undefined
linearCheckDefsPg (defs, pg) = do
  defs' <- lcDefs defs
  pg' <- linearCheck pg
  return (defs', pg')

lcDefs :: Definitions -> Result Definitions
lcDefs [] = return []
lcDefs ((var,iso):defs) = do
  defs' <- lcDefs defs
  _ <- lcIso [] iso
  return ((var,iso):defs')

linearCheck :: Program -> Result Program
linearCheck = linearCheckEnv []

linearCheckEnv :: LinearEnv -> Program -> Result Program
linearCheckEnv env (PgTm tm) = do
  env' <- lcTm env tm
  if sameVars env' env
    then return (PgTm tm)
    else Left $ moduleName ++ "Impossible case in linear check: an environment is not restored!"
linearCheckEnv env (PgIs iso) = do
  env' <- lcIso env iso
  if sameVars env' env
    then return (PgIs iso)
    else Left $ moduleName ++ "Impossible case in linear check: an environment is not restored!"

sameVars :: LinearEnv -> LinearEnv -> Bool
sameVars env env' = map fst env == map fst env'

{---------- Linear checking for Terms ----------}
lcTm :: LinearEnv -> Term -> Result LinearEnv
lcTm env TmUnit = return env
lcTm env (TmInt _) = return env
lcTm env TmEmpty = return env
lcTm env (TmCons v vs) = do
  env' <- lcTm env v
  lcTm env' vs
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
lcIso env (IsoFix _ _ _ body) = lcIso env body
lcIso env (IsoAnn iso _) = lcIso env iso

lcIsoPairs :: LinearEnv -> [(Value, Exp)] -> Result LinearEnv
lcIsoPairs = foldlM lcIsoPair

lcIsoPair :: LinearEnv -> (Value, Exp) -> Result LinearEnv
lcIsoPair env (v, e) = do
  let vars = lcVal env v
  env' <- extendPat env (PtMultiVar vars)
  env'' <- lcExp env' e
  dropPat env'' (PtMultiVar vars)

{---------- Linear type checking for Values -----------}
lcVal :: LinearEnv -> Value -> [String]
lcVal _ ValUnit = []
lcVal _ (ValInt _) = []
lcVal env (ValSuc v) = lcVal env v
lcVal _ ValEmpty = []
lcVal env (ValCons v vs) = vars ++ vars' where
  vars = lcVal env v
  vars' = lcVal env vs
lcVal _ (ValVar var) = [var]
lcVal env (ValLInj v) = lcVal env v
lcVal env (ValRInj v) = lcVal env v
lcVal env (ValPair l r) = lVars ++ rVars where
  lVars = lcVal env l
  rVars = lcVal env r
lcVal env (ValAnn v _) = lcVal env v

{---------- Linear type checking for Exps -----------}
lcExp :: LinearEnv -> Exp -> Result LinearEnv
-- lcExp env e | trace ("lcExp " ++ show env ++ " " ++ show e) False = undefined
lcExp env (ExpVal val) = lcValNoPat env val
lcExp env (ExpLet pat iso pat' body) = do
  env' <- lcIso env iso
  env'' <- lcRhsPat env' pat'
  env''' <- extendPat env'' pat
  env'''' <- lcExp env''' body
  dropPat env'''' pat
lcExp env (ExpScale _ e) = lcExp env e
lcExp env (ExpPlus []) = return env
lcExp env (ExpPlus (e:es)) = do
  _ <- lcExp env e
  -- every sum is checked separately
  lcExp env (ExpPlus es)

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
lcValNoPat env (ValSuc v) = lcValNoPat env v
lcValNoPat env ValEmpty = return env
lcValNoPat env (ValCons v vs) = do
  env' <- lcValNoPat env v
  lcValNoPat env' vs
lcValNoPat env (ValVar var) = increEnv env var
lcValNoPat env (ValLInj v) = lcValNoPat env v
lcValNoPat env (ValRInj v) = lcValNoPat env v
lcValNoPat env (ValPair l r) = do
  env' <- lcValNoPat env l
  lcValNoPat env' r
lcValNoPat env (ValAnn v _) = lcValNoPat env v

{-- Helper functions --}
increEnv :: LinearEnv -> String -> Result LinearEnv
increEnv [] var = Left $ moduleName ++ show var ++ " not found!"
increEnv ((var',n):tl) var
  | var' == var =
      if n > 0
      then Left $ moduleName ++ "Variable " ++ show var ++ " is used more than once!"
      else return ((var', n + 1):tl)
increEnv ((var',n):tl) var = do
  env' <- increEnv tl var
  return $ (var',n):env'

extendPat :: LinearEnv -> Pattern -> Result LinearEnv
extendPat env (PtSingleVar var) = return $ (var, 0):env
extendPat env (PtMultiVar vars)
  | Set.size (Set.fromList vars) == length vars =
    return $ map (,0) vars ++ env
  | otherwise = Left $ "patterns have duplicate variables: " ++ show vars

dropPat :: LinearEnv -> Pattern -> Result LinearEnv
dropPat (_:tl) (PtSingleVar _) = return tl
dropPat env (PtMultiVar []) = return env
dropPat (_:tl) (PtMultiVar (_:vars)) = dropPat tl (PtMultiVar vars)
dropPat env pat = Left $ moduleName ++ "Environment " ++ show env ++ " doesn't have enough variables for" ++ show pat ++ "!"
