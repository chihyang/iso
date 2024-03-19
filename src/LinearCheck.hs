module LinearCheck (linearCheck) where

import Syntax

type LinearEnv = [(String , Int)]

linearCheck :: LinearEnv -> Program -> LinearEnv
linearCheck env (PgTm tm) = linearCheckTm env tm
linearCheck env (PgIs iso) = linearCheckIso env iso

{---------- Linear checking for Terms ----------}
linearCheckTm :: LinearEnv -> Term -> LinearEnv
linearCheckTm env TmUnit = env
linearCheckTm env (TmInt _) = env
linearCheckTm env (TmVar var) = increEnv env var
linearCheckTm env (TmLInj tm) = linearCheckTm env tm
linearCheckTm env (TmRInj tm) = linearCheckTm env tm
linearCheckTm env (TmPair l r) = env'' where
  env' = linearCheckTm env l
  env'' = linearCheckTm env' r
linearCheckTm env (TmIsoApp iso tm) = linearCheckTm env' tm where
  env' = linearCheckIso env iso
linearCheckTm env (TmLet pat rhs body) = env'''' where
  env' = linearCheckTm env rhs
  env'' = extendPat env' pat
  env''' = linearCheckTm env'' body
  env'''' = dropPat env''' pat
linearCheckTm env (TmAnn tm _) = linearCheckTm env tm

{---------- Linear checking for Isos ----------}
linearCheckIso :: LinearEnv -> Iso -> LinearEnv
linearCheckIso env (IsoValue pairs) = linearCheckIsoPairs env pairs
linearCheckIso env (IsoVar _) = env
-- iso var binding is ignored
linearCheckIso env (IsoLam _ _ _ body) = linearCheckIso env body
linearCheckIso env (IsoApp rator rand) = linearCheckIso env' rator where
  env' = linearCheckIso env rand
linearCheckIso _ (IsoFix _ _) = error $ "IsoFix is not supported yet!"
linearCheckIso env (IsoAnn iso _) = linearCheckIso env iso

linearCheckIsoPairs :: LinearEnv -> [(Value, Exp)] -> LinearEnv
linearCheckIsoPairs env [] = env
linearCheckIsoPairs env (hd:tl) = linearCheckIsoPairs env' tl where
  env' = linearCheckIsoPair env hd

linearCheckIsoPair :: LinearEnv -> (Value, Exp) -> LinearEnv
linearCheckIsoPair env (v, e) = env'' where
  vars = linearCheckValue env v
  env' = extendPat env (PtMultiVar vars)
  env'' = linearCheckExp env' e

{---------- Linear type checking for Values -----------}
linearCheckValue :: LinearEnv -> Value -> [String]
linearCheckValue _ ValUnit = []
linearCheckValue _ (ValInt _) = []
linearCheckValue _ (ValVar var) = [var]
linearCheckValue env (ValLInj v) = linearCheckValue env v
linearCheckValue env (ValRInj v) = linearCheckValue env v
linearCheckValue env (ValPair l r) = lVars ++ rVars where
  lVars = linearCheckValue env l
  rVars = linearCheckValue env r
linearCheckValue env (ValAnn v _) = linearCheckValue env v

{---------- Linear type checking for Exps -----------}
linearCheckExp :: LinearEnv -> Exp -> LinearEnv
linearCheckExp env (ExpVal val) = linearCheckValueNoPattern env val
linearCheckExp env (ExpLet pat iso pat' body) = env''''' where
  env' = linearCheckIso env iso
  env'' = linearCheckRhsPattern env' pat'
  env''' = extendPat env'' pat
  env'''' = linearCheckExp env''' body
  env''''' = dropPat env'''' pat

linearCheckRhsPattern :: LinearEnv -> Pattern -> LinearEnv
linearCheckRhsPattern env (PtSingleVar var) = increEnv env var
linearCheckRhsPattern env (PtMultiVar vars) = foldl increEnv env vars

{-- Linear type checking for Values (Non-pattern) --}
linearCheckValueNoPattern :: LinearEnv -> Value -> LinearEnv
linearCheckValueNoPattern env ValUnit = env
linearCheckValueNoPattern env (ValInt _) = env
linearCheckValueNoPattern env (ValVar var) = increEnv env var
linearCheckValueNoPattern env (ValLInj v) = linearCheckValueNoPattern env v
linearCheckValueNoPattern env (ValRInj v) = linearCheckValueNoPattern env v
linearCheckValueNoPattern env (ValPair l r) = env'' where
  env' = linearCheckValueNoPattern env l
  env'' = linearCheckValueNoPattern env' r
linearCheckValueNoPattern env (ValAnn v _) = linearCheckValueNoPattern env v

{-- Helper functions --}
increEnv :: LinearEnv -> String -> LinearEnv
increEnv [] var = error $ show var ++ " not found!"
increEnv ((var',n):tl) var
  | var == var' =
      if n > 0
      then error $ "Variable " ++ show var ++ " is used more than once!"
      else ((var', (n + 1)):tl)
increEnv ((var',n):tl) var = (var',n):(increEnv tl var)

extendPat :: LinearEnv -> Pattern -> LinearEnv
extendPat env (PtSingleVar var) = (var, 0):env
extendPat env (PtMultiVar vars) = (map (\x -> (x , 0)) vars) ++ env

dropPat :: LinearEnv -> Pattern -> LinearEnv
dropPat (_:tl) (PtSingleVar _) = tl
dropPat env (PtMultiVar []) = env
dropPat (_:tl) (PtMultiVar (_:vars)) = extendPat tl (PtMultiVar vars)
dropPat env pat = error $ "Environment " ++ show env ++ " doesn't have enough variables for" ++ show pat ++ "!"
