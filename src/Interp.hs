module Interp (interp, interpEnv, applyIso) where

import Syntax
import Debug.Trace (trace)

moduleName :: String
moduleName = "Interpreter: "

interp :: Program -> Result ProgramValue
interp pg = interpEnv [] pg

interpEnv :: ValEnv -> Program -> Result ProgramValue
interpEnv env (PgTm tm) = do
  v <- (interpTm env tm)
  return (PB v)
interpEnv env (PgIs iso) = do
  v <- interpIso env iso
  return (PI v)

{---------- Interpretation of Terms ----------}
interpTm :: ValEnv -> Term -> Result ProgramBaseValue
interpTm _ TmUnit = return PBValUnit
interpTm _ (TmInt n) = return (PBValInt n)
interpTm env (TmVar var) = lookupBase env var
interpTm env (TmLInj tm) = do
  v <- interpTm env tm
  return (PBValLeft v)
interpTm env (TmRInj tm) = do
  v <- interpTm env tm
  return (PBValRight v)
interpTm env (TmPair t1 t2) = do
  v1 <- interpTm env t1
  v2 <- interpTm env t2
  return (PBValPair v1 v2)
interpTm env (TmIsoApp iso tm) = do
  fun <- interpIso env iso
  arg <- interpTm env tm
  applyIso fun arg
interpTm env (TmLet pat rhs body) = do
  vRhs <- interpTm env rhs
  newEnv <- extPat env pat vRhs
  interpTm newEnv body
interpTm env (TmAnn tm _) = interpTm env tm

{---------- Interpretation of Isos ----------}
interpIso :: ValEnv -> Iso -> Result ProgramIsoValue
interpIso env (IsoValue ps) = do
  pairs <- interpIsoPairs env ps
  return (PIValBase pairs env)
interpIso env (IsoVar var) = lookupIso env var
interpIso env (IsoLam var _ _ body) = return (PIValLam var body env)
interpIso env (IsoApp lhs rhs) = do
  lval <- interpIso env lhs
  rval <- interpIso env rhs
  applyIsoLam lval rval
interpIso _ (IsoFix _ _) = error "Evaluation of IsoFix is not supported yet!"
interpIso env (IsoAnn iso _) = interpIso env iso

interpIsoPairs :: ValEnv -> [(Value, Exp)] -> Result [(ProgramBaseValue , ProgramBaseValue)]
interpIsoPairs _ [] = return []
interpIsoPairs env (p:ps) = do
  val <- interpIsoPair env p
  vals <- interpIsoPairs env ps
  return (val:vals)

{---------- Applying An Iso To A Term ----------}
applyIso :: ProgramIsoValue -> ProgramBaseValue -> Result ProgramBaseValue
-- applyIso l r | trace ("applyIso " ++ show l ++ " " ++ show r) False = undefined
applyIso (PIValBase isos env) rhs = patternMatch env isos rhs
applyIso iso base = Left $ moduleName ++ "Cannot apply iso " ++ show iso ++ " to " ++ show base

{---------- Applying An Iso To An Iso ----------}
applyIsoLam :: ProgramIsoValue -> ProgramIsoValue -> Result ProgramIsoValue
applyIsoLam (PIValLam var body env) rhs = interpIso ((var , (PI rhs)) : env) body
applyIsoLam (PIValFix var body env) _ =
  error $ "Application of IsoFix is not supported yet, given " ++ show (PIValFix var body env)
applyIsoLam (PIValBase pairs env) _ =
  error $ "Expect an Iso Lambda, given an Iso Base " ++ show (PIValBase pairs env)

{---------- Interpretation of Values ----------}
interpValue :: ValEnv -> Value -> Result ProgramBaseValue
interpValue _ ValUnit = return PBValUnit
interpValue _ (ValInt n) = return (PBValInt n)
interpValue env (ValVar var) = lookupBase env var
interpValue env (ValLInj lhs) = do
  v <- interpValue env lhs
  return (PBValLeft v)
interpValue env (ValRInj rhs) = do
  v <- interpValue env rhs
  return (PBValRight v)
interpValue env (ValPair lhs rhs) = do
  v1 <- interpValue env lhs
  v2 <- interpValue env rhs
  return (PBValPair v1 v2)
interpValue env (ValAnn val _) = interpValue env val
--  TODO: ValFold

{---------- Interpretation of One Pair of Values In An Iso ----------}
interpIsoPair :: ValEnv -> (Value, Exp) -> Result (ProgramBaseValue, ProgramBaseValue)
interpIsoPair env (pat, e) = do
  lhsPair <- interpPat env pat
  let vars = map (\x -> (x , PB (PBValVar x))) (snd lhsPair)
  rhs <- interpExp (vars ++ env) e
  return (fst lhsPair, rhs)

{---------- Interpretation of One Pattern in LHS ----------}
interpPat :: ValEnv -> Value -> Result (ProgramBaseValue, [String])
interpPat _ ValUnit = return (PBValUnit , [])
interpPat _ (ValInt n) = return (PBValInt n , [])
interpPat _ (ValVar var) = return (PBValVar var , [var])
interpPat env (ValLInj lhs) = do
  rst <- interpPat env lhs
  return (PBValLeft $ fst rst , snd rst)
interpPat env (ValRInj rhs) = do
  rst <- interpPat env rhs
  return (PBValRight $ fst rst , snd rst)
interpPat env (ValPair lhs rhs) = do
  v1 <- interpPat env lhs
  v2 <- interpPat env rhs
  return (PBValPair (fst v1) (fst v2) , (snd v1) ++ (snd v2))
interpPat env (ValAnn val _) = interpPat env val
--  TODO: ValFold

{---------- Interpretation of Expressions ----------}
interpExp :: ValEnv -> Exp -> Result ProgramBaseValue
interpExp env (ExpVal v) = interpValue env v
interpExp env (ExpLet pat iso pat' body) = do
  rhsIso <- interpIso env iso
  rhsVal <- interpRhsPat env pat'
  vRhs <- applyIso rhsIso rhsVal
  newEnv <- extPat env pat vRhs
  interpExp newEnv body

{---------- Interpretation of Patterns in iso RHS' RHS  ----------}
interpRhsPat :: ValEnv -> Pattern -> Result ProgramBaseValue
interpRhsPat env (PtSingleVar var) = lookupBase env var
interpRhsPat env (PtMultiVar (var : [])) = lookupBase env var
interpRhsPat env (PtMultiVar (var : vars)) = do
  val <- lookupBase env var
  vals <- interpRhsPat env (PtMultiVar vars)
  return $ PBValPair val vals
interpRhsPat _ pat = Left $ moduleName ++ "Invalid pattern: " ++ show pat

{---------- Interpretation of iso RHS values ----------}
interpExpVal :: ValEnv -> ProgramBaseValue -> Result ProgramBaseValue
interpExpVal _ PBValUnit = return PBValUnit
interpExpVal _ (PBValInt n) = return (PBValInt n)
interpExpVal env (PBValVar var) = lookupBase env var
interpExpVal env (PBValLeft l) = do
  lVal <- interpExpVal env l
  return (PBValLeft lVal)
interpExpVal env (PBValRight l) = do
  lVal <- interpExpVal env l
  return (PBValRight lVal)
interpExpVal env (PBValPair l r) = do
  lVal <- interpExpVal env l
  rVal <- interpExpVal env r
  return (PBValPair lVal rVal)

{---------- Pattern Matching in iso RHS ----------}
patternMatch :: ValEnv -> [(ProgramBaseValue , ProgramBaseValue)] -> ProgramBaseValue
  -> Result ProgramBaseValue
patternMatch _ [] val = Left $ moduleName ++ "Invalid pattern: no match for the value " ++ show val
patternMatch env ((lhs , rhs) : tl) v =
  if isMatch lhs v
  then let pairs = extracPat lhs v
           newEnv = pairs ++ env
       in interpExpVal newEnv rhs
  else patternMatch env tl v

{---------- Pattern Match Checking ----------}
isMatch :: ProgramBaseValue -> ProgramBaseValue -> Bool
isMatch PBValUnit PBValUnit = True
isMatch (PBValInt n1) (PBValInt n2) = (n1 == n2)
isMatch (PBValVar _) _ = True
isMatch (PBValLeft v1) (PBValLeft v2) = isMatch v1 v2
isMatch (PBValRight v1) (PBValRight v2) = isMatch v1 v2
isMatch (PBValPair l1 r1) (PBValPair l2 r2) = isMatch l1 l2 && isMatch r1 r2
isMatch _ _ = False

{---------- Pattern Match Extractions ----------}
extracPat :: ProgramBaseValue -> ProgramBaseValue -> ValEnv
extracPat PBValUnit _ = []
extracPat (PBValInt _) _ = []
extracPat (PBValVar var) val = [(var , PB val)]
extracPat (PBValLeft v1) (PBValLeft v2) = extracPat v1 v2
extracPat (PBValRight v1) (PBValRight v2) = extracPat v1 v2
extracPat (PBValPair l1 r1) (PBValPair l2 r2) = extracPat l1 l2 ++ extracPat r1 r2
extracPat _ _ = []

{---------- Extending Environments With Patterns ----------}
extPat :: ValEnv -> Pattern -> ProgramBaseValue -> Result ValEnv
extPat env (PtSingleVar var) val  = return ((var , PB val) : env)
extPat env (PtMultiVar (var : [])) val  = return ((var , PB val) : env)
extPat env (PtMultiVar (var : vars)) (PBValPair hd tl) = do
  newTl <- extPat env (PtMultiVar vars) tl
  return ((var , (PB hd)) : newTl)
extPat _ pat val = Left $ moduleName ++ "Mismatched pattern and value: " ++ show pat ++ ", " ++ show val

{---------- Environment Lookup ----------}
lookupBase :: ValEnv -> String -> Result ProgramBaseValue
lookupBase env var = do
  case lookup var env of
    Just (PB bv) -> return bv
    _ -> Left $ moduleName ++ "Cannot find the value " ++ show var

lookupIso :: ValEnv -> String -> Result ProgramIsoValue
lookupIso env var = do
  case lookup var env of
    Just (PI bv) -> return bv
    _ -> Left $ moduleName ++ "Cannot find the iso " ++ show var
