module Interp (interp, interpEnv) where

import Syntax
import Debug.Trace (trace)

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
  applyIsoTerm fun arg
interpTm env (TmLet pat rhs body) = do
  vRhs <- interpTm env rhs
  newEnv <- extendPattern env pat vRhs
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
  applyIsoIso lval rval
interpIso _ (IsoFix _ _) = error "Evaluation of IsoFix is not supported yet!"
interpIso env (IsoAnn iso _) = interpIso env iso

interpIsoPairs :: ValEnv -> [(Value, Exp)] -> Result [(ProgramBaseValue , ProgramBaseValue)]
interpIsoPairs _ [] = return []
interpIsoPairs env (p:ps) = do
  val <- interpIsoPair env p
  vals <- interpIsoPairs env ps
  return (val:vals)

{---------- Applying An Iso To A Term ----------}
applyIsoTerm :: ProgramIsoValue -> ProgramBaseValue -> Result ProgramBaseValue
-- applyIsoTerm l r | trace ("applyIsoTerm " ++ show l ++ " " ++ show r) False = undefined
applyIsoTerm (PIValBase isos env) rhs = patternMatch env isos rhs
applyIsoTerm iso base = Left $ "Cannot apply iso " ++ show iso ++ " to " ++ show base

{---------- Applying An Iso To An Iso ----------}
applyIsoIso :: ProgramIsoValue -> ProgramIsoValue -> Result ProgramIsoValue
applyIsoIso (PIValLam var body env) rhs = interpIso ((var , (PI rhs)) : env) body
applyIsoIso (PIValFix var body env) _ =
  error $ "Application of IsoFix is not supported yet, given " ++ show (PIValFix var body env)
applyIsoIso (PIValBase pairs env) _ =
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
  lhsPair <- interpPattern env pat
  let vars = map (\x -> (x , PB (PBValVar x))) (snd lhsPair)
  rhs <- interpExp (vars ++ env) e
  return (fst lhsPair, rhs)

{---------- Interpretation of One Pattern in LHS ----------}
interpPattern :: ValEnv -> Value -> Result (ProgramBaseValue, [String])
interpPattern _ ValUnit = return (PBValUnit , [])
interpPattern _ (ValInt n) = return (PBValInt n , [])
interpPattern _ (ValVar var) = return (PBValVar var , [var])
interpPattern env (ValLInj lhs) = do
  rst <- interpPattern env lhs
  return (PBValLeft $ fst rst , snd rst)
interpPattern env (ValRInj rhs) = do
  rst <- interpPattern env rhs
  return (PBValRight $ fst rst , snd rst)
interpPattern env (ValPair lhs rhs) = do
  v1 <- interpPattern env lhs
  v2 <- interpPattern env rhs
  return (PBValPair (fst v1) (fst v2) , (snd v1) ++ (snd v2))
interpPattern env (ValAnn val _) = interpPattern env val
--  TODO: ValFold

{---------- Interpretation of Expressions ----------}
interpExp :: ValEnv -> Exp -> Result ProgramBaseValue
interpExp env (ExpVal v) = interpValue env v
interpExp env (ExpLet pat iso pat' body) = do
  rhsIso <- interpIso env iso
  rhsVal <- interpRhsPattern env pat'
  vRhs <- applyIsoTerm rhsIso rhsVal
  newEnv <- extendPattern env pat vRhs
  interpExp newEnv body

{---------- Interpretation of Patterns in iso RHS' RHS  ----------}
interpRhsPattern :: ValEnv -> Pattern -> Result ProgramBaseValue
interpRhsPattern env (PtSingleVar var) = lookupBase env var
interpRhsPattern env (PtMultiVar (var : [])) = lookupBase env var
interpRhsPattern env (PtMultiVar (var : vars)) = do
  val <- lookupBase env var
  vals <- interpRhsPattern env (PtMultiVar vars)
  return $ PBValPair val vals
interpRhsPattern _ pat = Left $ "Invalid pattern: " ++ show pat

{---------- Interpretation of iso RHS values ----------}
interpExpValue :: ValEnv -> ProgramBaseValue -> Result ProgramBaseValue
interpExpValue _ PBValUnit = return PBValUnit
interpExpValue _ (PBValInt n) = return (PBValInt n)
interpExpValue env (PBValVar var) = lookupBase env var
interpExpValue env (PBValLeft l) = do
  lVal <- interpExpValue env l
  return (PBValLeft lVal)
interpExpValue env (PBValRight l) = do
  lVal <- interpExpValue env l
  return (PBValRight lVal)
interpExpValue env (PBValPair l r) = do
  lVal <- interpExpValue env l
  rVal <- interpExpValue env r
  return (PBValPair lVal rVal)

{---------- Pattern Matching in iso RHS ----------}
patternMatch :: ValEnv -> [(ProgramBaseValue , ProgramBaseValue)] -> ProgramBaseValue
  -> Result ProgramBaseValue
patternMatch _ [] _ = Left "Invalid pattern: no pattern variable provided"
patternMatch env ((lhs , rhs) : tl) v =
  if isMatch lhs v
  then let pairs = extracPatterns lhs v
           newEnv = pairs ++ env
       in interpExpValue newEnv rhs
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
extracPatterns :: ProgramBaseValue -> ProgramBaseValue -> ValEnv
extracPatterns PBValUnit _ = []
extracPatterns (PBValInt _) _ = []
extracPatterns (PBValVar var) val = [(var , PB val)]
extracPatterns (PBValLeft v1) (PBValLeft v2) = extracPatterns v1 v2
extracPatterns (PBValRight v1) (PBValRight v2) = extracPatterns v1 v2
extracPatterns (PBValPair l1 r1) (PBValPair l2 r2) = extracPatterns l1 l2 ++ extracPatterns r1 r2
extracPatterns _ _ = []

{---------- Extending Environments With Patterns ----------}
extendPattern :: ValEnv -> Pattern -> ProgramBaseValue -> Result ValEnv
extendPattern env (PtSingleVar var) val  = return ((var , PB val) : env)
extendPattern env (PtMultiVar (var : [])) val  = return ((var , PB val) : env)
extendPattern env (PtMultiVar (var : vars)) (PBValPair hd tl) = do
  newTl <- extendPattern env (PtMultiVar vars) tl
  return ((var , (PB hd)) : newTl)
extendPattern _ pat val = Left $ "Mismatched pattern and value: " ++ show pat ++ ", " ++ show val

{---------- Environment Lookup ----------}
lookupBase :: ValEnv -> String -> Result ProgramBaseValue
lookupBase env var = do
  case lookup var env of
    Just (PB bv) -> return bv
    _ -> Left $ "Cannot find the value " ++ show var

lookupIso :: ValEnv -> String -> Result ProgramIsoValue
lookupIso env var = do
  case lookup var env of
    Just (PI bv) -> return bv
    _ -> Left $ "Cannot find the iso " ++ show var
