module Interp (interp) where

import Syntax
import Debug.Trace (trace)

interp :: ValEnv -> Program -> Maybe ProgramValue
interp env (PgTm tm) = do {
  v <- (interpTm env tm)
  ; Just (PB v)
  }
interp env (PgIs iso) = do {
  v <- interpIso env iso
  ; Just (PI v)
  }

{---------- Interpretation of Terms ----------}
interpTm :: ValEnv -> Term -> Maybe ProgramBaseValue
interpTm _ TmUnit = Just PBValUnit
interpTm _ (TmInt n) = Just (PBValInt n)
interpTm env (TmVar var) = lookupBase env var
interpTm env (TmLInj tm) = do {
  v <- interpTm env tm
  ; Just (PBValLeft v)
  }
interpTm env (TmRInj tm) = do {
  v <- interpTm env tm
  ; Just (PBValRight v)
  }
interpTm env (TmPair t1 t2) = do {
  v1 <- interpTm env t1
  ; v2 <- interpTm env t2
  ; Just (PBValPair v1 v2)
  }
interpTm env (TmIsoApp iso tm) = do {
  fun <- interpIso env iso
  ; arg <- interpTm env tm
  ; applyIsoTerm fun arg
  }
interpTm env (TmLet pat rhs body) = do {
  vRhs <- interpTm env rhs
  ; newEnv <- extendPattern env pat vRhs
  ; interpTm newEnv body
  }
interpTm env (TmAnn tm _) = interpTm env tm

{---------- Interpretation of Isos ----------}
interpIso :: ValEnv -> Iso -> Maybe ProgramIsoValue
interpIso env (IsoValue ps) = do {
  let pairs = map (interpIsoPair env) $ ps
  ; newPairs <- zipValues pairs
  ; Just (PIValBase newPairs env)
  }
interpIso env (IsoVar var) = do {
  v <- lookup var env
  ; case v of
      PI iv -> Just iv
      _ -> Nothing
  }
interpIso env (IsoLam var _ _ body) =
  Just (PIValLam var body env)
interpIso env (IsoApp lhs rhs) = do {
  lval <- interpIso env lhs
  ; rval <- interpIso env rhs
  ; applyIsoIso lval rval
  }
interpIso _ (IsoFix _ _) = error "Evaluation of IsoFix is not supported yet!"
interpIso env (IsoAnn iso _) = interpIso env iso

zipValues :: [(Maybe ProgramBaseValue, Maybe ProgramBaseValue)] ->
  Maybe [(ProgramBaseValue, ProgramBaseValue)]
zipValues [] = Just []
zipValues (((Just lh), (Just rh)) : tl) = do {
  let hd = (lh , rh)
  ; newTl <- zipValues tl
  ; Just (hd : newTl)
  }
zipValues _ = Nothing

{---------- Applying An Iso To A Term ----------}
applyIsoTerm :: ProgramIsoValue -> ProgramBaseValue -> Maybe ProgramBaseValue
-- applyIsoTerm l r | trace ("applyIsoTerm " ++ show l ++ " " ++ show r) False = undefined
applyIsoTerm (PIValBase isos env) rhs = patternMatch env isos rhs
applyIsoTerm _ _ = Nothing

{---------- Applying An Iso To An Iso ----------}
applyIsoIso :: ProgramIsoValue -> ProgramIsoValue -> Maybe ProgramIsoValue
applyIsoIso (PIValLam var body env) rhs = interpIso ((var , (PI rhs)) : env) body
applyIsoIso (PIValFix var body env) _ =
  error $ "Application of IsoFix is not supported yet, given " ++ show (PIValFix var body env)
applyIsoIso (PIValBase pairs env) _ =
  error $ "Expect an Iso Lambda, given an Iso Base " ++ show (PIValBase pairs env)

{---------- Interpretation of Values ----------}
interpValue :: ValEnv -> Value -> Maybe ProgramBaseValue
interpValue _ ValUnit = Just PBValUnit
interpValue _ (ValInt n) = Just (PBValInt n)
interpValue env (ValVar var) = lookupBase env var
interpValue env (ValLInj lhs) =  do {
  v <- interpValue env lhs
  ; Just (PBValLeft v)
  }
interpValue env (ValRInj rhs) =  do {
  v <- interpValue env rhs
  ; Just (PBValRight v)
  }
interpValue env (ValPair lhs rhs) =  do {
  v1 <- interpValue env lhs
  ; v2 <- interpValue env rhs
  ; Just (PBValPair v1 v2)
  }
interpValue env (ValAnn val _) = interpValue env val
--  TODO: ValFold

{---------- Interpretation of One Pair of Values In An Iso ----------}
interpIsoPair :: ValEnv -> (Value, Exp) -> (Maybe ProgramBaseValue, Maybe ProgramBaseValue)
interpIsoPair env (pat, e) = (lhs, rhs) where
  lhsPair = interpPattern env pat
  lhs = Just $ fst lhsPair
  vars = map (\x -> (x , PB (PBValVar x))) (snd lhsPair)
  rhs = interpExp (vars ++ env) e

{---------- Interpretation of One Pattern in LHS ----------}
interpPattern :: ValEnv -> Value -> (ProgramBaseValue, [String])
interpPattern _ ValUnit = (PBValUnit , [])
interpPattern _ (ValInt n) = (PBValInt n , [])
interpPattern _ (ValVar var) = (PBValVar var , [var])
interpPattern env (ValLInj lhs) = (PBValLeft $ fst rst , snd rst) where
  rst = interpPattern env lhs
interpPattern env (ValRInj rhs) = (PBValRight $ fst rst , snd rst) where
  rst = interpPattern env rhs
interpPattern env (ValPair lhs rhs) =
  (PBValPair (fst v1) (fst v2) , (snd v1) ++ (snd v2)) where
    v1 = interpPattern env lhs
    v2 = interpPattern env rhs
interpPattern env (ValAnn val _) = interpPattern env val
--  TODO: ValFold

{---------- Interpretation of Expressions ----------}
interpExp :: ValEnv -> Exp -> Maybe ProgramBaseValue
interpExp env (ExpVal v) = interpValue env v
interpExp env (ExpLet pat1 iso pat2 body) = do {
  rhsIso <- interpIso env iso
  ; rhsVal <- interpRhsPattern env pat2
  ; vRhs <- applyIsoTerm rhsIso rhsVal
  ; newEnv <- extendPattern env pat1 vRhs
  ; interpExp newEnv body
  }

{---------- Interpretation of Patterns in iso RHS' RHS  ----------}
interpRhsPattern :: ValEnv -> Pattern -> Maybe ProgramBaseValue
interpRhsPattern env (PtSingleVar var) = lookupBase env var
interpRhsPattern env (PtMultiVar (var : [])) = lookupBase env var
interpRhsPattern env (PtMultiVar (var : vars)) = do {
  val <- lookupBase env var
  ; vals <- interpRhsPattern env (PtMultiVar vars)
  ; Just $ PBValPair val vals
  }
interpRhsPattern _ _ = Nothing

{---------- Interpretation of iso RHS values ----------}
interpExpValue :: ValEnv -> ProgramBaseValue -> Maybe ProgramBaseValue
interpExpValue _ PBValUnit = Just PBValUnit
interpExpValue _ (PBValInt n) = Just (PBValInt n)
interpExpValue env (PBValVar var) = lookupBase env var
interpExpValue env (PBValLeft l) = do {
  lVal <- interpExpValue env l
  ; Just (PBValLeft lVal)
  }
interpExpValue env (PBValRight l) = do {
  lVal <- interpExpValue env l
  ; Just (PBValRight lVal)
  }
interpExpValue env (PBValPair l r) = do {
  lVal <- interpExpValue env l
  ; rVal <- interpExpValue env r
  ; Just (PBValPair lVal rVal)
  }

{---------- Pattern Matching in iso RHS ----------}
patternMatch :: ValEnv -> [(ProgramBaseValue , ProgramBaseValue)] -> ProgramBaseValue
  -> Maybe ProgramBaseValue
patternMatch _ [] _ = Nothing
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
extendPattern :: ValEnv -> Pattern -> ProgramBaseValue -> Maybe ValEnv
extendPattern env (PtSingleVar var) val  = Just ((var , PB val) : env)
extendPattern env (PtMultiVar (var : [])) val  = Just ((var , PB val) : env)
extendPattern env (PtMultiVar (var : vars)) (PBValPair hd tl)  = do {
  newTl <- extendPattern env (PtMultiVar vars) tl
  ; Just ((var , (PB hd)) : newTl)
  }
extendPattern _ _ _ = Nothing

{---------- Environment Lookup ----------}
lookupBase :: ValEnv -> String -> Maybe ProgramBaseValue
lookupBase env var = do {
  v <- lookup var env
  ; case v of
      PB bv -> Just bv
      _ -> Nothing
  }
