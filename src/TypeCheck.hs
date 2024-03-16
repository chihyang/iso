module TypeCheck (typeInfer) where

import Data

typeInfer :: TypEnv -> Program -> Program
typeInfer env (PgTm tm) = PgTm $ snd $ typeInferTm env tm
typeInfer env (PgIs iso) = PgIs $ snd $ typeInferIso env iso

{---------- Bidirectional type checking for Terms ----------}
-- Return a type annotated term together with its type.
typeInferTm :: TypEnv -> Term -> (BaseType, Term)
typeInferTm _ TmUnit = (BTyUnit , TmAnn TmUnit BTyUnit)
typeInferTm _ (TmInt n) = (BTyInt , TmAnn (TmInt n) BTyInt)
typeInferTm env (TmVar var) = (ty , TmAnn (TmVar var) ty) where
  ty = applyBaseEnv env var
typeInferTm _ (TmLInj tm) = error $ "Type annotation is required for the term " ++ show (TmLInj tm)
typeInferTm _ (TmRInj tm) = error $ "Type annotation is required for the term " ++ show (TmLInj tm)
typeInferTm env (TmPair l r) = (oType , TmAnn (TmPair lTm rTm) oType)  where
  rstL = typeInferTm env l
  rstR = typeInferTm env r
  lTy = fst rstL
  rTy = fst rstR
  lTm = snd rstL
  rTm = snd rstR
  oType = (BTyProd lTy rTy)
typeInferTm env (TmIsoApp iso tm) =
  let isoRst = typeInferIso env iso
      isoTy = fst isoRst
      iso' = snd isoRst
  in case isoTy of
    ITyBase lT rT ->
      let rst = typeCheckTm env tm lT
          argType = fst rst
          tm' = snd rst
      in if typeEqual env lT argType
         then (rT , (TmAnn (TmIsoApp iso' tm') rT))
         else error $ "The operand " ++ show tm ++ " has the type " ++ show argType ++ " , expect " ++ show lT
    _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"
typeInferTm env (TmLet pat rhs body) = (bodyTy , TmAnn (TmLet pat rhs' body') bodyTy) where
  rhsRst = typeInferTm env rhs
  rhsTy = fst rhsRst
  rhs' = snd rhsRst
  newEnv = extendPatternEnv env pat rhsTy
  bodyRst = typeInferTm newEnv body
  bodyTy = fst bodyRst
  body' = snd bodyRst
typeInferTm env (TmAnn tm ty) = typeCheckTm env tm ty

typeCheckTm :: TypEnv -> Term -> BaseType -> (BaseType, Term)
typeCheckTm env TmUnit ty =
  if typeEqual env BTyUnit ty
  then (BTyUnit , TmAnn TmUnit BTyUnit)
  else error $ "Expect " ++ show BTyUnit ++ ", got " ++ show ty ++ " in " ++ show TmUnit
typeCheckTm env (TmInt n) ty =
  if typeEqual env BTyInt ty
  then (BTyInt , TmAnn (TmInt n) BTyInt)
  else error $ "Expect " ++ show BTyInt ++ ", got " ++ show ty ++ " in " ++ show (TmInt n)
typeCheckTm env (TmVar var) ty =
  let ty' = applyBaseEnv env var
  in if typeEqual env ty' ty
     then (ty, TmAnn (TmVar var) ty)
     else error $ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (TmVar var)
typeCheckTm env (TmLInj tm) (BTySum lTy rTy) = (rstTy , TmAnn (TmLInj tm') rstTy) where
  rst = typeCheckTm env tm lTy
  tm' = snd rst
  rstTy = BTySum lTy rTy
typeCheckTm env (TmRInj tm) (BTySum lTy rTy) =  (rstTy , TmAnn (TmRInj tm') rstTy) where
  rst = typeCheckTm env tm rTy
  tm' = snd rst
  rstTy = BTySum lTy rTy
typeCheckTm env (TmPair lhs rhs) (BTyProd lTy rTy) =
  (oType , (TmAnn (TmPair lhs' rhs') oType)) where
    lRst = typeCheckTm env lhs lTy
    rRst = typeCheckTm env rhs rTy
    lhs' = snd lRst
    rhs' = snd rRst
    oType = (BTyProd lTy rTy)
typeCheckTm env (TmIsoApp iso tm) ty =
  let isoRst = typeInferIso env iso
      isoTy = fst isoRst
      iso' = snd isoRst
  in case isoTy of
       ITyBase lT rT ->
         let rst = typeCheckTm env tm lT
             argType = fst rst
             tm' = snd rst
         in if typeEqual env lT argType
            then if typeEqual env rT ty
                 then (ty , (TmAnn (TmIsoApp iso' tm') ty))
                 else error $ "The return " ++ show (TmIsoApp iso tm) ++
                      " has the type " ++ show rT ++ " , expect " ++ show ty
            else error $ "The operand " ++ show tm ++ " has the type " ++ show argType ++ " , expect " ++ show lT
       _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"
typeCheckTm env (TmLet pat rhs body) ty = (ty , TmAnn (TmLet pat rhs' body') ty) where
  rhsRst = typeInferTm env rhs
  rhsTy = fst rhsRst
  rhs' = snd rhsRst
  newEnv = extendPatternEnv env pat rhsTy
  bodyRst = typeCheckTm newEnv body ty
  body' = snd bodyRst
typeCheckTm env (TmAnn tm ty) ty' =
  if typeEqual env ty ty'
  then typeCheckTm env tm ty'
  else error $ "Expect " ++ show tm ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
typeCheckTm _ tm ty = error $ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Isos ----------}
typeInferIso :: TypEnv -> Iso -> (IsoType, Iso)
typeInferIso env (IsoValue pairs) = (otype , ov) where
  otype = typeInferIsoPairs env pairs
  ov = IsoAnn (IsoValue pairs) otype
typeInferIso env (IsoVar var) = (otype , ov) where
  otype = applyIsoEnv env var
  ov = IsoAnn (IsoVar var) otype
typeInferIso env (IsoLam var vLhsTy vRhsTy body) = (otype , ov) where
  newEnv = extendIsoEnv env var (ITyBase vLhsTy vRhsTy)
  rst = typeInferIso newEnv body
  bodyTy = fst rst
  body' = snd rst
  otype = ITyFun vLhsTy vRhsTy bodyTy
  ov = IsoAnn (IsoLam var vLhsTy vRhsTy body') otype
typeInferIso env (IsoApp rator rand) =
  let ratorRst = typeInferIso env rator
      ratorTy = fst ratorRst
      rator' = snd ratorRst
  in let randRst = typeInferIso env rand
         randTy = fst randRst
         rand' = snd randRst
     in case (ratorTy , randTy) of
          (ITyFun lhsTy rhsTy bodyTy, ITyBase randLhsTy randRhsTy) ->
            if typeEqual env lhsTy randLhsTy && typeEqual env rhsTy randRhsTy
            then (bodyTy , IsoAnn (IsoApp rator' rand') bodyTy)
            else error $ "Expect " ++ show rator ++ " and " ++ show rand  ++ " to have matched type!"
          (_, _) -> error $ "Expect " ++ show rator ++ " to have the type (Iso -> Iso)!"
typeInferIso _ (IsoFix _ _) = error $ "IsoFix is not supported yet!"
typeInferIso _ (IsoAnn _ _) = error $ "IsoAnn is an internal node!"

typeInferIsoPairs :: TypEnv -> [(Value, Exp)] -> IsoType
typeInferIsoPairs _ [] = error $ "There must be at least one pair of values in an iso, given zero!"
typeInferIsoPairs env (hd:tl) = typeCheckIsoPairs env tl lhsTy rhsTy where
  ty = typeInferIsoPair env hd
  lhsTy = fst ty
  rhsTy = snd ty

typeCheckIsoPairs :: TypEnv -> [(Value, Exp)] -> BaseType -> BaseType -> IsoType
typeCheckIsoPairs _ [] lhsTy rhsTy = ITyBase lhsTy rhsTy
typeCheckIsoPairs env (hd:tl) lhsTy rhsTy =
  typeCheckIsoPairs env tl lhsTy' rhsTy' where
    rst = typeCheckIsoPair env hd lhsTy rhsTy
    lhsTy' = fst rst
    rhsTy' = snd rst

typeInferIsoPair :: TypEnv -> (Value, Exp) -> (BaseType, BaseType)
typeInferIsoPair env (lhs, rhs) = (lTy , rTy) where
  lRst = typeInferValue env lhs
  lTy = fst $ fst lRst
  lBinds = snd lRst
  newEnv = extendMultiBaseEnv env lBinds
  rTy = typeInferExp newEnv rhs

typeCheckIsoPair :: TypEnv -> (Value, Exp) -> BaseType -> BaseType -> (BaseType, BaseType)
typeCheckIsoPair env (lhs , rhs) lTy rTy = (lTy' , rTy') where
  lRst = typeCheckValue env lhs lTy
  lTy' = fst $ fst lRst
  lBinds = snd lRst
  newEnv = extendMultiBaseEnv env lBinds
  rTy' = typeCheckExp newEnv rhs rTy

{---------- Bidirectional type checking for Values -----------}
-- Return the type of the given value, the type annotated value, and all pattern
-- variables and the corresponding type in this value.
typeInferValue :: TypEnv -> Value -> ((BaseType, Value), [(String, BaseType)])
typeInferValue _ ValUnit = ((BTyUnit, ValAnn ValUnit BTyUnit) , [])
typeInferValue _ (ValInt n) = ((BTyInt, ValAnn (ValInt n) BTyInt) , [])
typeInferValue _ (ValVar var) = error $ "Type annotation is required for a single pattern var " ++ var ++ "!"
typeInferValue _ (ValLInj v) = error $ "Type annotation is required for a Left value " ++ show v ++ "!"
typeInferValue _ (ValRInj v) = error $ "Type annotation is required for a Right value " ++ show v ++ "!"
typeInferValue env (ValPair l r) = ((otype , ov), lBinds ++ rBinds) where
  lRst = (typeInferValue env l)
  rRst = (typeInferValue env r)
  lTy = fst $ fst lRst
  rTy = fst $ fst rRst
  l' = snd $ fst lRst
  r' = snd $ fst rRst
  otype = BTyProd lTy rTy
  ov = ValAnn (ValPair l' r') otype
  lBinds = snd lRst
  rBinds = snd rRst
typeInferValue env (ValAnn v ty) = typeCheckValue env v ty

typeCheckValue :: TypEnv -> Value -> BaseType -> ((BaseType, Value), [(String, BaseType)])
typeCheckValue env ValUnit ty =
  if typeEqual env BTyUnit ty
  then ((BTyUnit , ValAnn ValUnit BTyUnit) , [])
  else error $ "Expect " ++ show BTyUnit ++ ", got " ++ show ty ++ " in " ++ show TmUnit
typeCheckValue env (ValInt n) ty =
  if typeEqual env BTyInt ty
  then ((BTyInt , ValAnn (ValInt n) BTyInt) , [])
  else error $ "Expect " ++ show BTyInt ++ ", got " ++ show ty ++ " in " ++ show (TmInt n)
-- special case, Var is a pattern
typeCheckValue _ (ValVar var) ty = ((ty, ValAnn (ValVar var) ty), [(var , ty)])
typeCheckValue env (ValLInj tm) (BTySum lTy rTy) = ((otype, ov) , binds) where
  rst = typeCheckValue env tm lTy
  lTy' = fst $ fst rst
  tm' = snd $ fst rst
  otype = BTySum lTy' rTy
  ov = ValAnn (ValLInj tm') otype
  binds = snd rst
typeCheckValue env (ValRInj tm) (BTySum lTy rTy) = ((otype, ov) , binds) where
  rst = typeCheckValue env tm rTy
  rTy' = fst $ fst rst
  tm' = snd $ fst rst
  otype = BTySum lTy rTy'
  ov = ValAnn (ValRInj tm') otype
  binds = snd rst
typeCheckValue env (ValPair lhs rhs) (BTyProd lTy rTy) =
  ((otype, ov) , lBinds ++ rBinds) where
  lRst = typeCheckValue env lhs lTy
  rRst = typeCheckValue env rhs rTy
  lTy' = fst $ fst lRst
  rTy' = fst $ fst rRst
  lhs' = snd $ fst lRst
  rhs' = snd $ fst rRst
  otype = BTyProd lTy' rTy'
  ov = ValAnn (ValPair lhs' rhs') otype
  lBinds = snd lRst
  rBinds = snd rRst
typeCheckValue env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then typeCheckValue env v ty'
  else error $ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
typeCheckValue _ tm ty = error $ "Expect " ++ show tm ++ " to have type " ++ show ty

{-- Bidirectional type checking for Values (Non-pattern) --}
-- Return the type of the given value.
typeInferValueNoPattern :: TypEnv -> Value -> (BaseType , Value)
typeInferValueNoPattern _ ValUnit = (BTyUnit , ValAnn ValUnit BTyUnit)
typeInferValueNoPattern _ (ValInt n) = (BTyInt , ValAnn (ValInt n) BTyInt)
typeInferValueNoPattern env (ValVar var) = (ty , ValAnn (ValVar var) ty) where
  ty = applyBaseEnv env var
typeInferValueNoPattern _ (ValLInj v) =
  error $ "Type annotation is required for a Left value " ++ show v ++ "!"
typeInferValueNoPattern _ (ValRInj v) =
  error $ "Type annotation is required for a Right value " ++ show v ++ "!"
typeInferValueNoPattern env (ValPair l r) = (otype, ov) where
  lRst = typeInferValueNoPattern env l
  rRst = typeInferValueNoPattern env r
  lTy = fst lRst
  rTy = fst rRst
  l' = snd lRst
  r' = snd rRst
  otype = BTyProd lTy rTy
  ov = ValAnn (ValPair l' r') otype
typeInferValueNoPattern env (ValAnn v ty) = typeCheckValueNoPattern env v ty

typeCheckValueNoPattern :: TypEnv -> Value -> BaseType -> (BaseType , Value)
typeCheckValueNoPattern env ValUnit ty =
  if typeEqual env BTyUnit ty
  then (BTyUnit , ValAnn ValUnit BTyUnit)
  else error $ "Expect " ++ show BTyUnit ++ ", got " ++ show ty ++ " in " ++ show TmUnit
typeCheckValueNoPattern env (ValInt n) ty =
  if typeEqual env BTyInt ty
  then (BTyInt , ValAnn (ValInt n) BTyInt)
  else error $ "Expect " ++ show BTyInt ++ ", got " ++ show ty ++ " in " ++ show (TmInt n)
typeCheckValueNoPattern env (ValVar var) ty =
  let ty' = applyBaseEnv env var
  in if typeEqual env ty' ty
     then (ty , ValAnn (ValVar var) ty)
     else error $ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (ValVar var)
typeCheckValueNoPattern env (ValLInj tm) (BTySum lTy rTy) = (otype , ov) where
  rst = typeCheckValueNoPattern env tm lTy
  lTy' = fst rst
  tm' = snd rst
  otype = BTySum lTy' rTy
  ov = ValAnn (ValLInj tm') otype
typeCheckValueNoPattern env (ValRInj tm) (BTySum lTy rTy) = (otype , ov) where
  rst = typeCheckValueNoPattern env tm rTy
  rTy' = fst rst
  tm' = snd rst
  otype = BTySum lTy rTy'
  ov = ValAnn (ValLInj tm') otype
typeCheckValueNoPattern env (ValPair lhs rhs) (BTyProd lTy rTy) =
  (otype , ov) where
    lRst = typeCheckValueNoPattern env lhs lTy
    rRst = typeCheckValueNoPattern env rhs rTy
    lTy' = fst lRst
    rTy' = fst rRst
    lhs' = snd lRst
    rhs' = snd lRst
    otype = BTyProd lTy' rTy'
    ov = ValAnn (ValPair lhs' rhs') otype
typeCheckValueNoPattern env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then typeCheckValueNoPattern env v ty'
  else error $ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
typeCheckValueNoPattern _ tm ty =
  error $ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Exps ----------}
typeInferExp :: TypEnv -> Exp -> BaseType
typeInferExp env (ExpVal val) = fst $ typeInferValueNoPattern env val
typeInferExp env (ExpLet pat iso pat' body) =
  let isoRst = typeInferIso env iso
      isoTy = fst isoRst
  in case isoTy of
    ITyBase lT rT ->
      let rst = typeInferRhsPat env pat'
      in if typeEqual env lT rst
         then let newEnv = extendPatternEnv env pat rT
              in typeInferExp newEnv body
         else error $ "The operand " ++ show pat' ++ " has the type " ++ show rst ++ " , expect " ++ show lT
    _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"

typeCheckExp :: TypEnv -> Exp -> BaseType -> BaseType
typeCheckExp env (ExpVal val) ty = fst $ typeCheckValueNoPattern env val ty
typeCheckExp env (ExpLet pat iso pat' body) ty =
  let isoRst = typeInferIso env iso
      isoTy = fst isoRst
  in case isoTy of
    ITyBase lT rT ->
      let rst = typeInferRhsPat env pat'
      in if typeEqual env lT rst
         then let newEnv = extendPatternEnv env pat rT
              in typeCheckExp newEnv body ty
         else error $ "The operand " ++ show pat' ++ " has the type " ++ show rst ++ " , expect " ++ show lT
    _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"

typeInferRhsPat :: TypEnv -> Pattern -> BaseType
typeInferRhsPat env (PtSingleVar var) = applyBaseEnv env var
typeInferRhsPat env (PtMultiVar (var : []) ) = applyBaseEnv env var
typeInferRhsPat env (PtMultiVar (var : vars) ) = BTyProd hd tl where
  hd = applyBaseEnv env var
  tl = typeInferRhsPat env (PtMultiVar vars)
typeInferRhsPat _ pat = error $ "Invalid pattern " ++ show pat

{-------------- Helper functions --------------}
typeEqual :: TypEnv -> BaseType -> BaseType -> Bool
typeEqual _ ty ty' = (ty == ty')

applyBaseEnv :: TypEnv -> String -> BaseType
applyBaseEnv env var = case (lookup var env) of
  Just (Left bTy) -> bTy
  v -> error $ "Expect a base type for variable " ++ show var ++ ", got " ++ show v

applyIsoEnv :: TypEnv -> String -> IsoType
applyIsoEnv env var = case (lookup var env) of
  Just (Right iTy) -> iTy
  v -> error $ "Expect an iso type for variable " ++ show var ++ ", got " ++ show v

extendIsoEnv :: TypEnv -> String -> IsoType -> TypEnv
extendIsoEnv env var ty = (var, Right ty) : env

extendBaseEnv :: TypEnv -> String -> BaseType -> TypEnv
extendBaseEnv env var ty = (var , Left ty) : env

extendMultiBaseEnv :: TypEnv -> [(String , BaseType)] -> TypEnv
extendMultiBaseEnv env binds = map f binds ++ env where
  f = \x -> (fst x, Left $ snd x)

extendPatternEnv :: TypEnv -> Pattern -> BaseType -> TypEnv
extendPatternEnv env (PtSingleVar var) ty = extendBaseEnv env var ty
extendPatternEnv env (PtMultiVar vars) ty = extend env vars ty where
  extend env' (var : []) ty' = extendBaseEnv env' var ty'
  extend env' (var : vars') (BTyProd lhsTy rhsTy) =
    extend (extendBaseEnv env' var lhsTy) vars' rhsTy
  extend _ _ _ = error $ "The number of pattern variables " ++ show vars ++ " don't match the type " ++ show ty
