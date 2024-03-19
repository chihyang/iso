module TypeCheck (typeInfer) where

import Syntax

typeInfer :: TypEnv -> Program -> Program
typeInfer env (PgTm tm) = PgTm $ snd $ tiTm env tm
typeInfer env (PgIs iso) = PgIs $ snd $ tiIso env iso

{---------- Bidirectional type checking for Terms ----------}
-- Return a type annotated term together with its type.
tiTm :: TypEnv -> Term -> (BaseType, Term)
tiTm _ TmUnit = (BTyUnit , TmAnn TmUnit BTyUnit)
tiTm _ (TmInt n) = (BTyInt , TmAnn (TmInt n) BTyInt)
tiTm env (TmVar var) = (ty , TmAnn (TmVar var) ty) where
  ty = applyBaseEnv env var
tiTm _ (TmLInj tm) = error $ "Type annotation is required for the term " ++ show (TmLInj tm)
tiTm _ (TmRInj tm) = error $ "Type annotation is required for the term " ++ show (TmLInj tm)
tiTm env (TmPair l r) = (oType , TmAnn (TmPair lTm rTm) oType)  where
  rstL = tiTm env l
  rstR = tiTm env r
  lTy = fst rstL
  rTy = fst rstR
  lTm = snd rstL
  rTm = snd rstR
  oType = (BTyProd lTy rTy)
tiTm env (TmIsoApp iso tm) =
  let isoRst = tiIso env iso
      isoTy = fst isoRst
      iso' = snd isoRst
  in case isoTy of
    ITyBase lT rT ->
      let rst = tcTm env tm lT
          argType = fst rst
          tm' = snd rst
      in if typeEqual env lT argType
         then (rT , (TmAnn (TmIsoApp iso' tm') rT))
         else error $ "The operand " ++ show tm ++ " has the type " ++ show argType ++ " , expect " ++ show lT
    _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"
tiTm env (TmLet pat rhs body) = (bodyTy , TmAnn (TmLet pat rhs' body') bodyTy) where
  rhsRst = tiTm env rhs
  rhsTy = fst rhsRst
  rhs' = snd rhsRst
  newEnv = extPatEnv env pat rhsTy
  bodyRst = tiTm newEnv body
  bodyTy = fst bodyRst
  body' = snd bodyRst
tiTm env (TmAnn tm ty) = tcTm env tm ty

tcTm :: TypEnv -> Term -> BaseType -> (BaseType, Term)
tcTm env TmUnit ty =
  if typeEqual env BTyUnit ty
  then (BTyUnit , TmAnn TmUnit BTyUnit)
  else error $ "Expect " ++ show BTyUnit ++ ", got " ++ show ty ++ " in " ++ show TmUnit
tcTm env (TmInt n) ty =
  if typeEqual env BTyInt ty
  then (BTyInt , TmAnn (TmInt n) BTyInt)
  else error $ "Expect " ++ show BTyInt ++ ", got " ++ show ty ++ " in " ++ show (TmInt n)
tcTm env (TmVar var) ty =
  let ty' = applyBaseEnv env var
  in if typeEqual env ty' ty
     then (ty, TmAnn (TmVar var) ty)
     else error $ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (TmVar var)
tcTm env (TmLInj tm) (BTySum lTy rTy) = (rstTy , TmAnn (TmLInj tm') rstTy) where
  rst = tcTm env tm lTy
  tm' = snd rst
  rstTy = BTySum lTy rTy
tcTm env (TmRInj tm) (BTySum lTy rTy) =  (rstTy , TmAnn (TmRInj tm') rstTy) where
  rst = tcTm env tm rTy
  tm' = snd rst
  rstTy = BTySum lTy rTy
tcTm env (TmPair lhs rhs) (BTyProd lTy rTy) =
  (oType , (TmAnn (TmPair lhs' rhs') oType)) where
    lRst = tcTm env lhs lTy
    rRst = tcTm env rhs rTy
    lhs' = snd lRst
    rhs' = snd rRst
    oType = (BTyProd lTy rTy)
tcTm env (TmIsoApp iso tm) ty =
  let isoRst = tiIso env iso
      isoTy = fst isoRst
      iso' = snd isoRst
  in case isoTy of
       ITyBase lT rT ->
         let rst = tcTm env tm lT
             argType = fst rst
             tm' = snd rst
         in if typeEqual env lT argType
            then if typeEqual env rT ty
                 then (ty , (TmAnn (TmIsoApp iso' tm') ty))
                 else error $ "The return " ++ show (TmIsoApp iso tm) ++
                      " has the type " ++ show rT ++ " , expect " ++ show ty
            else error $ "The operand " ++ show tm ++ " has the type " ++ show argType ++ " , expect " ++ show lT
       _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"
tcTm env (TmLet pat rhs body) ty = (ty , TmAnn (TmLet pat rhs' body') ty) where
  rhsRst = tiTm env rhs
  rhsTy = fst rhsRst
  rhs' = snd rhsRst
  newEnv = extPatEnv env pat rhsTy
  bodyRst = tcTm newEnv body ty
  body' = snd bodyRst
tcTm env (TmAnn tm ty) ty' =
  if typeEqual env ty ty'
  then tcTm env tm ty'
  else error $ "Expect " ++ show tm ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcTm _ tm ty = error $ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Isos ----------}
tiIso :: TypEnv -> Iso -> (IsoType, Iso)
tiIso env (IsoValue pairs) = (otype , ov) where
  otype = tiIsoPairs env pairs
  ov = IsoAnn (IsoValue pairs) otype
tiIso env (IsoVar var) = (otype , ov) where
  otype = applyIsoEnv env var
  ov = IsoAnn (IsoVar var) otype
tiIso env (IsoLam var vLhsTy vRhsTy body) = (otype , ov) where
  newEnv = extIsoEnv env var (ITyBase vLhsTy vRhsTy)
  rst = tiIso newEnv body
  bodyTy = fst rst
  body' = snd rst
  otype = ITyFun vLhsTy vRhsTy bodyTy
  ov = IsoAnn (IsoLam var vLhsTy vRhsTy body') otype
tiIso env (IsoApp rator rand) =
  let ratorRst = tiIso env rator
      ratorTy = fst ratorRst
      rator' = snd ratorRst
  in let randRst = tiIso env rand
         randTy = fst randRst
         rand' = snd randRst
     in case (ratorTy , randTy) of
          (ITyFun lhsTy rhsTy bodyTy, ITyBase randLhsTy randRhsTy) ->
            if typeEqual env lhsTy randLhsTy && typeEqual env rhsTy randRhsTy
            then (bodyTy , IsoAnn (IsoApp rator' rand') bodyTy)
            else error $ "Expect " ++ show rator ++ " and " ++ show rand  ++ " to have matched type!"
          (_, _) -> error $ "Expect " ++ show rator ++ " to have the type (Iso -> Iso)!"
tiIso _ (IsoFix _ _) = error $ "IsoFix is not supported yet!"
tiIso _ (IsoAnn _ _) = error $ "IsoAnn is an internal node!"

tiIsoPairs :: TypEnv -> [(Value, Exp)] -> IsoType
tiIsoPairs _ [] = error $ "There must be at least one pair of values in an iso, given zero!"
tiIsoPairs env (hd:tl) = tcIsoPairs env tl lhsTy rhsTy where
  ty = tiIsoPair env hd
  lhsTy = fst ty
  rhsTy = snd ty

tcIsoPairs :: TypEnv -> [(Value, Exp)] -> BaseType -> BaseType -> IsoType
tcIsoPairs _ [] lhsTy rhsTy = ITyBase lhsTy rhsTy
tcIsoPairs env (hd:tl) lhsTy rhsTy =
  tcIsoPairs env tl lhsTy' rhsTy' where
    rst = tcIsoPair env hd lhsTy rhsTy
    lhsTy' = fst rst
    rhsTy' = snd rst

tiIsoPair :: TypEnv -> (Value, Exp) -> (BaseType, BaseType)
tiIsoPair env (lhs, rhs) = (lTy , rTy) where
  lRst = tiValue env lhs
  lTy = fst $ fst lRst
  lBinds = snd lRst
  newEnv = extMultiBaseEnv env lBinds
  rTy = tiExp newEnv rhs

tcIsoPair :: TypEnv -> (Value, Exp) -> BaseType -> BaseType -> (BaseType, BaseType)
tcIsoPair env (lhs , rhs) lTy rTy = (lTy' , rTy') where
  lRst = tcVal env lhs lTy
  lTy' = fst $ fst lRst
  lBinds = snd lRst
  newEnv = extMultiBaseEnv env lBinds
  rTy' = tcExp newEnv rhs rTy

{---------- Bidirectional type checking for Values -----------}
-- Return the type of the given value, the type annotated value, and all pattern
-- variables and the corresponding type in this value.
tiValue :: TypEnv -> Value -> ((BaseType, Value), [(String, BaseType)])
tiValue _ ValUnit = ((BTyUnit, ValAnn ValUnit BTyUnit) , [])
tiValue _ (ValInt n) = ((BTyInt, ValAnn (ValInt n) BTyInt) , [])
tiValue _ (ValVar var) = error $ "Type annotation is required for a single pattern var " ++ var ++ "!"
tiValue _ (ValLInj v) = error $ "Type annotation is required for a Left value " ++ show v ++ "!"
tiValue _ (ValRInj v) = error $ "Type annotation is required for a Right value " ++ show v ++ "!"
tiValue env (ValPair l r) = ((otype , ov), lBinds ++ rBinds) where
  lRst = (tiValue env l)
  rRst = (tiValue env r)
  lTy = fst $ fst lRst
  rTy = fst $ fst rRst
  l' = snd $ fst lRst
  r' = snd $ fst rRst
  otype = BTyProd lTy rTy
  ov = ValAnn (ValPair l' r') otype
  lBinds = snd lRst
  rBinds = snd rRst
tiValue env (ValAnn v ty) = tcVal env v ty

tcVal :: TypEnv -> Value -> BaseType -> ((BaseType, Value), [(String, BaseType)])
tcVal env ValUnit ty =
  if typeEqual env BTyUnit ty
  then ((BTyUnit , ValAnn ValUnit BTyUnit) , [])
  else error $ "Expect " ++ show BTyUnit ++ ", got " ++ show ty ++ " in " ++ show TmUnit
tcVal env (ValInt n) ty =
  if typeEqual env BTyInt ty
  then ((BTyInt , ValAnn (ValInt n) BTyInt) , [])
  else error $ "Expect " ++ show BTyInt ++ ", got " ++ show ty ++ " in " ++ show (TmInt n)
-- special case, Var is a pattern
tcVal _ (ValVar var) ty = ((ty, ValAnn (ValVar var) ty), [(var , ty)])
tcVal env (ValLInj tm) (BTySum lTy rTy) = ((otype, ov) , binds) where
  rst = tcVal env tm lTy
  lTy' = fst $ fst rst
  tm' = snd $ fst rst
  otype = BTySum lTy' rTy
  ov = ValAnn (ValLInj tm') otype
  binds = snd rst
tcVal env (ValRInj tm) (BTySum lTy rTy) = ((otype, ov) , binds) where
  rst = tcVal env tm rTy
  rTy' = fst $ fst rst
  tm' = snd $ fst rst
  otype = BTySum lTy rTy'
  ov = ValAnn (ValRInj tm') otype
  binds = snd rst
tcVal env (ValPair lhs rhs) (BTyProd lTy rTy) =
  ((otype, ov) , lBinds ++ rBinds) where
  lRst = tcVal env lhs lTy
  rRst = tcVal env rhs rTy
  lTy' = fst $ fst lRst
  rTy' = fst $ fst rRst
  lhs' = snd $ fst lRst
  rhs' = snd $ fst rRst
  otype = BTyProd lTy' rTy'
  ov = ValAnn (ValPair lhs' rhs') otype
  lBinds = snd lRst
  rBinds = snd rRst
tcVal env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then tcVal env v ty'
  else error $ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcVal _ tm ty = error $ "Expect " ++ show tm ++ " to have type " ++ show ty

{-- Bidirectional type checking for Values (Non-pattern) --}
-- Return the type of the given value.
tiValNoPat :: TypEnv -> Value -> (BaseType , Value)
tiValNoPat _ ValUnit = (BTyUnit , ValAnn ValUnit BTyUnit)
tiValNoPat _ (ValInt n) = (BTyInt , ValAnn (ValInt n) BTyInt)
tiValNoPat env (ValVar var) = (ty , ValAnn (ValVar var) ty) where
  ty = applyBaseEnv env var
tiValNoPat _ (ValLInj v) =
  error $ "Type annotation is required for a Left value " ++ show v ++ "!"
tiValNoPat _ (ValRInj v) =
  error $ "Type annotation is required for a Right value " ++ show v ++ "!"
tiValNoPat env (ValPair l r) = (otype, ov) where
  lRst = tiValNoPat env l
  rRst = tiValNoPat env r
  lTy = fst lRst
  rTy = fst rRst
  l' = snd lRst
  r' = snd rRst
  otype = BTyProd lTy rTy
  ov = ValAnn (ValPair l' r') otype
tiValNoPat env (ValAnn v ty) = tcValNoPat env v ty

tcValNoPat :: TypEnv -> Value -> BaseType -> (BaseType , Value)
tcValNoPat env ValUnit ty =
  if typeEqual env BTyUnit ty
  then (BTyUnit , ValAnn ValUnit BTyUnit)
  else error $ "Expect " ++ show BTyUnit ++ ", got " ++ show ty ++ " in " ++ show TmUnit
tcValNoPat env (ValInt n) ty =
  if typeEqual env BTyInt ty
  then (BTyInt , ValAnn (ValInt n) BTyInt)
  else error $ "Expect " ++ show BTyInt ++ ", got " ++ show ty ++ " in " ++ show (TmInt n)
tcValNoPat env (ValVar var) ty =
  let ty' = applyBaseEnv env var
  in if typeEqual env ty' ty
     then (ty , ValAnn (ValVar var) ty)
     else error $ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (ValVar var)
tcValNoPat env (ValLInj tm) (BTySum lTy rTy) = (otype , ov) where
  rst = tcValNoPat env tm lTy
  lTy' = fst rst
  tm' = snd rst
  otype = BTySum lTy' rTy
  ov = ValAnn (ValLInj tm') otype
tcValNoPat env (ValRInj tm) (BTySum lTy rTy) = (otype , ov) where
  rst = tcValNoPat env tm rTy
  rTy' = fst rst
  tm' = snd rst
  otype = BTySum lTy rTy'
  ov = ValAnn (ValLInj tm') otype
tcValNoPat env (ValPair lhs rhs) (BTyProd lTy rTy) =
  (otype , ov) where
    lRst = tcValNoPat env lhs lTy
    rRst = tcValNoPat env rhs rTy
    lTy' = fst lRst
    rTy' = fst rRst
    lhs' = snd lRst
    rhs' = snd lRst
    otype = BTyProd lTy' rTy'
    ov = ValAnn (ValPair lhs' rhs') otype
tcValNoPat env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then tcValNoPat env v ty'
  else error $ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcValNoPat _ tm ty =
  error $ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Exps ----------}
tiExp :: TypEnv -> Exp -> BaseType
tiExp env (ExpVal val) = fst $ tiValNoPat env val
tiExp env (ExpLet pat iso pat' body) =
  let isoRst = tiIso env iso
      isoTy = fst isoRst
  in case isoTy of
    ITyBase lT rT ->
      let rst = tiRhsPat env pat'
      in if typeEqual env lT rst
         then let newEnv = extPatEnv env pat rT
              in tiExp newEnv body
         else error $ "The operand " ++ show pat' ++ " has the type " ++ show rst ++ " , expect " ++ show lT
    _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"

tcExp :: TypEnv -> Exp -> BaseType -> BaseType
tcExp env (ExpVal val) ty = fst $ tcValNoPat env val ty
tcExp env (ExpLet pat iso pat' body) ty =
  let isoRst = tiIso env iso
      isoTy = fst isoRst
  in case isoTy of
    ITyBase lT rT ->
      let rst = tiRhsPat env pat'
      in if typeEqual env lT rst
         then let newEnv = extPatEnv env pat rT
              in tcExp newEnv body ty
         else error $ "The operand " ++ show pat' ++ " has the type " ++ show rst ++ " , expect " ++ show lT
    _ -> error $ "The operator " ++ show iso ++ " should be an IsoBase!"

tiRhsPat :: TypEnv -> Pattern -> BaseType
tiRhsPat env (PtSingleVar var) = applyBaseEnv env var
tiRhsPat env (PtMultiVar (var : []) ) = applyBaseEnv env var
tiRhsPat env (PtMultiVar (var : vars) ) = BTyProd hd tl where
  hd = applyBaseEnv env var
  tl = tiRhsPat env (PtMultiVar vars)
tiRhsPat _ pat = error $ "Invalid pattern " ++ show pat

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

extIsoEnv :: TypEnv -> String -> IsoType -> TypEnv
extIsoEnv env var ty = (var, Right ty) : env

extBaseEnv :: TypEnv -> String -> BaseType -> TypEnv
extBaseEnv env var ty = (var , Left ty) : env

extMultiBaseEnv :: TypEnv -> [(String , BaseType)] -> TypEnv
extMultiBaseEnv env binds = map f binds ++ env where
  f = \x -> (fst x, Left $ snd x)

extPatEnv :: TypEnv -> Pattern -> BaseType -> TypEnv
extPatEnv env (PtSingleVar var) ty = extBaseEnv env var ty
extPatEnv env (PtMultiVar vars) ty = extend env vars ty where
  extend env' (var : []) ty' = extBaseEnv env' var ty'
  extend env' (var : vars') (BTyProd lhsTy rhsTy) =
    extend (extBaseEnv env' var lhsTy) vars' rhsTy
  extend _ _ _ = error $ "The number of pattern variables " ++ show vars ++ " don't match the type " ++ show ty
