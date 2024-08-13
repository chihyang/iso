module OrthoCheck (unify, odCheck) where

import Convert (isUnitary)
import Data.Foldable (toList)
import Data.List (sortBy)
import Data.Sequence (Seq, Seq(Empty, (:<|), (:|>)), (<|), (><), fromList)
import Debug.Trace as T (trace)
import Data.Matrix (fromLists)
import Syntax hiding (ValEnv)

moduleName :: String
moduleName = "Orthogonal Check: "

type ValEnv = [(String, ProgramBaseValue)]

{-- A new exhaustivity check using orthogonal decomposition in the paper. --}
-- Instead of checking if a list of values is orthogonally decompositional, we
-- build a tree according to types. For each value in vals, we try to add it to
-- the existing tree. If it can be added to exactly one branch of the tree, then
-- we continue; if the branch that this value can be added has been occupied,
-- then we have a duplication error; if in the end, there are some branches in
-- this tree that haven't been occupied, then the patterns are non-exhausting.
--
-- This is a similar implementation to https://github.com/chessai/theseus.
odCheck :: (Definitions, Program) -> Result (Definitions, Program)
odCheck (defs, pgm) = do
  defs' <- odDefs defs
  pgm' <- orthoDecompose pgm
  return (defs', pgm')

odDefs :: Definitions -> Result Definitions
odDefs [] = return []
odDefs ((var,iso):ds) = do
  iso' <- odIso iso
  ds' <- odDefs ds
  return $ (var,iso'):ds'

orthoDecompose :: Program -> Result Program
orthoDecompose (PgIs iso) = do
  iso' <- odIso iso
  return $ (PgIs iso')
orthoDecompose pg = return pg

odIso :: Iso -> Result Iso
odIso (IsoAnn iso ty) = do
  iso' <- odIsoWithType ty iso
  return $ (IsoAnn iso' ty)
odIso _ = Left $ moduleName ++ "Cannot do OD check for an iso without type annotation."

odIsoWithType :: IsoType -> Iso -> Result Iso
odIsoWithType ty (IsoValue pairs) = do
  pairs' <- odPairsWithType ty pairs
  return (IsoValue pairs')
odIsoWithType _ (IsoVar var) = return (IsoVar var)
odIsoWithType _ (IsoLam var lTy rTy iso) = do
  iso' <- odIso iso
  return (IsoLam var lTy rTy iso')
odIsoWithType _ (IsoApp rator rand) = do
  rator' <- odIso rator
  rand' <- odIso rand
  return $ (IsoApp rator' rand')
odIsoWithType _ (IsoFix var lTy rTy iso) = do
  iso' <- odIso iso
  return (IsoFix var lTy rTy iso')
odIsoWithType _ (IsoAnn iso ty) = odIsoWithType ty iso

odPairsWithType :: IsoType -> [(Value, Exp)] -> Result [(Value, Exp)]
odPairsWithType (ITyBase lTy rTy) pairs = do
  vs <- odVals lTy $ map fst pairs
  es <- odExps rTy $ map snd pairs
  return $ zip vs es
odPairsWithType ty _ = Left $ moduleName ++ "Impossible case: not a base iso type: " ++ show ty

genPats :: BaseType -> Result [Value]
-- genPats ty | trace ("genPats " ++ show ty) False = undefined
genPats BTyUnit = return [ValUnit]
genPats BTyInt = return [ValInt 0, ValSuc (ValAnn (ValVar "_") BTyInt)]
genPats (BTyList ty) = return [ValEmpty, ValCons (ValAnn (ValVar "_") ty) (ValAnn (ValVar "_") (BTyList ty))]
genPats (BTySum lt rt) = return [ValLInj (ValAnn (ValVar "_") lt), ValRInj (ValAnn (ValVar "_") rt)]
genPats (BTyProd lt rt) = return [ValPair (ValAnn (ValVar "_") lt) (ValAnn (ValVar "_") rt)]
genPats (BTyMu v ty) = Left $ moduleName ++ "Unsupported iso pattern type: " ++ show (BTyMu v ty)
genPats (BTyVar v) = Left $ moduleName ++ "Unsupported iso pattern type: " ++ show (BTyVar v)

reconcile2 :: (Value -> Value -> Value) -> (Value, Value) -> (Value, Value) -> Result (Maybe ([Value], [Value]))
-- reconcile2 _ p1 p2 | trace ("reconcile2 " ++ show p1 ++ " " ++ show p2) False = undefined
reconcile2 f (v1,v1') (v2,v2') = do
  ps1 <- reconcile v1 v2
  case ps1 of
    Just ([], []) -> do
      r <- reconcile v1' v2'
      case r of
        Just (pats, vs) -> return $ Just ([f v1 p | p <- pats], [f v2 p | p <- vs])
        Nothing -> return Nothing
    Just (pats, vs) -> return $ Just ([f p v1' | p <- pats], [f p v2' | p <- vs])
    Nothing -> return Nothing

reconcile1 :: (Value -> Value) -> Value -> Value -> Result (Maybe ([Value], [Value]))
-- reconcile1 _ v1 v1' | trace ("reconcile1 " ++ show v1 ++ " " ++ show v1') False = undefined
reconcile1 f v1 v1' = do
  ps <- reconcile v1 v1'
  case ps of
    Just (pats, vs) -> return $ Just ([f p | p <- pats], [f p | p <- vs])
    Nothing -> return Nothing

reconcile :: Value -> Value -> Result (Maybe ([Value], [Value]))
-- reconcile v1 v2 | trace ("reconcile " ++ show v1 ++ " " ++ show v2) False = undefined
reconcile v1 v2 | v1 == v2 = return $ Just ([], [])
reconcile (ValAnn (ValVar _) _) (ValAnn (ValVar _) _) = return $ Just ([], [])
reconcile (ValAnn (ValVar _) ty) v = genPats ty >>= \ps -> return $ Just (ps, [v])
reconcile p (ValAnn (ValVar _) ty) = genPats ty >>= \vs -> return $ Just ([p], vs)
reconcile (ValCons v1 v1') (ValCons v2 v2') = reconcile2 ValCons (v1,v1') (v2,v2')
reconcile (ValLInj v1) (ValLInj v2) = reconcile1 ValLInj v1 v2
reconcile (ValRInj v1) (ValRInj v2) = reconcile1 ValRInj v1 v2
reconcile (ValPair v1 v1') (ValPair v2 v2') = reconcile2 ValPair (v1,v1') (v2,v2')
reconcile (ValSuc v1) (ValSuc v2) = reconcile1 ValSuc v1 v2
reconcile (ValSuc _) (ValInt 0) = return Nothing
reconcile (ValSuc v1) (ValInt n) = reconcile1 ValSuc v1 (ValInt (n-1))
reconcile (ValAnn v1 _) v2 = reconcile v1 v2
reconcile v1 (ValAnn v2 _) = reconcile v1 v2
reconcile _ _ = return Nothing

odPats :: Seq Value -> Seq Value -> Result Bool
-- odPats ps vs | trace ("odPats " ++ show ps ++ " " ++ show vs) False = undefined
odPats Empty Empty = return True
odPats ps@(_ :<| _) Empty = Left $ moduleName ++ "Missing patterns for: " ++ show (toList ps)
odPats Empty vs@(_ :<| _) = Left $ moduleName ++ "Duplicate patterns: " ++ show (toList vs)
odPats (p :<| ps) (v :<| vs) = do
  r <- reconcile p v
  case r of
    Just (ps', vs') -> odPats (ps >< (fromList ps')) (vs >< (fromList vs'))
    Nothing | ps == Empty && vs == Empty ->
              Left $ moduleName ++ "Missing patterns for: " ++ show p
    Nothing | ps == Empty -> Left $ moduleName ++ "Duplicate patterns: " ++ show (toList vs)
    Nothing | vs == Empty -> Left $ moduleName ++ "Missing patterns for: " ++ show (toList ps)
    Nothing -> odPats (ps :|> p) (v <| vs)

odVals :: BaseType -> [Value] -> Result [Value]
-- odVals ty vs | trace ("odVals " ++ show ty ++ " " ++ show vs) False = undefined
odVals ty vals = do
  pats <- genPats ty
  _ <- odPats (fromList pats) (fromList vals)
  return vals

-- For expressions, it has two modes:
--
-- 1. if no expression uses scale or plus, then all of them together compose a
-- set that needs to be checked
-- 2. if any of them uses scale and plus, then all of them must use scale or
-- plus, and they have to identical.
valOfExp :: Exp -> [(Scale, Value)]
valOfExp (ExpVal v) = [(1, eraseName v)] where
  eraseName (ValVar _) = ValVar "_"
  eraseName (ValCons v1 v2) = ValCons (eraseName v1) (eraseName v2)
  eraseName (ValLInj v1) = ValLInj (eraseName v1)
  eraseName (ValRInj v1) = ValRInj (eraseName v1)
  eraseName (ValPair v1 v2) = ValPair (eraseName v1) (eraseName v2)
  eraseName (ValAnn v1 ty) = ValAnn (eraseName v1) ty
  eraseName v1 = v1
valOfExp (ExpLet _ _ _ b) = valOfExp b
valOfExp (ExpScale s e) = map (\(s',v) -> (s'*s,v)) $ valOfExp e
valOfExp (ExpPlus es) = foldl (++) [] (map valOfExp es)

-- make sure there is no nested plus
checkPlus :: Bool -> Exp -> Result Exp
checkPlus _ (ExpVal v) = return (ExpVal v)
checkPlus b (ExpLet p i p' e) = checkPlus b e >>= return . (ExpLet p i p')
checkPlus b (ExpScale s e) = checkPlus b e >>= return . (ExpScale s)
checkPlus True (ExpPlus es) = Left $ moduleName ++ "Nested sum expressions are disallowed: " ++ show (ExpPlus es)
checkPlus False (ExpPlus es) = mapM (checkPlus True) es >>= return . ExpPlus

collectVals :: [[(Scale, Value)]] -> Result [Value]
collectVals [] = Left $ moduleName ++ "Empty clause set in an iso is meaningless!"
collectVals clauses
  | all isSingleton clauses = return $ map snd $ concat clauses
  | all sameLength clauses =
    if isSame && isUnit
    then return $ head sortedValss
    else if isSame
         then Left $ moduleName ++ "The given scales cannot compose a unitary matrix: " ++ show sortedScales
         else Left $ moduleName ++ "When using s1 * e1 + s2 * e2 + ..., " ++
              "every clause must have the same set of expressions, given " ++
              show sortedValss
  | otherwise = Left $ moduleName ++ "When using s1 * e1 + s2 * e2 + ..., " ++
    "every clause must have the same set of expressions, given " ++
    show sortedValss where
      isSingleton [_] = True
      isSingleton _ = False

      sameLength [] = True
      sameLength (vs1:vs) = all (\vs' -> length vs1 == length vs') vs

      sortCaluse vs = sortBy (\(_, a) (_, b) -> compare a b) vs

      allEqual [] = True
      allEqual (a:as) = all (\b -> a == b) as

      sortedClauses = map sortCaluse clauses
      sortedValss = map (map snd) sortedClauses
      sortedScales = map (map fst) sortedClauses

      isSame = allEqual sortedValss
      isUnit = isUnitary (fromLists sortedScales)

odExps :: BaseType -> [Exp] -> Result [Exp]
odExps ty exps = do
  exps' <- mapM (checkPlus False) exps
  let vals = map valOfExp exps'
  vs <- collectVals vals
  _ <- odVals ty vs
  return exps

{-- Given two values of the same type, try to unify them. --}
unify :: ValEnv -> ProgramBaseValue -> ProgramBaseValue -> Maybe ValEnv
unify env v1 v2 | v1 == v2 = Just env
unify env (PBValVar var) v = Just $ (var , v) : env
unify env (PBValCons v1 vs1) (PBValCons v2 vs2) = do
  env' <- unify env v1 v2
  unify env' vs1 vs2
unify env (PBValSuc v1) (PBValSuc v2) = unify env v1 v2
unify _ (PBValSuc _) (PBValInt 0) = Nothing
unify env (PBValSuc v1) (PBValInt n) = unify env v1 (PBValInt (n-1))
unify env (PBValInt n) (PBValSuc v1) = unify env (PBValSuc v1) (PBValInt n)
unify env (PBValLeft v1) (PBValLeft v2) = unify env v1 v2
unify env (PBValRight v1) (PBValRight v2) = unify env v1 v2
unify env (PBValPair l1 r1) (PBValPair l2 r2) = do
  env' <- unify env l1 l2
  unify env' r1 r2
unify env v1 (PBValVar var) = unify env (PBValVar var) v1
unify _ _ _ = Nothing
