module OrthoCheck (unify, ortho, orthoList, orthoPairs) where

import Debug.Trace as T (trace)
import Syntax hiding (ValEnv)

moduleName :: String
moduleName = "Orthogonal Check: "

type ValEnv = [(String, ProgramBaseValue)]

find :: ValEnv -> ProgramBaseValue -> ProgramBaseValue
find env (PBValVar var) =
  case lookup var env of
    Just val -> find env val
    Nothing -> PBValVar var
find _ val = val

{-- Given two values of the same type, try to unify them. --}
unify :: ValEnv -> ProgramBaseValue -> ProgramBaseValue -> Maybe ValEnv
unify env v1 v2 | v1 == v2 = Just env
unify env (PBValVar var) v = Just $ (var , v) : env
unify env (PBValCons v1 vs1) (PBValCons v2 vs2) = do
  env' <- unify env v1 v2
  unify env' vs1 vs2
unify env (PBValLeft v1) (PBValLeft v2) = unify env v1 v2
unify env (PBValRight v1) (PBValRight v2) = unify env v1 v2
unify env (PBValPair l1 r1) (PBValPair l2 r2) = do
  env' <- unify env l1 l2
  unify env' r1 r2
unify env v1 (PBValVar var) = unify env (PBValVar var) v1
unify _ _ _ = Nothing

orthoEnv :: ValEnv -> ProgramBaseValue -> ProgramBaseValue -> Result ProgramBaseValue
orthoEnv env v1 v2 =
  let v1' = find env v1
      v2' = find env v2
  in case unify env v1' v2' of
       Just _ -> Left $ moduleName ++ "Value " ++ show v1 ++ " and " ++ show v2 ++ " overlap!"
       Nothing -> return v1

ortho :: ProgramBaseValue -> ProgramBaseValue -> Result ProgramBaseValue
ortho v1 v2 = orthoEnv [] v1 v2

orthoLst1 :: ProgramBaseValue -> [ProgramBaseValue] -> Result ProgramBaseValue
orthoLst1 v [] = return v
orthoLst1 v (v1:v1s) = do
  v' <- ortho v v1
  orthoLst1 v' v1s

orthoList :: [ProgramBaseValue] -> Result [ProgramBaseValue]
-- orthoList v | T.trace ("orthoList " ++ show v) False = undefined
orthoList [] = return []
orthoList (v:vs) = do
  v' <- orthoLst1 v vs
  vs' <- orthoList vs
  return (v':vs')

orthoPairs :: [(ProgramBaseValue, ProgramBaseValue)] -> Result [(ProgramBaseValue, ProgramBaseValue)]
-- orthoPairs pairs | T.trace ("orthoPairs " ++ show pairs) False = undefined
orthoPairs pairs = do
  let lhs = map fst pairs
  let rhs = map snd pairs
  lhs' <- orthoList lhs
  rhs' <- orthoList rhs
  return $ zip lhs' rhs'
