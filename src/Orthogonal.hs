module Orthogonal (ortho, orthoPairs) where

import Syntax hiding (ValEnv)

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
unify env (PBValLeft v1) (PBValLeft v2) = unify env v1 v2
unify env (PBValRight v1) (PBValRight v2) = unify env v1 v2
unify env (PBValPair l1 r1) (PBValPair l2 r2) = do {
  env' <- unify env l1 l2
  ; unify env' r1 r2
  }
unify env v1 (PBValVar var) = unify env (PBValVar var) v1
unify _ _ _ = Nothing

isOrtho :: ValEnv -> ProgramBaseValue -> ProgramBaseValue -> Bool
isOrtho env v1 v2 =
  let v1' = find env v1
      v2' = find env v2
  in case unify env v1' v2' of
       Just _ -> False
       Nothing -> True

ortho :: ProgramBaseValue -> ProgramBaseValue -> Bool
ortho v1 v2 = isOrtho [] v1 v2

orthoLst1 :: ProgramBaseValue -> [ProgramBaseValue] -> Bool
orthoLst1 v vs = foldl (\rst v' -> rst && ortho v v') True vs

orthoLst :: [ProgramBaseValue] -> Bool
orthoLst [] = True
orthoLst (v:vs) =
  if orthoLst1 v vs
  then orthoLst vs
  else False

orthoPairs :: [(ProgramBaseValue, ProgramBaseValue)] -> Bool
orthoPairs pairs = orthoLst lhs && orthoLst rhs where
  lhs = map fst pairs
  rhs = map snd pairs
