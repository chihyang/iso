module Run (check, run, runTypedMat) where

import Convert
import Debug.Trace as T (trace)
import Expand
import FlatParser
import Data.Matrix as M
import qualified Data.List as List
import Interp
import LinearCheck
import OrthoCheck
import Syntax as S
import TypeCheck

moduleName :: String
moduleName = "Run: "

check :: String -> S.Result Program
check str =
  Right str >>=
  parse >>=
  typeInfer >>=
  linearCheck

run :: String -> S.Result ProgramValue
run str = Right str >>= check >>= interp

runTypedMat :: String -> S.Result (M.Matrix Int)
runTypedMat str = do
  pg <- check str
  val <- interp pg
  matrixizePg pg val

matrixizeTypedIso :: ProgramType -> ProgramValue -> S.Result (Matrix Int)
matrixizeTypedIso (Right (ITyBase lTy rTy)) (PI (PIValBase pairs env)) = do
  lhs <- expandType lTy
  rhs <- expandType rTy
  pairs' <- applyToPairs (PIValBase pairs env) lhs
  let lhs' = map fst pairs'
  rhs' <- orthoList (map snd pairs')
  return $ matrixize (List.sort (zip lhs' rhs')) lhs rhs
matrixizeTypedIso (Left ty) (PB val) = Left $ moduleName ++ "Cannot convert a base value to matrix: " ++
  show val ++ "::" ++ show ty
matrixizeTypedIso (Right ty) (PI val) = Left $ moduleName ++ "Cannot convert an iso lambda to matrix: " ++
  show val ++ "::" ++ show ty
matrixizeTypedIso ty val = Left $ moduleName ++ "Type and value mismatch: " ++ show val ++ ", " ++ show ty

applyToPairs :: ProgramIsoValue -> [ProgramBaseValue] -> S.Result [(ProgramBaseValue , ProgramBaseValue)]
-- applyToPairs iso pairs | T.trace ("applyToPairs " ++ show iso ++ ", " ++ show pairs) False = undefined
applyToPairs _ [] = return []
applyToPairs iso (l:ls) =
  case applyIso iso l of
    Right r -> do
      pairs <- applyToPairs iso ls
      return ((l,r): pairs)
    Left _ -> applyToPairs iso ls

-- The given program must be type annotated
matrixizePg :: Program -> ProgramValue -> S.Result (Matrix Int)
matrixizePg pg val = do
  ty <- extractType pg
  matrixizeTypedIso ty val

extractType :: Program -> S.Result ProgramType
extractType (PgTm (TmAnn _ ty)) = return $ Left ty
extractType (PgIs (IsoAnn _ ty)) = return $ Right ty
extractType pg = Left $ "The given program " ++ show pg ++ " is not type annoated!"
