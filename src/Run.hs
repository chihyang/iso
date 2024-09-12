module Run (check, typeOf, run, runTypedMat, toPerplPg, compile) where

import Convert
import Debug.Trace as T (trace)
import Expand
import FlatParser
import Data.Matrix as M
import qualified Data.List as List
import Interp
import LinearCheck
import OrthoCheck
import Reduce
import RevealFix
import ClosureConvert
import Syntax as S
import Translate
import TypeCheck
import Uniquify

moduleName :: String
moduleName = "Run: "

check :: String -> S.Result (Definitions, Program)
check str =
  Right str >>=
  parseDefsPg >>=
  foldDefsPg >>=
  typeInferDefsPg >>=
  linearCheckDefsPg >>=
  odCheck

run :: String -> S.Result ProgramValue
run str = Right str >>= check >>= interpDefsPg

-- for debugging
compile :: String -> S.Result (Definitions, Program)
compile str = Right str >>= check >>= uniquify >>= closureConvert

toPerplPg :: String -> S.Result PProg
toPerplPg str = compile str >>= transToPerplPg

typeOf :: String -> S.Result ProgramType
typeOf str = do
  (_, pg) <- check str
  typeOfPg pg where
    typeOfPg (PgTm (TmAnn _ ty)) = return $ Left ty
    typeOfPg (PgIs (IsoAnn _ ty)) = return $ Right ty
    typeOfPg _ = Left $ moduleName ++ "Failed to get the type of the program!"

runTypedMat :: String -> S.Result (M.Matrix Scale)
runTypedMat str = do
  (defs, pg) <- check str
  val <- interpDefsPg (defs, pg)
  matrixizePg pg val

matrixizeTypedIso :: ProgramType -> ProgramValue -> S.Result (Matrix Scale)
-- matrixizeTypedIso ty v | T.trace ("matrixizeTypedIso " ++ show ty ++ " " ++ show v) False = undefined
matrixizeTypedIso (Right (ITyBase lTy rTy)) (PI (PIValBase pairs env)) = do
  lhs <- expandType lTy
  rhs <- expandType rTy
  pairs' <- applyToPairs (PIValBase pairs env) lhs
  let rhs' = map snd pairs'
  return $ matrixizeScale rhs' rhs
matrixizeTypedIso (Left ty) (PB val) = do
  vals <- expandType ty
  return $ matrixize (List.sort vals) val
matrixizeTypedIso (Left ty) (PQ vals) = do
  allVals <- expandType ty
  return $ matrixizeEntangled vals allVals
matrixizeTypedIso (Right ty) (PI val) = Left $ moduleName ++ "Cannot convert an iso lambda to matrix: " ++
  show val ++ "::" ++ show ty
matrixizeTypedIso ty val = Left $ moduleName ++ "Type and value mismatch: " ++ show val ++ ", " ++ show ty

applyToPairs :: ProgramIsoValue -> [ProgramBaseValue] -> S.Result [(ProgramBaseValue , EntangledValue)]
-- applyToPairs iso pairs | T.trace ("applyToPairs " ++ show iso ++ ", " ++ show pairs) False = undefined
applyToPairs _ [] = return []
applyToPairs iso (l:ls) =
  case applyIso iso [(1, l)] of
    Right r -> do
      pairs <- applyToPairs iso ls
      return ((l,r): pairs)
    Left _ -> applyToPairs iso ls

-- The given program must be type annotated
matrixizePg :: Program -> ProgramValue -> S.Result (Matrix Scale)
matrixizePg pg val = do
  ty <- extractType pg
  matrixizeTypedIso ty val

extractType :: Program -> S.Result ProgramType
extractType (PgTm (TmAnn _ ty)) = return $ Left ty
extractType (PgIs (IsoAnn _ ty)) = return $ Right ty
extractType pg = Left $ "The given program " ++ show pg ++ " is not type annoated!"
