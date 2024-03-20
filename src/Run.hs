module Run (run, matrixizeIso) where

import Convert
import Data.Matrix as M
import Data.List
import Expand
import FlatParser
import Interp
import LinearCheck
import OrthoCheck
import Syntax as S
import TypeCheck

moduleName :: String
moduleName = "Run: "

run :: String -> S.Result ProgramValue
run str =
  Right str >>=
  parse >>=
  typeInfer >>=
  linearCheck >>=
  interp

matrixizeIso :: ProgramValue -> S.Result (M.Matrix Int)
matrixizeIso (PI (PIValBase pairs _)) = return $ matrixize $ sort pairs
matrixizeIso (PB val) = Left $ moduleName ++ "Cannot convert a base value to matrix: " ++ show val
matrixizeIso (PI val) = Left $ moduleName ++ "Cannot convert an iso lambda to matrix: " ++ show val
