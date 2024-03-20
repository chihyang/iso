module Run where

import Convert
import Expand
import FlatParser
import Interp
import LinearCheck
import OrthoCheck
import Syntax as S
import TypeCheck

run :: String -> S.Result ProgramValue
run str =
  Right str >>=
  parse >>=
  typeInfer >>=
  linearCheck >>=
  interp
