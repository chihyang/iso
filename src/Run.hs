module Run (run) where

import FlatParser
import Interp
import LinearCheck
import Syntax as S
import TypeCheck

run :: String -> S.Result ProgramValue
run str =
  Right str >>=
  parse >>=
  typeInfer >>=
  linearCheck >>=
  interp
