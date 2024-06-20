{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}
module Main (main) where

import qualified Command as Cmd
import qualified Repl (repl)
import System.Console.CmdArgs

data IsoMode = Repl
  | Eval {input :: FilePath, output :: FilePath}
  | Matrix {input :: FilePath, output :: FilePath}
  | Type {input :: FilePath, output :: FilePath}
  | Perpl {input :: FilePath, output :: FilePath}
  deriving (Data,Typeable,Show,Eq)

repl :: IsoMode
repl = Repl &=
  help "start REPL (Default mode)"

evalFile :: IsoMode
evalFile = Eval {
  input = def &= typ "<ISO to eval>" &= argPos 0,
  output = def &= help "Write the value to the specified file" &= typ "TEXT"
  } &=
  help "Evaluate a file"

evalToMatFile :: IsoMode
evalToMatFile = Matrix {
  input = def &= typ "<ISO to convert>" &= argPos 0,
  output = def &= help "Write the matrix to the specified file" &= typ "TEXT"
  } &=
  help "Evaluate a file to a matrix"

typeOf :: IsoMode
typeOf = Type {
  input = def &= typ "<ISO to type infer>" &= argPos 0,
  output = def &= help "Write the type to the specified file" &= typ "TEXT"
  } &=
  help "Get the type of the given program in the file"

toPerpl :: IsoMode
toPerpl = Perpl {
  input = def &= typ "<ISO to translate>" &= argPos 0,
  output = def &= help "Write the FGG to the specified file" &= typ "TEXT"
  } &=
  help "Convert the given file to FGG"

mode :: Mode (CmdArgs IsoMode)
mode = cmdArgsMode $ modes [repl &= auto, evalFile, evalToMatFile, typeOf, toPerpl]
  &= help "Iso command line tool"
  &= program "iso"
  &= summary "Iso v0.0.1"

main :: IO ()
main = do
  opts <- cmdArgsRun mode
  optionHandler opts

optionHandler :: IsoMode -> IO ()
optionHandler opts = exec opts

exec :: IsoMode -> IO ()
exec Repl = Repl.repl
exec Eval{..} = Cmd.evalFile input
exec Matrix{..} = Cmd.evalToMatrixFile input
exec Type{..} = Cmd.typeOfFile input
exec Perpl{..} = Cmd.toPerplFile input
