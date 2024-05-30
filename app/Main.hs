{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}
module Main (main) where

import qualified Command as Cmd
import qualified Repl (repl)
import System.Console.CmdArgs
import System.Environment (getArgs, withArgs)

data IsoMode = Repl
  | Eval {efile :: FilePath, output :: FilePath}
  | Matrix {mfile :: FilePath, output :: FilePath}
  | Type {tfile :: FilePath, output :: FilePath}
  deriving (Data,Typeable,Show,Eq)

repl :: IsoMode
repl = Repl &=
  help "start REPL (Default mode)"

evalFile :: IsoMode
evalFile = Eval {
  efile = def &= typFile &= argPos 0,
  output = def &= help "Write the value to the specified file" &= typFile
  } &=
  help "Evaluate a file"

evalToMatFile :: IsoMode
evalToMatFile = Matrix {
  mfile = def &= typ "FILE" &= argPos 0,
  output = def &= help "Write the matrix to the specified file" &= typFile
  } &=
  help "Evaluate a file to a matrix"

typeOf :: IsoMode
typeOf = Type {
  tfile = def &= argPos 0,
  output = def &= help "Write the type to the specified file" &= typFile
  } &=
  help "Get the type of the given program in the file"

mode :: Mode (CmdArgs IsoMode)
mode = cmdArgsMode $ modes [repl &= auto, evalFile, evalToMatFile, typeOf]
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
exec Eval{..} = Cmd.evalFile efile
exec Matrix{..} = Cmd.evalToMatrixFile mfile
exec Type{..} = Cmd.typeOfFile tfile
