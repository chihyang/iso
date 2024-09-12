module Command
  (
    compile,
    compileFile,
    eval,
    evalFile,
    evalToMatrix,
    evalToMatrixFile,
    typeOf,
    typeOfFile,
    toPerpl,
    toPerplFile
  ) where

import Control.Exception
import Control.Monad.IO.Class
import Data.Char
import qualified Data.List as List
import qualified Run
import Syntax (Result)
import System.IO

-- Commands
-- Load a file and convert it to matrix.
evalToMatrixFile :: Handle -> String -> IO ()
evalToMatrixFile = loadF evalToMatrix

-- Read a string and convert it to matrix.
evalToMatrix :: Handle -> String -> IO ()
evalToMatrix = procOneLine Run.runTypedMat

-- Load a string and evaluate its value.
eval :: Handle -> String -> IO ()
eval hdl input = parseOneLine hdl $ trim input

-- Load a file and evaluate its value.
evalFile :: Handle -> String -> IO ()
evalFile = loadF parseOneLine

-- Load a file and evaluate its value.
typeOfFile :: Handle -> String -> IO ()
typeOfFile = loadF typeOf

-- Read a string and evaluate its value.
typeOf :: Handle -> String -> IO ()
typeOf _ "" = hPutStr stderr ""
typeOf hdl parseThis = case Run.typeOf $ trim parseThis of
  Right (Left ty) -> hPrint hdl ty
  Right (Right ty) -> hPrint hdl ty
  Left err -> hPutStrLn stderr err

compile :: Handle -> String -> IO ()
compile = procOneLine Run.compile

compileFile :: Handle -> String -> IO ()
compileFile = loadF compile

toPerpl :: Handle -> String -> IO ()
toPerpl = procOneLine Run.toPerplPg

toPerplFile :: Handle -> String -> IO ()
toPerplFile = loadF toPerpl

-- Helper functions
trim :: String -> String
trim = List.dropWhileEnd isSpace . List.dropWhile isSpace

loadFile :: String -> IO String
loadFile file =
  catch (readFile file)
  (\e -> do let err = show (e :: IOException)
            hPutStrLn stderr ("Warning:" ++ err)
            return "")

loadF :: (Handle -> String -> IO ()) -> Handle -> String -> IO ()
loadF f hdl cmdStr =
  let str = trim cmdStr in
  if str == ""
  then liftIO $ putStrLn "File name required!"
  else do
    input <- liftIO $ loadFile $ trim str
    f hdl input

parseOneLine :: Handle -> String -> IO ()
parseOneLine = procOneLine Run.run

procOneLine :: Show a => (String -> Result a) -> Handle -> String -> IO ()
procOneLine _ _ "" = hPutStr stderr ""
procOneLine f hdl parseThis = case f parseThis of
  Right val -> hPrint hdl $ val
  Left err -> hPutStrLn stderr err
