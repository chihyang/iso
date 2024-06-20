module Command
  (
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
import System.IO

-- Commands
-- Load a file and convert it to matrix.
evalToMatrixFile :: String -> IO ()
evalToMatrixFile = loadF evalToMatrix

-- Read a string and convert it to matrix.
evalToMatrix :: String -> IO ()
evalToMatrix input = case Run.runTypedMat $ trim input of
  Right val -> print val
  Left err -> putStrLn err

-- Load a file and evaluate its value.
eval :: String -> IO ()
eval input = parseOneLine $ trim input

-- Load a file and evaluate its value.
evalFile :: String -> IO ()
evalFile = loadF parseOneLine

-- Load a file and evaluate its value.
typeOfFile :: String -> IO ()
typeOfFile = loadF typeOf

-- Read a string and evaluate its value.
typeOf :: String -> IO ()
typeOf parseThis = case Run.typeOf $ trim parseThis of
  Right (Left ty) -> print ty
  Right (Right ty) -> print ty
  Left err -> putStrLn err

toPerpl :: String -> IO ()
toPerpl parseThis = case Run.toPerplPg $ trim parseThis of
  Right r -> print r
  Left err -> putStrLn err

toPerplFile :: String -> IO ()
toPerplFile = loadF toPerpl

-- Helper functions
trim :: String -> String
trim = List.dropWhileEnd isSpace . List.dropWhile isSpace

loadFile :: String -> IO String
loadFile file =
  catch (readFile file)
  (\e -> do let err = show (e :: IOException)
            hPutStr stderr ("Warning: Couldn't open " ++ file ++ ": " ++ err)
            return "")

loadF :: (String -> IO ()) -> String -> IO ()
loadF f cmdStr =
  let str = trim cmdStr in
  if str == ""
  then liftIO $ putStrLn "File name required!"
  else do
    input <- liftIO $ loadFile $ trim str
    f $ input

parseOneLine :: String -> IO ()
parseOneLine "" = putStrLn ""
parseOneLine parseThis = case Run.run parseThis of
  Right val -> print val
  Left err -> putStrLn err
