module Repl
  ( repl
  ) where

import Control.Exception
import Control.Monad.IO.Class
import Data.Char
import qualified Data.List as List
import Run
import System.Console.Repline hiding (banner)
import System.Exit
import System.IO

type Repl a = HaskelineT IO a

trim :: String -> String
trim = List.dropWhileEnd isSpace . List.dropWhile isSpace

banner :: MultiLine -> Repl String
banner MultiLine = pure " "
banner SingleLine = pure ">>> "

initial :: Repl ()
initial = liftIO $ putStrLn "Welcome to ISOCi"

final :: Repl ExitDecision
final = do
  liftIO $ putStrLn "Leaving IsoCi."
  return Exit

commandF :: String -> Repl ()
commandF input = parseOneLine $ trim input

optionsList :: [(String , String -> Repl ())]
optionsList =
  [ ("help", help), ("h", help)
  , ("load", load), ("l", load)
  , ("matrix", toTypedMatrix), ("m", toTypedMatrix)
  , ("lm", loadMatrix)
  , ("quit", quit), ("q", quit)
  ]

help :: String -> Repl ()
help _ = liftIO $ putStrLn $
  ":help, :h              Show this information.\n" ++
  ":load file, :l file    Load a file.\n" ++
  ":matrix exp, :mt exp\n" ++
  "                       Convert the exp into a matrix according to\n" ++
  "                       its type if exp evaluates to an iso\n" ++
  ":lm file               Convert the file into a matrix according to\n" ++
  "                       its type if exp evaluates to an iso\n" ++
  ":quit, :q              Quite the program.\n"

loadFile :: String -> IO String
loadFile file =
  catch (readFile file)
  (\e -> do let err = show (e :: IOException)
            hPutStr stderr ("Warning: Couldn't open " ++ file ++ ": " ++ err)
            return "")

load :: String -> Repl ()
load cmdStr = do
  input <- liftIO $ loadFile cmdStr
  parseOneLine $ trim input

loadMatrix :: String -> Repl ()
loadMatrix cmdStr = do
  input <- liftIO $ loadFile cmdStr
  toTypedMatrix $ trim input

toTypedMatrix :: String -> Repl ()
toTypedMatrix input = case runTypedMat input of
  Right val -> liftIO $ print val
  Left err -> liftIO $ putStrLn err

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Leaving IsoCi."
    exitSuccess

completer :: WordCompleter IO
completer n = do
  let names = [":help", ":load", ":lm", ":matrix", ":matrixtyped", ":quit"]
  pure $ filter (List.isPrefixOf n) names

repl :: IO ()
repl = evalRepl
  banner
  commandF
  optionsList
  (Just ':')
  Nothing
  (Word completer)
  initial
  final

parseOneLine :: String -> Repl ()
parseOneLine "" = liftIO $ putStrLn ""
parseOneLine parseThis = case run parseThis of
  Right val -> liftIO $ print val
  Left err -> liftIO $ putStrLn err
