module Repl
  ( repl
  ) where

import Control.Monad.IO.Class
import qualified Data.List as List
import OrthoCheck
import Run
import System.Console.Repline hiding (banner)
import System.Exit

type Repl a = HaskelineT IO a

banner :: MultiLine -> Repl String
banner MultiLine = pure " "
banner SingleLine = pure ">>> "

initial :: Repl ()
initial = liftIO $ putStrLn "Welcome to ISOCi"

final :: Repl ExitDecision
final = do
  liftIO $ putStrLn "Goodbye!"
  return Exit

commandF :: String -> Repl ()
commandF input = parseOneLine input

optionsList :: [(String , String -> Repl ())]
optionsList =
  [ ("help", help), ("h", help)
  , ("load", load), ("l", load)
  , ("matrix", toMatrix), ("m", toMatrix)
  , ("quit", quit), ("q", quit)
  ]

help :: String -> Repl ()
help = const (pure ())

load :: String -> Repl ()
load cmdStr = do
  input <- liftIO $ readFile cmdStr
  parseOneLine input

toMatrix :: String -> Repl ()
toMatrix input = case run input >>= orthoCheck >>= matrixizeIso of
  Right val -> liftIO $ print val
  Left err -> liftIO $ putStrLn err

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Leaving IsoCi."
    exitSuccess

completer :: WordCompleter IO
completer n = do
  let names = [":help", ":load", ":matrix", ":quit"]
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
parseOneLine parseThis = case run parseThis of
  Right val -> liftIO $ print val
  Left err -> liftIO $ putStrLn err
