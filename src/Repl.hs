module Repl
  ( repl
  ) where

import qualified Command as Cmd
import Control.Monad.IO.Class
import qualified Data.List as List
import System.Console.Repline as Repline hiding (banner)
import System.Exit

type Repl a = HaskelineT IO a

banner :: MultiLine -> Repl String
banner MultiLine = pure "| "
banner SingleLine = pure ">>> "

initial :: Repl ()
initial = liftIO $ putStrLn "Welcome to ISOCi"

final :: Repl ExitDecision
final = do
  liftIO $ putStrLn "Leaving IsoCi."
  return Exit

optionsList :: [(String , String -> Repl ())]
optionsList =
  [ ("help", help), ("h", help)
  , ("load", load), ("l", load)
  , ("matrix", toTypedMatrix), ("m", toTypedMatrix)
  , ("lm", loadMatrix)
  , ("lt", typeOfF), ("type", typeOfPg)
  , ("quit", quit), ("q", quit)
  ]

help :: String -> Repl ()
help _ = liftIO $ putStrLn $
  ":help, :h              Show this information.\n" ++
  ":load file, :l file    Load a file.\n" ++
  ":matrix exp, :m exp\n" ++
  "                       Convert the exp into a matrix according to\n" ++
  "                       its type if exp evaluates to an iso.\n" ++
  ":lm file               Convert the file into a matrix according to\n" ++
  "                       its type if exp evaluates to an iso or a base value.\n" ++
  ":lt file               Show the type of the program in the file.\n" ++
  ":type exp, :t exp      Show the type of the given expression.\n" ++
  ":paste                 Enter multi-line input mode.\n" ++
  ":quit, :q              Quit the program.\n"

eval :: String -> Repl ()
eval = liftIO . Cmd.eval

load :: String -> Repl ()
load = liftIO . Cmd.evalFile

typeOfF :: String -> Repl ()
typeOfF = liftIO . Cmd.typeOfFile

typeOfPg :: String -> Repl ()
typeOfPg = liftIO . Cmd.typeOf

loadMatrix :: String -> Repl ()
loadMatrix = liftIO . Cmd.evalToMatrixFile

toTypedMatrix :: String -> Repl ()
toTypedMatrix = liftIO . Cmd.evalToMatrix

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Leaving IsoCi."
    exitSuccess

completer :: WordCompleter IO
completer n = do
  let names = [":help", ":load", ":lm", ":matrix", ":m", ":lt", ":type", ":paste", ":quit"]
  pure $ filter (List.isPrefixOf n) names

prefixCompleter :: CompleterStyle IO
prefixCompleter = Repline.Prefix (wordCompleter completer)
  [(":l" , fileCompleter), (":load" , fileCompleter),
   (":lm" , fileCompleter), (":lt" , fileCompleter)]

repl :: IO ()
repl = evalRepl
  banner
  eval
  optionsList
  (Just ':')
  (Just "paste")
  prefixCompleter
  initial
  final
