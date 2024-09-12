module Repl
  ( repl
  ) where

import qualified Command as Cmd
import Control.Monad.IO.Class
import qualified Data.List as List
import System.Console.Repline as Repline hiding (banner)
import System.Exit
import System.IO

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
  , ("lp", toPerplF), ("perpl", toPerpl)
  , ("lc", compileF), ("compile", compile)
  , ("quit", quit), ("q", quit)
  ]

help :: String -> Repl ()
help _ = liftIO $ putStrLn $
  ":l file, :load file    Load a file.\n" ++
  ":lm file               Convert the file into a matrix according to\n" ++
  "                       its type if exp evaluates to an iso or a base value.\n" ++
  ":lt file               Show the type of the program in the file.\n" ++
  ":lp file               Convert the file to an equivalent perpl program.\n" ++
  ":c exp, :lc file        [For debugging] Compile the file or expression.\n" ++
  ":m exp, :matrix exp\n" ++
  "                       Convert the exp into a matrix according to\n" ++
  "                       its type if exp evaluates to an iso.\n" ++
  ":t exp, :type exp      Show the type of the given expression.\n" ++
  ":perpl exp             Convert the exp to an equivalent perpl program.\n" ++
  ":paste                 Enter multi-line input mode.\n" ++
  ":h, :help              Show this information.\n" ++
  ":q, :quit              Quit the program.\n"

eval :: String -> Repl ()
eval = liftIO . Cmd.eval stdout

load :: String -> Repl ()
load = liftIO . Cmd.evalFile stdout

typeOfF :: String -> Repl ()
typeOfF = liftIO . Cmd.typeOfFile stdout

typeOfPg :: String -> Repl ()
typeOfPg = liftIO . Cmd.typeOf stdout

loadMatrix :: String -> Repl ()
loadMatrix = liftIO . Cmd.evalToMatrixFile stdout

toTypedMatrix :: String -> Repl ()
toTypedMatrix = liftIO . Cmd.evalToMatrix stdout

compile :: String -> Repl ()
compile = liftIO . Cmd.compile stdout

compileF :: String -> Repl ()
compileF = liftIO . Cmd.compileFile stdout

toPerpl :: String -> Repl ()
toPerpl = liftIO . Cmd.toPerpl stdout

toPerplF :: String -> Repl ()
toPerplF = liftIO . Cmd.toPerplFile stdout

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Leaving IsoCi."
    exitSuccess

completer :: WordCompleter IO
completer n = do
  let names = [":help", ":load", ":lc", ":lm", ":lp", ":lt", ":compile", ":matrix", ":m", ":type", ":paste", ":perpl", ":quit"]
  pure $ filter (List.isPrefixOf n) names

prefixCompleter :: CompleterStyle IO
prefixCompleter = Repline.Prefix (wordCompleter completer)
  [(":l" , fileCompleter), (":load" , fileCompleter),
   (":lm" , fileCompleter), (":lt" , fileCompleter),
   (":lp" , fileCompleter), (":lc" , fileCompleter)
  ]

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
