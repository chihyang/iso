module Repl
  ( repl
  ) where

import System.Console.Repline hiding (banner)
import Control.Monad.IO.Class
import Data.List
import System.Exit

import FlatParser (parse, Result(..))
import qualified Data.ByteString as Byte

type Repl a = HaskelineT IO a

data Line = Load FilePath | BadCmd

parseCommand :: [String] -> Line
parseCommand ["load", f] = Load f
parseCommand _ = BadCmd

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
  -- , ("load", load), ("l", load)
  , ("quit", quit), ("q", quit)
  ]

help :: String -> Repl ()
help = const (pure ())

-- load :: [String] -> Repl ()
-- load cmdStr = case parseCommand cmdStr of
--   Load f -> tryAction $ do
--     liftIO $ run f
--   BadCmd -> do
--     liftIO $ putStrLn $ "unknown command"

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Exiting TCHi."
    exitSuccess

completer :: WordCompleter IO
completer n = do
  let names = [":help", ":quit"]
  pure $ filter (isPrefixOf n) names

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
parseOneLine parseThis = case parse parseThis of
  OK ast rest ->
    if rest == Byte.empty
    then liftIO $ print ast
    else liftIO $ do putStr $ id "Incomplete input: "
                     putStrLn $ show rest
  Fail -> liftIO $ do putStrLn "Invalid input!"
  Err err -> liftIO $ do print err
