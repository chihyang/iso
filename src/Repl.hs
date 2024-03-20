module Repl
  ( repl
  ) where

import Control.Monad.IO.Class
import qualified Data.ByteString as Byte
import Data.List
import FlatParser (parse, Result(..))
import Run
import System.Console.Repline hiding (banner)
import System.Exit

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
toMatrix input = case run input >>= matrixizeIso of
  Right val -> liftIO $ print val
  Left err -> liftIO $ putStrLn err

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Leaving IsoCi."
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
parseOneLine parseThis = case run parseThis of
  Right val -> liftIO $ print val
  Left err -> liftIO $ putStrLn err
