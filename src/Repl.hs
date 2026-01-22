module Repl
  ( repl
  ) where

import qualified Command as Cmd
import Control.Monad.IO.Class
import Control.Monad.State.Strict
import Data.List (groupBy, sortBy, intersperse, isPrefixOf)
import System.Console.Repline as Repline hiding (banner)
import System.Exit
import System.IO

type ReplState = Bool -- print FGG JSON in compact mode

type Repl a = HaskelineT (StateT ReplState IO) a

data CmdKind =
  General
  | Debugging
  | Setting
  deriving (Eq, Ord, Show)

data CmdHelp = CmdHelp {
  cmd :: String,
  short :: String,
  args :: [String],
  kind :: CmdKind,
  help :: String
} deriving (Eq, Ord, Show)

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
  [ ("help", helpCmd), ("h", helpCmd)
  , ("load", load), ("l", load)
  , ("matrix", toTypedMatrix), ("m", toTypedMatrix)
  , ("lm", loadMatrix)
  , ("lt", typeOfF), ("type", typeOfPg)
  , ("lp", toPerplF), ("perpl", toPerpl)
  , ("lc", compileF), ("compile", compile)
  , ("lf", toFggF), ("fgg", toFgg)
  , ("quit", quit), ("q", quit)
  , ("set", setOption . words)
  ]

-- Each help info is a tuple: (command, short command, arguments, CmdKind, help)
helpInfo :: [(String, CmdHelp)]
helpInfo =
  map (\ h@CmdHelp{cmd=c, short=_, args=_, kind=_, help=_} -> (c, h))
  [
    CmdHelp {
      cmd = "<exp>", short = "", args = [], kind = General,
      help = "Evaluate <exp>."
      },
    CmdHelp {
      cmd = ":load", short = ":l", args = ["<file>"], kind = General,
      help = "Evaluate <file>."
      },
    CmdHelp {
      cmd = ":c", short = "", args = ["<exp>"], kind = Debugging,
      help = "[For debugging] Compile <exp>."
      },
    CmdHelp {
      cmd = ":lc", short = "", args = ["<file>"], kind = Debugging,
      help = "[For debugging] Compile <file>."
      },
    CmdHelp {
      cmd = ":fgg", short = "", args = ["<exp>"], kind = General,
      help = "Convert <exp> to an equivalent FGG program."
      },
    CmdHelp {
      cmd = ":lf", short = "", args = ["<file>"], kind = General,
      help = "Convert <file> to an equivalent FGG program."
      },
    CmdHelp {
      cmd = ":matrix", short = ":m", args = ["<exp>"], kind = General,
      help = "Convert <exp> into a matrix according to its type if <exp> evaluates to an iso."
      },
    CmdHelp {
      cmd = ":lm", short = "", args = ["<file>"], kind = General,
      help = "Convert <file> into a matrix according to its type if <exp> evaluates to an iso."
      },
    CmdHelp {
      cmd = ":type", short = ":t", args = ["<exp>"], kind = General,
      help = "Show the type of <exp>."
      },
    CmdHelp {
      cmd = ":lt", short = "", args = ["<file>"], kind = General,
      help = "Show the type of <file>."
      },
    CmdHelp {
      cmd = ":perpl", short = "", args = ["<exp>"], kind = General,
      help = "Convert <exp> to an equivalent perpl program."
      },
    CmdHelp {
      cmd = ":lp", short = "", args = ["<file>"], kind = General,
      help = "Convert <file> to an equivalent perpl program."
      },
    CmdHelp {
      cmd = ":help", short = ":h", args = [], kind = General,
      help = "Show this information."
      },
    CmdHelp {
      cmd = ":quit", short = ":q", args = [], kind = General,
      help = "Quit the program."
      },
    CmdHelp {
      cmd = ":set compact", short = "", args = ["<bool>"], kind = Setting,
      help = "Set compact mode to <bool> (true or false) for printing FGG."
      }
  ]

showCmdKind :: CmdKind -> String
showCmdKind General = "Commands available from the prompt:"
showCmdKind Debugging = "Commands for debugging:"
showCmdKind Setting = "Commands for changing settings:"

showCmdArgs :: String -> [String] -> [String]
showCmdArgs "" _ = []
showCmdArgs cmd args = [unwords $ cmd:args]

showCmdHelp :: String -> CmdHelp -> String
showCmdHelp indent CmdHelp{cmd=c, short=s, args=a, kind=_, help=h} =
  form ++ "\n" ++ help where
  form = indent ++ unwords (showCmdArgs c a) ++ ", " ++ unwords (showCmdArgs s a)
  help = indent ++ replicate 20 ' ' ++ h

showAllHelp :: String
showAllHelp = unlines $ concatMap (\(g,cs) -> [g, cs]) (zip cmdKinds cmdStrs) where
  cmdGroups :: [[CmdHelp]]
  cmdGroups = groupBy (\c1 c2 -> kind c1 == kind c2) $
    sortBy (\c1 c2 -> compare (kind c1) (kind c2)) $ map snd helpInfo

  cmdKinds :: [String]
  cmdKinds = map (\(c:_) -> showCmdKind (kind c) ++ "\n") cmdGroups

  cmdStrs :: [String]
  cmdStrs = map (unlines . map (showCmdHelp "  ")) cmdGroups

helpCmd :: String -> Repl ()
helpCmd key = case lookup key helpInfo of
  Just cmd -> liftIO $ putStrLn $ showCmdHelp "" cmd
  Nothing -> liftIO $ putStrLn showAllHelp

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

toFgg :: String -> Repl ()
toFgg str = do
  c <- get
  (liftIO . Cmd.toFgg c stdout) str

toFggF :: String -> Repl ()
toFggF str = do
  c <- get
  (liftIO . Cmd.toFggFile c stdout) str

setCompact :: String -> String -> Repl ()
setCompact _ "true" = put True
setCompact _ "false" = put False
setCompact cmd _ = helpCmd cmd

setOption :: [String] -> Repl ()
setOption args =
  case args of
    [] -> helpCmd $ unwords $ ":set ":args
    ["compact", b] -> setCompact ":set compact" b
    _ -> helpCmd $ unwords $ ":set ":args

quit :: String -> Repl ()
quit = const $ do
  liftIO $ do
    putStrLn "Leaving IsoCi."
    exitSuccess

completer :: WordCompleter (StateT ReplState IO)
completer n = do
  let names = [":help", ":load", ":lc", ":lf", ":lm", ":lp", ":lt",
               ":compile", ":matrix", ":m", ":type", ":paste",
               ":perpl", ":quit", ":set"]
  pure $ filter (isPrefixOf n) names

prefixCompleter :: CompleterStyle (StateT ReplState IO)
prefixCompleter = Repline.Prefix (wordCompleter completer)
  [(":l" , fileCompleter), (":load" , fileCompleter),
   (":lm" , fileCompleter), (":lt" , fileCompleter),
   (":lp" , fileCompleter), (":lc" , fileCompleter),
   (":lf" , fileCompleter)
  ]

repl :: IO ()
repl = flip evalStateT False $
  evalRepl
  banner
  eval
  optionsList
  (Just ':')
  (Just "paste")
  prefixCompleter
  initial
  final
