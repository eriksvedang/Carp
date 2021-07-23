{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Repl where

import ColorText
import Control.Monad.State.Strict
import Data.List (isPrefixOf)
import Env
import Eval
import qualified Map
import Obj
import Parsing (balance)
import Path
import Project
import System.Console.Haskeline
  ( Completion,
    InputT,
    Settings (..),
    completeWordWithPrev,
    getInputLine,
    runInputT,
    simpleCompletion,
  )
import System.Exit (exitSuccess)

completeKeywordsAnd :: Context -> String -> [Completion]
completeKeywordsAnd context word =
  findKeywords word (envPublicBindingNames (contextGlobalEnv context) ++ keywords) []
  where
    findKeywords _ [] res = res
    findKeywords match (x : xs) res =
      if match `isPrefixOf` x
        then findKeywords match xs (res ++ [simpleCompletion x])
        else findKeywords match xs res
    keywords =
      [ "def",
        "defn",
        "let",
        "do",
        "if",
        "while",
        "ref",
        "set!",
        "the",
        "defmacro",
        "dynamic",
        "quote",
        "car",
        "cdr",
        "cons",
        "list",
        "array",
        "expand",
        "deftype",
        "register",
        "true",
        "false"
      ]

readlineSettings :: String -> Settings (StateT Context IO)
readlineSettings historyPath =
  Settings
    { complete =
        completeWordWithPrev
          Nothing
          ['(', ')', '[', ']', ' ', '\t', '\n']
          ( \_ w -> do
              ctx <- get
              pure (completeKeywordsAnd ctx w)
          ),
      historyFile = Just historyPath,
      autoAddHistory = True
    }

specialCommands :: Map.Map Char String
specialCommands =
  Map.fromList
    [ ('x', "run"),
      ('r', "reload"),
      ('b', "build"),
      ('c', "cat"),
      ('e', "env"),
      ('h', "help"),
      ('p', "project"),
      ('q', "quit"),
      ('t', "type"),
      ('m', "expand"),
      ('i', "info")
    ]

rewriteError :: String -> String
rewriteError msg = "(macro-error \"" ++ msg ++ "\")"

treatSpecialInput :: String -> String
treatSpecialInput ":\n" = rewriteError "Unfinished special command"
treatSpecialInput (':' : rest) =
  let cmdAndArgs = words rest
      cmd = head cmdAndArgs
      args = tail cmdAndArgs
   in if length cmd == 1
        then makeCommand args (head cmd)
        else
          if null args
            then "(do " ++ unwords (map (makeCommand []) cmd) ++ ")"
            else rewriteError "Can’t have grouped special command with arguments"
  where
    makeCommand args cmd =
      case Map.lookup cmd specialCommands of
        Just command -> "(" ++ command ++ " " ++ unwords args ++ ")"
        Nothing -> rewriteError ("Unknown special command: :" ++ [cmd])
treatSpecialInput arg = arg

repl :: Int -> String -> String -> InputT (StateT Context IO) ()
repl line readSoFar prompt =
  do
    context <- lift get
    input <- getInputLine (strWithColor Yellow prompt)
    case input of
      Nothing -> do
        _ <- liftIO exitSuccess
        pure ()
      Just i -> do
        let concatenated = readSoFar ++ i ++ "\n"
            balanced = balance concatenated
            proj = contextProj context
        case balanced of
          "" -> do
            let input' = if concatenated == "\n" then contextLastInput context else concatenated -- Entering an empty string repeats last input
            context' <- liftIO $ executeStringAtLine line True True (resetAlreadyLoadedFiles context) (treatSpecialInput input') "REPL"
            lift $ put context'
            repl (line + (length (filter ('\n' ==) input'))) "" (projectPrompt proj)
          _ -> repl line concatenated (if projectBalanceHints proj then balanced else "")

resetAlreadyLoadedFiles :: Context -> Context
resetAlreadyLoadedFiles context =
  let proj = contextProj context
      proj' = proj {projectAlreadyLoaded = []}
   in context {contextProj = proj'}

runRepl :: Context -> IO ((), Context)
runRepl context = do
  historyPath <- configPath "history"
  createDirectoryIfMissing True (takeDirectory historyPath)
  runStateT (runInputT (readlineSettings historyPath) (repl 1 "" (projectPrompt (contextProj context)))) context
