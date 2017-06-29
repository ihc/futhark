{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}
module Main (main) where

import Control.Exception
import Data.Char
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T
import NeatInterpolation(text)
import Prelude
import System.IO
import System.Exit
import System.Console.GetOpt

import Language.Futhark as AST
import Futhark.Compiler(readProgram, reportingIOErrors, dumpError, newFutharkConfig)
import Futhark.Debugger
import Futhark.Pipeline(CompilerError(ExternalError))
import Futhark.Util.Options

-- commandline options, not currently used
newtype DebuggerConfig = DebuggerConfig { entryPoint :: Name }

debuggerConfig :: DebuggerConfig
debuggerConfig = DebuggerConfig defaultEntryPoint

options :: [FunOptDescr DebuggerConfig]
options = [ Option "e" ["entry-point"]
          (ReqArg (\entry -> Right $ \config ->
                      config { entryPoint = nameFromString entry })
           "NAME")
            "The entry point to execute."
          ]

-- current program state, and last command executed
data DebuggerState a = DebuggerState
       { lastState :: DebugT IO a
       , lastCommand :: Maybe Command
       }

newDebuggerState :: DebugT IO a -> DebuggerState a
newDebuggerState p = DebuggerState
       { lastState = p
       , lastCommand = Nothing
       }

type FutharkdbM b a = StateT (DebuggerState b) IO a

{- Entry point. Takes filename and entry point as commandline arguments -}
main :: IO ()
main = reportingIOErrors $
       mainWithOptions debuggerConfig options run
  where run :: [String] -> DebuggerConfig -> Maybe (IO ())
        run [prog] config = Just $ do
            putStrLn $ "Reading file: " <> prog
            res <- liftIO $ runExceptT (readProgram prog)
                   `catch` \(err::IOException) ->
                   return (Left (ExternalError (T.pack $ show err)))
            case res of
              Left err ->
                dumpError newFutharkConfig err
              Right (pro, _, _imports, _src) ->
                repl $ runProgram pro (entryPoint config)
        run [] _config = Just $ repl $ return [] -- use maybe instead?
        run _ _config  = Nothing

        repl :: DebugT IO [Value] -> IO ()
        repl pr = do
          putStrLn "Run help for a list of commands."
          evalStateT (forever readEvalPrint) (newDebuggerState pr)

runProgram :: Prog -> Name -> DebugT IO [Value]
runProgram prog entry =
    let ep = if nameToString entry == ""
             then defaultEntryPoint
             else entry in
    runFun ep [] prog

readEvalPrint :: FutharkdbM [Value] ()
readEvalPrint = do
  liftIO $ putStr "> "
  liftIO $ hFlush stdout
  line <- liftIO T.getLine
  let (cmdname, rest) = T.break isSpace line
      arg = T.dropWhileEnd isSpace $ T.dropWhile isSpace rest
  if cmdname == "" then do
      st <- get
      case lastCommand st of
          Just cmd -> cmd ""
          Nothing ->
            liftIO $ putStrLn "No command"
  else
    case lookup cmdname commands of
      Just (cmdf, _) -> cmdf arg
      Nothing -> liftIO $ T.putStrLn $ "Unknown command '" <> cmdname <> "'"

type Command = T.Text -> FutharkdbM [Value] ()

updateLastCommand :: Command -> FutharkdbM [Value] ()
updateLastCommand k =
  modify $ \st -> st { lastCommand = Just k}

updateLastState :: MonadState (DebuggerState a) m => DebugT IO a -> m ()
updateLastState s =
  modify $ \st -> st { lastState = s }

commands :: [(T.Text, (Command, T.Text))]
commands = [("load", (loadCommand, [text|Load a Futhark source file.|])),
            ("help", (helpCommand, [text|Print a list of commands.|])),
            ("quit", (quitCommand, [text|Quit futharkdb.|])),
            ("run", (runCommand, [text|Run program.|])),
            ("step", (stepCommand, [text|Make one step in the program.|]))]
  where
        loadCommand :: Command
        loadCommand file = do
          updateLastCommand loadCommand -- a bit useless since param not kept
          liftIO $ T.putStrLn $ "Reading file " <> file
          res <- liftIO $ runExceptT (readProgram $ T.unpack file)
                 `catch` \(err::IOException) ->
                 return (Left (ExternalError (T.pack $ show err)))
          case res of
            Left err ->
              liftIO $ dumpError newFutharkConfig err
            Right (prog, _, _imports, _src) -> do
              liftIO $ putStrLn "Succesfully loaded."
              updateLastState $ runProgram prog defaultEntryPoint

        helpCommand :: Command
        helpCommand _ = do
            updateLastCommand helpCommand
            liftIO $ forM_ commands $ \(cmd, (_, desc)) -> do
                       T.putStrLn cmd
                       T.putStrLn $ T.replicate (T.length cmd) "-"
                       T.putStr desc
                       T.putStrLn ""
                       T.putStrLn ""

        quitCommand :: Command
        quitCommand _ = liftIO exitSuccess

        stepCommand :: Command
        stepCommand _ = do
            updateLastCommand stepCommand
            st <- get
            x <- lift $ stepDebugT (lastState st)
            case x of
                (Left x') -> do
                  liftIO $ print x'
                  updateLastState $ return []
                (Right (desc, m')) -> do
                  liftIO $ putStrLn ("Step: " ++ desc)
                  updateLastState m'

        runCommand :: Command
        runCommand _ = do
            updateLastCommand runCommand
            st <- get
            m <- lift $ stepDebugT $ lastState st
            loop m

        loop (Left x) = do
            liftIO $ print x
            updateLastState $ return []
        loop (Right (_, s)) = do
            updateLastState s
            runCommand ""
