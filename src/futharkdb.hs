{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}
module Main (main) where

import Control.Exception
import Data.Char
import Data.List(find)
import Data.Maybe
import Control.Monad
--import Control.Monad.Reader
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

{- TYPES -}

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
data DebuggerState = DebuggerState
       { lastState :: Maybe ProgramState
       , lastCommand :: Maybe Command
       }

newDebuggerState :: Maybe ProgramState -> DebuggerState
newDebuggerState p = DebuggerState
       { lastState = p
       , lastCommand = Nothing
       }

type ProgramState = (DebuggerT IO [Value], ExportedEnv)
type FutharkdbM = StateT DebuggerState IO

{- ENTRY POINT -}

{- Takes filename and entry point as commandline arguments -}
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
                repl $ Just $ runProgram pro (entryPoint config)
        run [] _config = Just $ repl Nothing
        run _ _config  = Nothing

        repl :: Maybe ProgramState -> IO ()
        repl pr = do
          putStrLn "Run help for a list of commands."
          evalStateT (forever readEvalPrint) (newDebuggerState pr)

runProgram :: Prog -> Name -> ProgramState
runProgram prog entry =
    let ep = if nameToString entry == ""
             then defaultEntryPoint
             else entry in
    runFun ep [] prog

readEvalPrint :: FutharkdbM ()
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
          Nothing -> liftIO $ putStrLn "No command"
  else
    case lookup cmdname commands of
      Just (cmdf, _) -> do
        updateLastCommand cmdf
        cmdf arg
      Nothing -> liftIO $ T.putStrLn $ "Unknown command '" <> cmdname <> "'"

{- COMMANDS -}

type Command = T.Text -> FutharkdbM ()

updateLastCommand :: Command -> FutharkdbM ()
updateLastCommand k =
  modify $ \st -> st { lastCommand = Just k}

updateLastState :: MonadState DebuggerState m => Maybe ProgramState -> m ()
updateLastState s =
  modify $ \st -> st { lastState = s }

getEnv :: FutharkdbM (Maybe ExportedEnv)
getEnv = do
  st <- get
  return $ case lastState st of
    Nothing -> Nothing
    Just (_, env) -> Just env

handleVariables :: (VTable -> FutharkdbM ()) -> FutharkdbM ()
handleVariables cont = do
  env <- getEnv
  case env of
    Nothing -> liftIO $ putStrLn "No environment is currently loaded."
    (Just e) -> cont (vtable e)

handleStep :: (MonadTrans t, MonadIO (t IO), MonadState DebuggerState (t IO))
              => (String -> ExportedEnv -> t IO ()) -> t IO ()
handleStep cont = do
  st <- get
  case lastState st of
    Nothing -> liftIO $ putStrLn "No program is currently loaded."
    (Just (prog, _)) -> do
      k <- lift $ runExceptT $ stepDebuggerT prog
      case k of
        (Right (Right (desc, env, m'))) -> do
          updateLastState $ Just (m', env)
          cont desc env
        (Right (Left res)) -> do
          updateLastState Nothing
          liftIO $ putStrLn ("Result: " ++ show res)
        (Left err) -> do
          updateLastState Nothing
          liftIO $ putStrLn ("Error: " ++ show err)

commands :: [(T.Text, (Command, T.Text))]
commands = [("load", (loadCommand, [text|Load a Futhark source file.|])),
            ("help", (helpCommand, [text|Print a list of commands.|])),
            ("quit", (quitCommand, [text|Quit futharkdb.|])),
            ("run", (runCommand, [text|Run program.|])),
            ("step", (stepCommand, [text|Make one step in the program.|])),
            ("read", (readCommand, [text|Read the value of a variable.|]))]
  where
        loadCommand :: Command
        loadCommand file = do
          liftIO $ T.putStrLn $ "Reading file " <> file
          res <- liftIO $ runExceptT (readProgram $ T.unpack file)
                 `catch` \(err::IOException) ->
                 return (Left (ExternalError (T.pack $ show err)))
          case res of
            Left err ->
              liftIO $ dumpError newFutharkConfig err
            Right (prog, _, _imports, _src) -> do
              liftIO $ putStrLn "Succesfully loaded."
              updateLastState $ Just $ runProgram prog defaultEntryPoint

        helpCommand :: Command
        helpCommand _ =
          liftIO $ forM_ commands $ \(cmd, (_, desc)) -> do
                     T.putStrLn cmd
                     T.putStrLn $ T.replicate (T.length cmd) "-"
                     T.putStr desc
                     T.putStrLn ""
                     T.putStrLn ""

        quitCommand :: Command
        quitCommand _ = liftIO exitSuccess

        stepCommand :: Command
        stepCommand _ =
          handleStep (\desc _ -> liftIO $ putStrLn ("Step: " ++ desc))

        runCommand :: Command
        runCommand _ =
          handleStep (\_ _ -> runCommand "")

        readCommand :: Command
        readCommand var =
          handleVariables (\vars ->
            case find (\(n, _) -> baseString n == T.unpack var) vars of
              Nothing ->
                liftIO $ putStrLn ("No variable named " ++ show var)
              (Just (_, v)) ->
                liftIO $ putStrLn (pretty v)
            )
