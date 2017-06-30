{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}
module Main (main) where

import Control.Exception
import Data.Char
import Data.List(find)
import Data.Loc
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Text.Read(decimal)
import NeatInterpolation(text)
import Prelude
import System.IO
import System.Exit
import System.Console.GetOpt

import Language.Futhark as AST
import Language.Futhark.Core(locStr)
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

data Breakpoint =
    Location String Int -- file name, line number
  | Function String     -- function name. should include modules at some point

instance Show Breakpoint where
  show (Location file line) = "location:" ++ file ++ ":" ++ show line
  show (Function name) = "function:" ++ name

-- current program state, and last command executed
data DebuggerState = DebuggerState
       { lastState :: Maybe ProgramState
       , lastCommand :: Maybe Command
       , breakpoints :: [Breakpoint]
       }

newDebuggerState :: Maybe ProgramState -> DebuggerState
newDebuggerState p = DebuggerState
       { lastState = p
       , lastCommand = Nothing
       , breakpoints = []
       }

type ProgramState = (DebuggerT IO [Value], ExportedEnv)
type DebuggerM = StateT DebuggerState IO

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

readEvalPrint :: DebuggerM ()
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

type Command = T.Text -> DebuggerM ()

updateLastCommand :: Command -> DebuggerM ()
updateLastCommand k =
  modify $ \st -> st { lastCommand = Just k}

updateLastState :: Maybe ProgramState -> DebuggerM ()
updateLastState s =
  modify $ \st -> st { lastState = s }

getProgState :: DebuggerM (Maybe ProgramState)
getProgState = do
  st <- get
  return $ lastState st

getBreakpoints :: DebuggerM [Breakpoint]
getBreakpoints = do
  st <- get
  return (breakpoints st)

getStringLoc :: ExportedEnv -> DebuggerM String
getStringLoc env =
  return $ locStr $ location env

-- returns indices of hit breakpoints
getHitBreakpoints :: ExportedEnv -> DebuggerM [Int]
getHitBreakpoints env = do
  bps <- getBreakpoints
  return $ getBrokenPoints env bps 0
  where getBrokenPoints _ [] _ = []
        getBrokenPoints e (b:bs) ix =
          if checkBreakpoint e b
          then ix : getBrokenPoints e bs (ix+1)
          else getBrokenPoints e bs (ix+1)

-- extract program state if any, call continuation on it
handleProgState :: (DebuggerT IO [Value] -> ExportedEnv -> DebuggerM ())
                   -> DebuggerM ()
handleProgState cont = do
  ps <- getProgState
  case ps of
    Nothing -> liftIO $ putStrLn "No program is currently loaded."
    (Just (p,e)) -> cont p e

-- go one step in execution. if more steps and breakpoint not hit,
-- call continuation on description and environment of next suspension.
handleStep :: (String -> ExportedEnv -> DebuggerM ()) -> DebuggerM ()
handleStep cont =
  handleProgState (\prog _ -> do
    k <- lift $ runExceptT $ stepDebuggerT prog
    case k of
      (Right (Right (Export desc env m'))) -> do
        updateLastState $ Just (m', env)
        handleHitBreakpoints desc env cont
      (Right (Left res)) -> do
        updateLastState Nothing
        liftIO $ putStrLn ("Result: " ++ show res)
      (Left err) -> do
        updateLastState Nothing
        liftIO $ putStrLn ("Error: " ++ show err)
    )

-- TODO: currently stops every time the breakpoint's line is hit, but there
-- may be several steps in one line. Maybe should only break first time.
handleHitBreakpoints :: String -> ExportedEnv
                        -> (String -> ExportedEnv -> DebuggerM ())
                        -> DebuggerM ()
handleHitBreakpoints desc env cont = do
  b <- getHitBreakpoints env
  case b of
    [] -> cont desc env
    x ->
      liftIO $ forM_ x (\ix -> do
        putStrLn ("Breakpoint " ++ show ix ++ " hit.")
        putStrLn (locStr (location env) ++ ": " ++ desc)
        )

checkBreakpoint :: ExportedEnv -> Breakpoint -> Bool
checkBreakpoint env (Location _ line) =
  let loc = location env
      (_f, l) = getFileLine loc in
  l == line -- && f == file  -- assume single-file for now
  where getFileLine (SrcLoc (Loc (Pos f l _ _) _)) = (f, l)
        getFileLine _ = ("", -1)
checkBreakpoint _ (Function _) =
  error "function breakpoint unimplemented"

commands :: [(T.Text, (Command, T.Text))]
commands = [("load",  (loadCommand, [text|Load a Futhark source file.|]))
           , ("help", (helpCommand, [text|Print a list of commands.|]))
           , ("quit", (quitCommand, [text|Quit futharkdb.|]))
           , ("run",  (runCommand, [text|Run program.|]))
           , ("step", (stepCommand, [text|Make one step in the program.|]))
           , ("read", (readCommand, [text|Read the value of a variable.|]))
           , ("next", (nextCommand,
                      [text|Skip until same evaluation depth is reached.|]))
           , ("break",(breakCommand, [text|Add a breakpoint.|]))
           , ("list", (listCommand, [text|List all breakpoints.|]))
           ]
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
          handleStep (\desc env -> do
            loc <- getStringLoc env
            liftIO $ putStrLn (loc ++ ": " ++ desc)
          )

        nextCommand :: Command
        nextCommand _ =
          handleProgState (\_ env ->
            let dep = depth env
                cont desc e =
                  if depth e == dep
                  then do
                    loc <- getStringLoc e
                    liftIO $ putStrLn (loc ++ ": " ++ desc)
                  else handleStep cont in
            handleStep cont
            )

        runCommand :: Command
        runCommand _ =
          handleStep (\_ _ -> runCommand "")

        readCommand :: Command
        readCommand var =
          handleProgState (\_ env ->
            if var == ""
            then -- list all
              liftIO $ forM_ (vtable env) $ \(n, val) ->
                         putStrLn (baseString n ++ ": " ++ show (pretty val))
            else
              case find (\(n, _) -> baseString n == T.unpack var) $ vtable env of
                Nothing ->
                  liftIO $ putStrLn ("No variable named " ++ show var)
                (Just (_, v)) ->
                  liftIO $ putStrLn (pretty v)
            )

        breakCommand :: Command
        breakCommand input =
          -- for now assume user input is a line number. assume single-file!
          case decimal input :: Either String (Int, T.Text) of
            Left _ -> do
              liftIO $ T.putStr input
              liftIO $ putStrLn " is not a line number."
            Right (i, _) -> do
              bps <- getBreakpoints
              let ix = length bps
                  newb = Location "" i in do
                liftIO $ putStrLn ("Added breakpoint " ++ show ix ++ ": " ++ show newb)
                modify $ \st -> st { breakpoints = breakpoints st ++ [newb] }

        listCommand :: Command
        listCommand _ = do
          bps <- getBreakpoints
          liftIO $ putStrLn "Breakpoints:"
          liftIO $ foldM_ (\(ix :: Int) bp -> do
            putStrLn (show ix ++ ": " ++ show bp)
            return (ix+1)
            ) 0 bps
