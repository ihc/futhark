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

-- description of breakpoint break condition
data Breakpoint =
    Location String Int -- file name, line number
  | Function String     -- function name. should include modules at some point

instance Show Breakpoint where
  show (Location file line) = "location:" ++ file ++ ":" ++ show line
  show (Function name) = "function:" ++ name

-- description of current suspension, program suspension, suspension environment
data DebuggerStep = DebuggerStep
       { stepDesc :: String
       , stepEnv :: DebuggerEnv IO
       , stepState :: DebuggerT IO [Value]
       }

instance Show DebuggerStep where
  show d = locStr (dbLocation (stepEnv d)) ++ ": " ++ stepDesc d

debuggerStep :: String -> DebuggerEnv IO -> DebuggerT IO [Value] -> DebuggerStep
debuggerStep desc env pro =
  DebuggerStep { stepDesc = desc, stepEnv = env, stepState = pro }

data DebuggerState = DebuggerState
       { history :: [DebuggerStep]
       , lastCommand :: Maybe Command
       , breakpoints :: [Breakpoint]
       }

newDebuggerState :: Maybe DebuggerStep -> DebuggerState
newDebuggerState p = DebuggerState
       { history = maybeToList p
       , lastCommand = Nothing
       , breakpoints = []
       }

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

        repl :: Maybe DebuggerStep -> IO ()
        repl pr = do
          putStrLn "Run help for a list of commands."
          evalStateT (forever readEvalPrint) (newDebuggerState pr)

runProgram :: Prog -> Name -> DebuggerStep
runProgram prog entry =
    let ep = if nameToString entry == ""
             then defaultEntryPoint
             else entry
        (pro, env) = runFun ep [] prog in
    DebuggerStep { stepDesc = "Entry point.", stepState = pro, stepEnv = env }

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

commands :: [(T.Text, (Command, T.Text))]
commands = [ ("load", (loadCommand, [text|Load a Futhark source file.|]))
           , ("help", (helpCommand, [text|Print a list of commands.|]))
           , ("quit", (quitCommand, [text|Quit futharkdb.|]))
           , ("run",  (runCommand, [text|Run program.|]))
           , ("step", (stepCommand, [text|Make one step in the program.|]))
           , ("read", (readCommand, [text|Read the value of a variable.|]))
           , ("next", (nextCommand,
                      [text|Skip until same evaluation depth is reached.|]))
           , ("break",(breakCommand, [text|Add a breakpoint.|]))
           , ("list", (listCommand, [text|List all breakpoints.|]))
           , ("back", (backCommand, [text|Make one step in backwards direction.|]))
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
              pushHistory $ runProgram prog defaultEntryPoint

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
          handleStep (liftIO . print)

        nextCommand :: Command
        nextCommand _ =
          handleProgState (\step ->
            let dep = dbDepth (stepEnv step)
                cont step' =
                  if dbDepth (stepEnv step') == dep
                  then liftIO $ print step'
                  else handleStep cont in
            handleStep cont
            )

        runCommand :: Command
        runCommand _ =
          handleStep (\_ -> runCommand "")

        readCommand :: Command
        readCommand var =
          handleProgState (\step ->
            let vtable = dbVtable $ stepEnv step in
            if var == ""
            then -- no variable name provided, list all
              liftIO $ forM_ vtable $ \(n, val) ->
                         putStrLn (baseString n ++ ": " ++ show (pretty val))
            else
              case find (\(n, _) -> baseString n == T.unpack var) vtable of
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

        backCommand :: Command
        backCommand _ = do
          lst <- popHistory
          case lst of
            Nothing -> liftIO $ putStrLn "Nothing to go back to!"
            (Just step) -> liftIO $ print step

updateLastCommand :: Command -> DebuggerM ()
updateLastCommand k =
  modify $ \st -> st { lastCommand = Just k }

pushHistory :: DebuggerStep -> DebuggerM ()
pushHistory s =
  modify $ \st -> st { history = s : history st }

popHistory :: DebuggerM (Maybe DebuggerStep)
popHistory = do
  st <- get
  case history st of
    [] -> return Nothing
    (x:xs) -> do
      modify $ \st' -> st' { history = xs }
      return $ Just x

resetHistory :: DebuggerM ()
resetHistory =
  modify $ \st -> st { history = [] }

getProgState :: DebuggerM (Maybe DebuggerStep)
getProgState = do
  st <- get
  return $ listToMaybe $ history st

getBreakpoints :: DebuggerM [Breakpoint]
getBreakpoints = do
  st <- get
  return (breakpoints st)

-- returns indices of breakpoints whose conditions were fulfilled at this stage
getHitBreakpoints :: DebuggerEnv IO -> DebuggerM [Int]
getHitBreakpoints env = do
  bps <- getBreakpoints
  return $ getBrokenPoints env bps 0
  where getBrokenPoints _ [] _ = []
        getBrokenPoints e (b:bs) ix =
          if checkBreakpoint e b
          then ix : getBrokenPoints e bs (ix+1)
          else getBrokenPoints e bs (ix+1)

-- extract program state if any, call continuation on it
handleProgState :: (DebuggerStep -> DebuggerM ()) -> DebuggerM ()
handleProgState cont = do
  ps <- getProgState
  case ps of
    Nothing -> liftIO $ putStrLn "No program is currently loaded."
    (Just d) -> cont d

-- go one step in execution. if more steps and breakpoint not hit,
-- call continuation on step of next suspension.
handleStep :: (DebuggerStep -> DebuggerM ()) -> DebuggerM ()
handleStep cont =
  handleProgState (\step -> do
    k <- lift $ runExceptT $ stepDebuggerT $ stepState step
    case k of
      (Right (Right (Export desc env m'))) ->
        let nextStep = debuggerStep desc env m' in
        do
          pushHistory nextStep
          handleHitBreakpoints nextStep cont
      (Right (Left res)) -> do
        resetHistory
        liftIO $ putStrLn ("Result: " ++ show res)
      (Left err) -> do
        resetHistory
        liftIO $ putStrLn ("Error: " ++ show err)
    )

-- TODO: currently stops every time the breakpoint's line is hit, but there
-- may be several steps in one line. Maybe should only break first time.
handleHitBreakpoints :: DebuggerStep -> (DebuggerStep -> DebuggerM ())
                        -> DebuggerM ()
handleHitBreakpoints step cont = do
  b <- getHitBreakpoints (stepEnv step)
  case b of
    [] -> cont step
    x ->
      liftIO $ forM_ x (\ix -> do
        putStrLn ("Breakpoint " ++ show ix ++ " hit.")
        print step
        )

checkBreakpoint :: DebuggerEnv IO -> Breakpoint -> Bool
checkBreakpoint env (Location _ line) =
  let (_f, l) = getFileLine $ dbLocation env in
  l == line -- && f == file  -- assume single-file for now
  where getFileLine (SrcLoc (Loc (Pos f l _ _) _)) = (f, l)
        getFileLine _ = ("", -1)
checkBreakpoint _ (Function _) =
  error "function breakpoint unimplemented"
