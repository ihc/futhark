{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Futhark.Debugger
  ( DebuggerError
  , DebuggerT, debuggerT
  , Export(..)
  , ExportedEnv, vtable, VTable, depth, location
  , runFun
  , stepDebuggerT
  )
where

import Control.Applicative
import Control.Monad.Except
import Data.List
import Data.Loc
import Prelude
import Language.Futhark
import Futhark.Representation.Primitive(intValue, valueIntegral)

{- TYPES -}

-- base debugging monad. NOTE: this is basically the coroutine monad
newtype BaseDebuggerT s m a = DebuggerT
  { stepDebuggerT :: m (Either a (s (BaseDebuggerT s m a))) }

instance (Functor s, Monad m) => Monad (BaseDebuggerT s m) where
  return x = DebuggerT $ return $ Left x

  m >>= f = DebuggerT $ do
    x <- stepDebuggerT m
    case x of
      Left x' ->
        stepDebuggerT $ f x'
      Right s ->
        return $ Right (fmap (>>= f) s)

instance (Functor s, Monad m) => Functor (BaseDebuggerT s m) where
  fmap = liftM

instance (Functor s, Monad m) => Applicative (BaseDebuggerT s m) where
  pure = return
  df <*> dx = df >>= \f -> liftM f dx

debuggerT :: m (Either a (s (BaseDebuggerT s m a))) -> BaseDebuggerT s m a
debuggerT = DebuggerT

-- language-specific debugging monad with error handling
type DebuggerT m = BaseDebuggerT Export (ExceptT DebuggerError m)

-- error type for interpreter errors
data DebuggerError = Generic String
instance Show DebuggerError where
  show (Generic s) = s

instance Monad m => MonadError DebuggerError (DebuggerT m) where
  throwError e = debuggerT $ throwError e
  a `catchError` e =
    debuggerT $ stepDebuggerT a `catchError` (stepDebuggerT . e)

-- functor that we use to wrap information that is exported in a step
data Export a = Export String ExportedEnv a
instance Functor Export where
  fmap f (Export a b c) = Export a b (f c)

-- insert one single step with the given environment and description
step :: Monad m
        => DebuggerEnv m -> String -> DebuggerT m a
        -> DebuggerT m a
step env desc m =
  debuggerT $ return $ Right (Export desc (export env) m)


{- ENVIRONMENT -}

-- TODO: we probably want this to be only for builtin functions.
type Fun m = DebuggerEnv m -> [Value] -> DebuggerT m [Value]

-- TODO: use maps instead of lists
type FunTable m = [(Name, Fun m)]
type VTable = [(VName, Value)]

-- reader environment for interpreter
data DebuggerEnv m = DebuggerEnv { envVtable :: VTable
                                 , envFtable :: FunTable m
                                 , evaluationDepth :: Int
                                 , envLocation :: SrcLoc
                                 }

-- the environment that is exposed to the outside.
data ExportedEnv = ExportedEnv { vtable :: VTable
                               , depth :: Int
                               , location :: SrcLoc
                               }

newDebuggerEnv :: Monad m => FunTable m -> DebuggerEnv m
newDebuggerEnv ftable =
  DebuggerEnv { envVtable = []
              , envFtable = ftable
              , evaluationDepth = 0
              , envLocation = noLoc
              }

lookupVar :: Monad m => VName -> DebuggerEnv m -> DebuggerT m Value
lookupVar vname env =
  case lookup vname (envVtable env) of
    Just val' -> return val'
    Nothing   -> throwError $ Generic $ "lookupVar " ++ show vname

bindVar :: VName -> Value -> DebuggerEnv m -> DebuggerEnv m
bindVar name val env =
  env { envVtable = (name, val) : envVtable env }

extendVtable :: VTable -> DebuggerEnv m -> DebuggerEnv m
extendVtable vt env =
  env { envVtable = vt ++ envVtable env }

inc :: DebuggerEnv m -> DebuggerEnv m
inc env =
  env { evaluationDepth = evaluationDepth env + 1 }

setLocation :: SrcLoc -> DebuggerEnv m -> DebuggerEnv m
setLocation s env =
  env { envLocation = s }

export :: DebuggerEnv m -> ExportedEnv
export e = ExportedEnv { vtable = envVtable e
                       , depth = evaluationDepth e
                       , location = envLocation e
                       }


{- HELPERS -}

-- extract variable names for vtable bindings
getPatternName :: Pattern -> VName
getPatternName x =
  case x of
      TuplePattern _ _ -> VName (nameFromString "tuplePattern") 1
      RecordPattern _ _ -> VName (nameFromString "recordPattern") 1
      PatternParens p _ -> getPatternName p
      Id idbase -> identName idbase
      Wildcard _ _ -> VName (nameFromString "wildcardPattern") 1
      PatternAscription p _ -> getPatternName p

getBinOp :: VName -> Value -> Value -> Value
getBinOp vname x y =
  case (baseString vname, x, y) of
      ("+", PrimValue (SignedValue a), PrimValue (SignedValue b)) ->
          PrimValue (SignedValue
            (intValue Int32 (valueIntegral a + valueIntegral b)))
      (_, _, _) ->
          error "Debugger error: UNIMPLEMENTED"


{- INTERPRETER -}

evalBody :: Monad m => Exp -> DebuggerEnv m -> DebuggerT m [Value]
evalBody body ev =
  let env = setLocation (srclocOf body) (inc ev) in
  case body of
      Literal p _loc -> return [PrimValue p]

      Parens e _ -> evalBody e env

      Var name _ _ ->
        do
           val <- lookupVar (qualLeaf name) env
           return [val]

      LetPat _ pat val e _ ->
        let vname = getPatternName pat in -- assume just one for now
        do
          [v] <- evalBody val env
          step env ("Binding variable \"" ++ baseString vname
                    ++ "\" to :" ++ show (pretty v))
            $ evalBody e $ bindVar (getPatternName pat) v env

      BinOp name (e1,_) (e2,_) _ _ ->
        let bname = qualLeaf name
            bino = getBinOp bname
            sname = baseString bname in
        do
          [ee1] <- step env
                     ("Evaluating first operand of binop ("
                       ++ sname ++ "): " ++ show (pretty e1))
                     $ evalBody e1 env
          [ee2] <- step env
                     ("Evaluating second operand of binop ("
                       ++ sname ++ "): " ++ show (pretty e2))
                     $ evalBody e2 env
          step env ("Applying binop (" ++ sname ++ ")") $ return [bino ee1 ee2]

      _ ->
        throwError $ Generic "unimplemented"

mkFun :: Monad m => FunBind -> (Name, Fun m)
mkFun fu =
  let name = case funBindName fu of VName n _ -> n
      fun env n =
          let params =
                case funBindParams fu of
                  [TuplePattern x _] -> x
                  _ -> fail "function was not given expected (...) parameters"
              vt = zip (map getPatternName params) n in
              -- TODO: needs bounds checking
              -- and support for binding values in-place
              -- (i.e. unique type array inplace modification)
          if length params /= length n
          then throwError $ Generic ("not same parameter length" ++ show n)
          else evalBody (funBindBody fu) $ extendVtable vt env
  in
  (name, fun)

mkDec :: [Dec] -> [FunBind]
mkDec decs =
  let only_funcs = filter (\x -> case x of FunDec _ -> True; _ -> False) decs in
  map (\x -> case x of FunDec f -> f; _ -> error "not fundec") only_funcs

buildFunTable :: Monad m => Prog -> FunTable m
buildFunTable prog =
  let decs = progDecs prog
      funcs = mkDec decs in
  foldl (\acc elt -> mkFun elt : acc) [] funcs

runFun :: Monad m =>
          Name -> [Value] -> Prog -> (DebuggerT m [Value], ExportedEnv)
runFun fname args prog =
  let ftable = buildFunTable prog
      env = newDebuggerEnv ftable in
  case lookup fname ftable of
     Just f -> (f env args, export env)
     _ -> (debuggerT $ throwError $ Generic "unknown function", export env)
