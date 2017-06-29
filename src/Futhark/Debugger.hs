{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Futhark.Debugger
  ( DebuggerError
  , ExportedEnv, vtable, VTable, depth
  , DebuggerT
  , debuggerT
  , runFun
  , stepDebuggerT
  )
where

import Control.Applicative
import Control.Monad.Except
import Data.List
import Data.Loc(srclocOf)
import Prelude
import Language.Futhark.Core(locStr)
import Language.Futhark
import Futhark.Representation.Primitive(intValue, valueIntegral)

{- TYPES -}

data DebuggerError = Generic String
instance Show DebuggerError where
  show (Generic s) = s

newtype BaseDebuggerT m a = DebuggerT
  { stepDebuggerT :: m (Either a (String, ExportedEnv, BaseDebuggerT m a)) }

instance Monad m => Monad (BaseDebuggerT m) where
  return x = DebuggerT $ return $ Left x

  m >>= f = DebuggerT $ do
    x <- stepDebuggerT m
    case x of
      Left x' ->
        stepDebuggerT $ f x'
      Right (desc, env, m') ->
        return $ Right (desc, env, m' >>= f)

instance Monad m => Functor (BaseDebuggerT m) where
  fmap = liftM

instance Monad m => Applicative (BaseDebuggerT m) where
  pure = return
  df <*> dx = df >>= \f -> liftM f dx

debuggerT :: Monad m
             => m (Either a (String, ExportedEnv, BaseDebuggerT m a))
             -> BaseDebuggerT m a
debuggerT = DebuggerT

-- debugger transformer with error
type DebuggerT m = BaseDebuggerT (ExceptT DebuggerError m)

instance Monad m => MonadError DebuggerError (DebuggerT m) where
  throwError e = debuggerT $ throwError e
  a `catchError` e =
    debuggerT $ stepDebuggerT a `catchError` (stepDebuggerT . e)

step :: Monad m
        => DebuggerEnv m -> String -> DebuggerT m a
        -> DebuggerT m a
step env desc m = debuggerT $ return $ Right (desc, export env, m)

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
                                 }

-- the environment that is exposed to the outside.
data ExportedEnv = ExportedEnv { vtable :: VTable
                               , depth :: Int
                               }

newDebuggerEnv :: Monad m => FunTable m -> DebuggerEnv m
newDebuggerEnv ftable =
  DebuggerEnv { envVtable = [], envFtable = ftable, evaluationDepth = 0 }

lookupVar :: Monad m => VName -> DebuggerEnv m -> DebuggerT m Value
lookupVar vname env =
  case lookup vname (envVtable env) of
    Just val' -> return val'
    Nothing   -> throwError $ Generic $ "lookupVar " ++ show vname

bindVar :: VName -> Value -> DebuggerEnv m -> DebuggerEnv m
bindVar name val table =
  table { envVtable = (name, val) : envVtable table }

extendVtable :: VTable -> DebuggerEnv m -> DebuggerEnv m
extendVtable vt env =
  env { envVtable = vt ++ envVtable env }

inc :: DebuggerEnv m -> DebuggerEnv m
inc env =
  env { evaluationDepth = evaluationDepth env + 1 }

export :: DebuggerEnv m -> ExportedEnv
export e = ExportedEnv { vtable = envVtable e
                       , depth = evaluationDepth e
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
  let env = inc ev in
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
          step env (locStr (srclocOf e)
                 ++ ": Binding variable \"" ++ baseString vname
                 ++ "\" to :" ++ show (pretty v))
            $ evalBody e $ bindVar (getPatternName pat) v env

      BinOp name (e1,_) (e2,_) _ _ ->
        let bname = qualLeaf name
            bino = getBinOp bname
            sname = case bname of VName n _ -> nameToString n in
        do
          [ee1] <- step env
                     (locStr (srclocOf e1)
                       ++ ": Evaluating first operand of binop ("
                       ++ sname ++ "): " ++ show (pretty e1))
                     $ evalBody e1 env
          [ee2] <- step env
                     (locStr (srclocOf e2)
                       ++ ": Evaluating second operand of binop ("
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
              vtable = zip (map getPatternName params) n in
              -- TODO: needs bounds checking
              -- and support for binding values in-place
              -- (i.e. unique type array inplace modification)
          if length params /= length n
          then throwError $ Generic ("not same parameter length" ++ show n)
          else evalBody (funBindBody fu) $ extendVtable vtable env
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
