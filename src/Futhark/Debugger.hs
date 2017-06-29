{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Futhark.Debugger
  ( DebuggerError
  , DebugT
  , EDebugT
  , FutharkEnv
  , runFun
  , stepDebugT
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

-- currently unused
data DebuggerError = Generic String
instance Show DebuggerError where
  show (Generic s) = s

newtype DebugT m a = DebugT { stepDebugT :: m (Either a (String, DebugT m a)) }

instance Monad m => Monad (DebugT m) where
  return x = DebugT $ return $ Left x

  m >>= f = DebugT $ do
    x <- stepDebugT m
    case x of
      Left x' ->
        stepDebugT $ f x'
      Right (desc, m') ->
        return $ Right (desc, m' >>= f)

instance Monad m => Functor (DebugT m) where
  fmap = liftM

instance Monad m => Applicative (DebugT m) where
  pure = return
  df <*> dx = df >>= \f -> liftM f dx

-- debugger transformer with error
type EDebugT m = DebugT (ExceptT DebuggerError m)

instance Monad m => MonadError DebuggerError (EDebugT m) where
  throwError e = DebugT $ throwError e
  a `catchError` e = DebugT $ stepDebugT a `catchError` (stepDebugT . e)

step :: Monad m => String -> EDebugT m a -> EDebugT m a
step desc m = DebugT $ return $ Right (desc, m)

-- TODO: we probably want this to be only for builtin functions.
type Fun m = FutharkEnv m -> [Value] -> EDebugT m [Value]
type FunTable m = [(Name, Fun m)]
type VTable = [(VName, Value)]

-- reader environment for interpreter
data FutharkEnv m = FutharkEnv { envVtable :: VTable
                               , envFtable :: FunTable m
                               }

lookupVar :: Monad m => VName -> FutharkEnv m -> EDebugT m Value
lookupVar vname env =
  case lookup vname (envVtable env) of
    Just val' -> return val'
    Nothing   -> throwError $ Generic $ "lookupVar " ++ show vname

bindVar :: VName -> Value -> FutharkEnv m -> FutharkEnv m
bindVar name val table =
  table { envVtable = (name, val) : envVtable table }

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

getStringName :: VName -> String
getStringName (VName name _) = nameToString name

getBinOp :: VName -> Value -> Value -> Value
getBinOp vname x y =
  case (getStringName vname, x, y) of
      ("+", PrimValue (SignedValue a), PrimValue (SignedValue b)) ->
          PrimValue (SignedValue
            (intValue Int32 (valueIntegral a + valueIntegral b)))
      (_, _, _) ->
          error "Debugger error: UNIMPLEMENTED"

evalBody :: Monad m => FutharkEnv m -> Exp -> EDebugT m [Value]
evalBody env body =
  case body of
      Literal p _loc -> return [PrimValue p]

      Parens e _ -> evalBody env e

      Var name _ _ ->
        do
           val <- lookupVar (qualLeaf name) env
           return [val]

      LetPat _ pat val e _ ->
        let vname = getPatternName pat in -- assume just one for now
        do
          [v] <- evalBody env val
          step (locStr (srclocOf e)
                 ++ ": Binding variable \"" ++ getStringName vname
                 ++ "\" to :" ++ show (pretty v))
            $ evalBody (bindVar (getPatternName pat) v env) e

      BinOp name (e1,_) (e2,_) _ _ ->
        let bname = qualLeaf name
            bino = getBinOp bname
            sname = case bname of VName n _ -> nameToString n in
        do
          [ee1] <- step
                     (locStr (srclocOf e1)
                       ++ ": Evaluating first operand of binop ("
                       ++ sname ++ "): " ++ show (pretty e1))
                     $ evalBody env e1
          [ee2] <- step
                     (locStr (srclocOf e2)
                       ++ ": Evaluating second operand of binop ("
                       ++ sname ++ "): " ++ show (pretty e2))
                     $ evalBody env e2
          step ("Applying binop (" ++ sname ++ ")") $ return [bino ee1 ee2]

      _ ->
        throwError $ Generic "unimplemented"

mkFun :: Monad m => FunBind -> (Name, Fun m)
mkFun fu =
  let name = case funBindName fu of VName n _ -> n
      fun env n =
          let params = case funBindParams fu of
                           [TuplePattern x _] -> x
                           _ -> fail "function was not given expected (...) parameters"
              vtable = zip (map getPatternName params) n in
              -- TODO: needs bounds checking
              -- and support for binding values in-place
              -- (i.e. unique type array inplace modification)
          if length params /= length n
          then throwError $ Generic ("not same parameter length" ++ show n)
          else evalBody (extendVtable vtable env) $ funBindBody fu
          where extendVtable vtable en =
                  en { envVtable = vtable  ++ envVtable en }
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

runFun :: Monad m => Name -> [Value] -> Prog -> EDebugT m [Value]
runFun fname args prog =
  let ftable = buildFunTable prog
      env = FutharkEnv { envVtable = [], envFtable = ftable } in
  case lookup fname ftable of
     Just f -> f env args
     _ -> DebugT $ throwError $ Generic "no function"
