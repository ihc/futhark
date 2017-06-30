{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Futhark.Debugger
  ( DebuggerError
  , DebuggerT, debuggerT
  , DebuggerExport(..)
  , DebuggerEnv, dbVtable, dbDepth, dbLocation
  , runFun
  , stepDebuggerT
  , VTable
  )
where

import Control.Monad.Except
import Data.Loc(SrcLoc, noLoc, srclocOf)

import Futhark.Representation.Primitive(intValue, valueIntegral)
import Language.Futhark

{------------------------------------------------------------------------------}
{- TYPES                                                                      -}
{------------------------------------------------------------------------------}

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
type DebuggerT m = BaseDebuggerT (DebuggerExport m) (ExceptT DebuggerError m)

-- error type for interpreter errors
data DebuggerError =
    Generic String
  | Unimplemented String

instance Show DebuggerError where
  show (Generic s) = s
  show (Unimplemented s) = "Unimplemented: " ++ s

-- temporary, until stuff starts not being unimplemented
unimp :: Monad m => String -> DebuggerT m a
unimp s = throwError $ Unimplemented s

instance Monad m => MonadError DebuggerError (DebuggerT m) where
  throwError e = debuggerT $ throwError e
  a `catchError` e =
    debuggerT $ stepDebuggerT a `catchError` (stepDebuggerT . e)

-- functor that we use to wrap information that is exported in a step
data DebuggerExport m a = DebuggerExport String (DebuggerEnv m) a

instance Monad m => Functor (DebuggerExport m) where
  fmap f (DebuggerExport a b c) = DebuggerExport a b (f c)

-- insert one single step with the given environment and description
step :: Monad m
        => DebuggerEnv m -> String -> DebuggerT m a
        -> DebuggerT m a
step env desc m =
  debuggerT $ return $ Right (DebuggerExport desc env m)

{------------------------------------------------------------------------------}
{- ENVIRONMENT                                                                -}
{------------------------------------------------------------------------------}

-- TODO: we probably want this to be only for builtin functions.
type Fun m = DebuggerEnv m -> [Value] -> DebuggerT m [Value]

-- TODO: use maps instead of lists
type FunTable m = [(Name, Fun m)]
type VTable = [(VName, Value)]

-- reader environment for interpreter
data DebuggerEnv m = DebuggerEnv { dbVtable :: VTable
                                 , dbFtable :: FunTable m
                                 , dbDepth :: Int
                                 , dbLocation :: SrcLoc
                                 }

-- used for debugging ... of the debugger!
instance Show (DebuggerEnv m) where
  show d = concatMap (show . fst) (dbVtable d)

newDebuggerEnv :: Monad m => FunTable m -> DebuggerEnv m
newDebuggerEnv ftable =
  DebuggerEnv { dbVtable = []
              , dbFtable = ftable
              , dbDepth = 0
              , dbLocation = noLoc
              }

lookupVar :: Monad m => VName -> DebuggerEnv m -> DebuggerT m Value
lookupVar vname env =
  case lookup vname (dbVtable env) of
    Just val' -> return val'
    Nothing   -> throwError $ Generic $ "lookupVar " ++ show vname

bindVar :: VName -> Value -> DebuggerEnv m -> DebuggerEnv m
bindVar name val env =
  env { dbVtable = (name, val) : dbVtable env }

extendVtable :: VTable -> DebuggerEnv m -> DebuggerEnv m
extendVtable vt env =
  env { dbVtable = vt ++ dbVtable env }

incDepth :: DebuggerEnv m -> DebuggerEnv m
incDepth env =
  env { dbDepth = dbDepth env + 1 }

setLocation :: SrcLoc -> DebuggerEnv m -> DebuggerEnv m
setLocation s env =
  env { dbLocation = s }

{------------------------------------------------------------------------------}
{- HELPERS                                                                    -}
{------------------------------------------------------------------------------}

-- extract variable name sfor vtable bindings
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
        let (c,d) = (valueIntegral a, valueIntegral b) :: (Int, Int) in
        PrimValue $ SignedValue $ intValue Int32 (c + d)
    (op, _, _) ->
        error $ "Debugger error: unimplemented binop (" ++ op ++ ")"

{------------------------------------------------------------------------------}
{- INTERPRETER                                                                -}
{------------------------------------------------------------------------------}

evalExp :: Monad m => Exp -> DebuggerEnv m -> DebuggerT m [Value]
evalExp body ev =
  let env = incDepth $ setLocation (srclocOf body) ev in
  case body of
    Literal p _loc -> return [PrimValue p]

    Parens e _ -> evalExp e env

    TupLit _e _ ->
      unimp "tuple lit"

    RecordLit _fe _ ->
      unimp "record lit"

    ArrayLit _es _type _ ->
      unimp "array lit"

    Empty _typedecl _ ->
      unimp "empty"

    Var name _comptypebase _ ->
      do
        val <- lookupVar (qualLeaf name) env
        return [val]

    Ascript _e _typedecl _ ->
      unimp "ascript"

    LetPat _ pat val e _ ->
      let vname = getPatternName pat in -- assume just one for now
      do
        [v] <- evalExp val env
        step env ("Binding variable \"" ++ baseString vname
                  ++ "\" to " ++ show (pretty v))
          $ evalExp e $ bindVar (getPatternName pat) v env

    LetFun _vname (_paramtypes, _patterns, _rettypeexp, _structtyp, _exp) _body _ ->
      unimp "let function expression"

    If cond _t _e _compty _ ->
      unimp "if"

    Apply _qualname _params _compty _ ->
      unimp "apply"

    Negate _e _ ->
      unimp "numeric negation"

    DoLoop _types _mergepat _initval _looptype _body _ ->
      unimp "do loop"

    BinOp name (e1,_) (e2,_) _ _ ->
      let bname = qualLeaf name
          bino = getBinOp bname
          sname = baseString bname in
      do
        [ee1] <- step env
                   ("Evaluating first operand of binop ("
                     ++ sname ++ "): " ++ show (pretty e1))
                   $ evalExp e1 env
        [ee2] <- step env
                   ("Evaluating second operand of binop ("
                     ++ sname ++ "): " ++ show (pretty e2))
                   $ evalExp e2 env
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
          else evalExp (funBindBody fu) $ extendVtable vt env
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
          Name -> [Value] -> Prog -> (DebuggerT m [Value], DebuggerEnv m)
runFun fname args prog =
  let ftable = buildFunTable prog
      env = newDebuggerEnv ftable in
  case lookup fname ftable of
    Just f -> (f env args, env)
    _ -> (debuggerT $ throwError $ Generic "unknown function", env)
