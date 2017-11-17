{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Futhark.Debugger
  ( DebuggerError
  , DebuggerT, debuggerT, stepDebuggerT
  , DebuggerExport(..)
  , DebuggerEnv, dbVtable, dbDepth, dbLocation
  , runFun
  , VTable
  )
where

import Control.Monad.Coroutine
import Control.Monad.Except
import Data.Loc(SrcLoc, noLoc, srclocOf)

import Futhark.Representation.Primitive(intValue, valueIntegral)
import Language.Futhark

{------------------------------------------------------------------------------}
{- TYPES                                                                      -}
{------------------------------------------------------------------------------}

type BaseDebuggerT = Coroutine

stepDebuggerT :: BaseDebuggerT s m a -> m (Either (s (BaseDebuggerT s m a)) a )
stepDebuggerT = resume

debuggerT :: m (Either (s (BaseDebuggerT s m a)) a) -> BaseDebuggerT s m a
debuggerT = Coroutine

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
step env desc m = suspend (DebuggerExport desc env m)

{------------------------------------------------------------------------------}
{- ENVIRONMENT                                                                -}
{------------------------------------------------------------------------------}

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

replaceVtable :: VTable -> DebuggerEnv m -> DebuggerEnv m
replaceVtable vt env =
  env { dbVtable = vt }

lookupFun :: Monad m => Name -> DebuggerEnv m -> DebuggerT m (Fun m)
lookupFun nm env =
  case lookup nm (dbFtable env) of
    Just fun' -> return fun'
    Nothing   -> throwError $ Generic $ "lookupFun " ++ show nm


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
    Id vn _ _ -> vn
    Wildcard _ _ -> VName (nameFromString "wildcardPattern") 1
    PatternAscription p _ -> getPatternName p

-- TODO: make this less sad
getBinOp :: VName -> Value -> Value -> Value
getBinOp vname x y =
  case (baseString vname, x, y) of
    ("+", PrimValue (SignedValue a), PrimValue (SignedValue b)) ->
        let (c,d) = (valueIntegral a, valueIntegral b) :: (Int, Int) in
        PrimValue $ SignedValue $ intValue Int32 (c + d)
    ("-", PrimValue (SignedValue a), PrimValue (SignedValue b)) ->
        let (c,d) = (valueIntegral a, valueIntegral b) :: (Int, Int) in
        PrimValue $ SignedValue $ intValue Int32 (c - d)
    (">", PrimValue (SignedValue a), PrimValue (SignedValue b)) ->
        PrimValue $ BoolValue $ a > b
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

    QualParens _ _ _ ->
      unimp "qual parens"

    TupLit _e _ ->
      unimp "tuple lit"

    RecordLit _fe _ ->
      unimp "record lit"

    ArrayLit _es _type _ ->
      unimp "array lit"

    Range _ _ _ _ ->
      unimp "range"

    Empty _typedecl _ ->
      unimp "empty"

    Var name _comptypebase _ ->
      do
        val <- lookupVar (qualLeaf name) env
        return [val]

    Ascript e _typedecl _ ->
      evalExp e env -- TODO: use type ascription?

    LetPat _ pat val e _ ->
      let vname = getPatternName pat in -- assume just one for now
      do
        [v] <- evalExp val env
        step env ("Binding variable \"" ++ baseString vname
                  ++ "\" to " ++ show (pretty v))
          $ evalExp e $ bindVar (getPatternName pat) v env

    LetFun _vname (_paramtypes, _patterns, _rettypeexp, _structtyp, _exp) _body _ ->
      unimp "let function expression"

    If cond t e _compty _ ->
      do
        [PrimValue (BoolValue ccond)] <- step env
          ("Evaluating condition of if-statement: " ++ show (pretty cond))
          $ evalExp cond env
        if ccond
        then
          step env
            "Evaluating then-branch of if-statement"
            $ evalExp t env
        else
          step env
            "Evaluating else-branch of if-statement"
            $ evalExp e env

    Apply qualname params _compty _ ->
      let (VName n _) = qualLeaf qualname in
      do
        fun' <- lookupFun n env
        pparams <- mapM (\(param, _diet) ->
                    step env
                      ("Evaluating a parameter in call to function: "
                      ++ nameToString n)
                      $ evalExp param env
                  ) params
        step env ("Calling function " ++ show n) $ fun' env (concat pparams)

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

    Project _name _e _comp _ ->
      unimp "project"

    LetWith _id1 _id2 _dim _e1 _e2 _ ->
      unimp "letwith"

    Index _e _dim _ ->
      unimp "index"

    Update _e1 _dim _e2 _ ->
      unimp "update"

    Split _i _e1 _e2 _ ->
      unimp "split"

    Concat _i _e1 _e2 _ ->
      unimp "concat"

    Reshape _e1 _e2 _ ->
      unimp "reshape"

    Rearrange _dims _e _ ->
      unimp "rearrange"

    Rotate _i _e1 _e2 _ ->
      unimp "rotate"

    Map _l _es _ ->
      unimp "map"

    Reduce _com _lamb _e1 _e2 _ ->
      unimp "reduce"

    Scan _l _e1 _e2 _ ->
      unimp "scan"

    Filter _l _e _ ->
      unimp "filter"

    Partition _ls _e _ ->
      unimp "partition"

    Stream _stf _l _e _ ->
      unimp "stream"

    Zip _i _e1 _e2 _ ->
      unimp "zip"

    Unzip _e _types _ ->
      unimp "unzip"

    Unsafe _e _ ->
      unimp "unsafe"

mkFun :: Monad m => FunBind -> (Name, Fun m)
mkFun fu =
  let name = case funBindName fu of VName n _ -> n
      fun env n = -- static scoping, ignore existing vtable
          let vt = zip (map getPatternName (funBindParams fu)) n
              newenv = replaceVtable vt env in
          evalExp (funBindBody fu) newenv
  in
  (name, fun)

mkDec :: [Dec] -> [FunBind]
mkDec decs =
  let only_funcs = filter (\x -> case x of FunDec _ -> True; _ -> False) decs in
  map (\x -> case x of FunDec f -> f; _ -> error "not fundec") only_funcs

-- assume type-checked, therefore it is fine to put all functions within scope
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
