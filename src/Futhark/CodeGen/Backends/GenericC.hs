{-# LANGUAGE QuasiQuotes, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | C code generator framework.
module Futhark.CodeGen.Backends.GenericC
  ( compileProg
  , CParts(..)
  , asLibrary
  , asExecutable

  -- * Pluggable compiler
  , Operations (..)
  , defaultOperations
  , OpCompiler

  , PointerQuals
  , MemoryType
  , WriteScalar
  , writeScalarPointerWithQuals
  , ReadScalar
  , readScalarPointerWithQuals
  , Allocate
  , Deallocate
  , Copy
  , StaticArray

  -- * Monadic compiler interface
  , CompilerM
  , CompilerState (compUserState)
  , getUserState
  , putUserState
  , modifyUserState
  , contextContents
  , contextFinalInits
  , runCompilerM
  , blockScope
  , compileFun
  , compileCode
  , compileExp
  , compilePrimExp
  , compilePrimValue
  , compileExpToName
  , dimSizeToExp
  , rawMem
  , item
  , stm
  , stms
  , decl
  , atInit
  , headerDecl
  , debugReport
  , HeaderSection(..)
  , libDecl
  , earlyDecls
  , publicName
  , contextType
  , contextField

  -- * Building Blocks
  , primTypeToCType
  , copyMemoryDefaultSpace
  ) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import qualified Data.Map.Strict as M
import qualified Data.DList as DL
import Data.List
import Data.Maybe
import Data.FileEmbed
import Data.Ord
import Data.Hashable

import Prelude

import qualified Language.C.Syntax as C
import qualified Language.C.Quote.OpenCL as C

import Futhark.CodeGen.ImpCode hiding (dimSizeToExp)
import Futhark.MonadFreshNames
import Futhark.CodeGen.Backends.SimpleRepresentation
import Futhark.CodeGen.Backends.GenericC.Options
import Futhark.Util (zEncodeString, mapAccumLM)
import Futhark.Representation.AST.Attributes (isBuiltInFunction, builtInFunctions)


data CompilerState s = CompilerState {
    compTypeStructs :: [([Type], (C.Type, C.Definition))]
  , compArrayStructs :: [((C.Type, Int), (C.Type, [C.Definition]))]
  , compOpaqueStructs :: [(String, (C.Type, [C.Definition]))]
  , compEarlyDecls :: DL.DList C.Definition
  , compInit :: [C.Stm]
  , compNameSrc :: VNameSource
  , compUserState :: s
  , compHeaderDecls :: M.Map HeaderSection (DL.DList C.Definition)
  , compLibDecls :: DL.DList C.Definition
  , compCtxFields :: DL.DList (String, C.Type, Maybe C.Exp)
  , compDebugItems :: DL.DList C.BlockItem
  }

newCompilerState :: VNameSource -> s -> CompilerState s
newCompilerState src s = CompilerState { compTypeStructs = []
                                       , compArrayStructs = []
                                       , compOpaqueStructs = []
                                       , compEarlyDecls = mempty
                                       , compInit = []
                                       , compNameSrc = src
                                       , compUserState = s
                                       , compHeaderDecls = mempty
                                       , compLibDecls = mempty
                                       , compCtxFields = mempty
                                       , compDebugItems = mempty
                                       }

-- | In which part of the header file we put the declaration.  This is
-- to ensure that the header file remains structured and readable.
data HeaderSection = ArrayDecl String
                   | OpaqueDecl String
                   | EntryDecl
                   | MiscDecl
                   | InitDecl
                   deriving (Eq, Ord)

-- | A substitute expression compiler, tried before the main
-- compilation function.
type OpCompiler op s = op -> CompilerM op s ()

-- | The address space qualifiers for a pointer of the given type with
-- the given annotation.
type PointerQuals op s = String -> CompilerM op s [C.TypeQual]

-- | The type of a memory block in the given memory space.
type MemoryType op s = SpaceId -> CompilerM op s C.Type

-- | Write a scalar to the given memory block with the given index and
-- in the given memory space.
type WriteScalar op s =
  C.Exp -> C.Exp -> C.Type -> SpaceId -> Volatility -> C.Exp -> CompilerM op s ()

-- | Read a scalar from the given memory block with the given index and
-- in the given memory space.
type ReadScalar op s =
  C.Exp -> C.Exp -> C.Type -> SpaceId -> Volatility -> CompilerM op s C.Exp

-- | Allocate a memory block of the given size in the given memory
-- space, saving a reference in the given variable name.
type Allocate op s = C.Exp -> C.Exp -> SpaceId
                     -> CompilerM op s ()

-- | De-allocate the given memory block which is in the given memory
-- space.
type Deallocate op s = C.Exp -> SpaceId -> CompilerM op s ()

-- | Create a static array of values - initialised at load time.
type StaticArray op s = VName -> SpaceId -> PrimType -> [PrimValue] -> CompilerM op s ()

-- | Copy from one memory block to another.
type Copy op s = C.Exp -> C.Exp -> Space ->
                 C.Exp -> C.Exp -> Space ->
                 C.Exp ->
                 CompilerM op s ()

data Operations op s =
  Operations { opsWriteScalar :: WriteScalar op s
             , opsReadScalar :: ReadScalar op s
             , opsAllocate :: Allocate op s
             , opsDeallocate :: Deallocate op s
             , opsCopy :: Copy op s
             , opsStaticArray :: StaticArray op s

             , opsMemoryType :: MemoryType op s
             , opsCompiler :: OpCompiler op s

             , opsFatMemory :: Bool
               -- ^ If true, use reference counting.  Otherwise, bare
               -- pointers.
             }

-- | A set of operations that fail for every operation involving
-- non-default memory spaces.  Uses plain pointers and @malloc@ for
-- memory management.
defaultOperations :: Operations op s
defaultOperations = Operations { opsWriteScalar = defWriteScalar
                               , opsReadScalar = defReadScalar
                               , opsAllocate  = defAllocate
                               , opsDeallocate  = defDeallocate
                               , opsCopy = defCopy
                               , opsStaticArray = defStaticArray
                               , opsMemoryType = defMemoryType
                               , opsCompiler = defCompiler
                               , opsFatMemory = True
                               }
  where defWriteScalar _ _ _ _ _ =
          fail "Cannot write to non-default memory space because I am dumb"
        defReadScalar _ _ _ _ =
          fail "Cannot read from non-default memory space"
        defAllocate _ _ _ =
          fail "Cannot allocate in non-default memory space"
        defDeallocate _ _ =
          fail "Cannot deallocate in non-default memory space"
        defCopy destmem destoffset DefaultSpace srcmem srcoffset DefaultSpace size =
          copyMemoryDefaultSpace destmem destoffset srcmem srcoffset size
        defCopy _ _ _ _ _ _ _ =
          fail "Cannot copy to or from non-default memory space"
        defStaticArray _ _ _ _ =
          fail "Cannot create static array in non-default memory space"
        defMemoryType _ =
          fail "Has no type for non-default memory space"
        defCompiler _ =
          fail "The default compiler cannot compile extended operations"

data CompilerEnv op s = CompilerEnv {
    envOperations :: Operations op s
  , envFtable     :: M.Map Name [Type]
  }

data CompilerAcc op s = CompilerAcc {
    accItems :: DL.DList C.BlockItem
  , accDeclaredMem :: [(VName,Space)]
  }

instance Monoid (CompilerAcc op s) where
  CompilerAcc items1 declared1 `mappend` CompilerAcc items2 declared2 =
    CompilerAcc (items1<>items2) (declared1<>declared2)
  mempty = CompilerAcc mempty mempty

envOpCompiler :: CompilerEnv op s -> OpCompiler op s
envOpCompiler = opsCompiler . envOperations

envMemoryType :: CompilerEnv op s -> MemoryType op s
envMemoryType = opsMemoryType . envOperations

envReadScalar :: CompilerEnv op s -> ReadScalar op s
envReadScalar = opsReadScalar . envOperations

envWriteScalar :: CompilerEnv op s -> WriteScalar op s
envWriteScalar = opsWriteScalar . envOperations

envAllocate :: CompilerEnv op s -> Allocate op s
envAllocate = opsAllocate . envOperations

envDeallocate :: CompilerEnv op s -> Deallocate op s
envDeallocate = opsDeallocate . envOperations

envCopy :: CompilerEnv op s -> Copy op s
envCopy = opsCopy . envOperations

envStaticArray :: CompilerEnv op s -> StaticArray op s
envStaticArray = opsStaticArray . envOperations

envFatMemory :: CompilerEnv op s -> Bool
envFatMemory = opsFatMemory . envOperations

newCompilerEnv :: Functions op -> Operations op s
               -> CompilerEnv op s
newCompilerEnv (Functions funs) ops =
  CompilerEnv { envOperations = ops
              , envFtable = ftable <> builtinFtable
              }
  where ftable = M.fromList $ map funReturn funs
        funReturn (name, fun) =
          (name, paramsTypes $ functionOutput fun)
        builtinFtable =
          M.map (map Scalar . snd) builtInFunctions

tupleDefinitions, arrayDefinitions, opaqueDefinitions :: CompilerState s -> [C.Definition]
tupleDefinitions = map (snd . snd) . compTypeStructs
arrayDefinitions = concatMap (snd . snd) . compArrayStructs
opaqueDefinitions = concatMap (snd . snd) . compOpaqueStructs

initDecls, arrayDecls, opaqueDecls, entryDecls, miscDecls :: CompilerState s -> [C.Definition]
initDecls = concatMap (DL.toList . snd) . filter ((==InitDecl) . fst) . M.toList . compHeaderDecls
arrayDecls = concatMap (DL.toList . snd) . filter (isArrayDecl . fst) . M.toList . compHeaderDecls
  where isArrayDecl ArrayDecl{} = True
        isArrayDecl _           = False
opaqueDecls = concatMap (DL.toList . snd) . filter (isOpaqueDecl . fst) . M.toList . compHeaderDecls
  where isOpaqueDecl OpaqueDecl{} = True
        isOpaqueDecl _           = False
entryDecls = concatMap (DL.toList . snd) . filter ((==EntryDecl) . fst) . M.toList . compHeaderDecls
miscDecls = concatMap (DL.toList . snd) . filter ((==MiscDecl) . fst) . M.toList . compHeaderDecls

contextContents :: CompilerM op s ([C.FieldGroup], [C.Stm])
contextContents = do
  (field_names, field_types, field_values) <- gets $ unzip3 . DL.toList . compCtxFields
  let fields = [ [C.csdecl|$ty:ty $id:name;|]
               | (name, ty) <- zip field_names field_types ]
      init_fields = [ [C.cstm|ctx->$id:name = $exp:e;|]
                    | (name, Just e) <- zip field_names field_values ]
  return (fields, init_fields)

contextFinalInits :: CompilerM op s [C.Stm]
contextFinalInits = gets compInit

newtype CompilerM op s a = CompilerM (RWS
                                      (CompilerEnv op s)
                                      (CompilerAcc op s)
                                      (CompilerState s) a)
  deriving (Functor, Applicative, Monad,
            MonadState (CompilerState s),
            MonadReader (CompilerEnv op s),
            MonadWriter (CompilerAcc op s))

instance MonadFreshNames (CompilerM op s) where
  getNameSource = gets compNameSrc
  putNameSource src = modify $ \s -> s { compNameSrc = src }

runCompilerM :: Functions op -> Operations op s -> VNameSource -> s
             -> CompilerM op s a
             -> (a, CompilerState s)
runCompilerM prog ops src userstate (CompilerM m) =
  let (x, s, _) = runRWS m (newCompilerEnv prog ops) (newCompilerState src userstate)
  in (x, s)

getUserState :: CompilerM op s s
getUserState = gets compUserState

putUserState :: s -> CompilerM op s ()
putUserState s = modify $ \compstate -> compstate { compUserState = s }

modifyUserState :: (s -> s) -> CompilerM op s ()
modifyUserState f = modify $ \compstate ->
  compstate { compUserState = f $ compUserState compstate }

atInit :: C.Stm -> CompilerM op s ()
atInit x = modify $ \s ->
  s { compInit = compInit s ++ [x] }

collect :: CompilerM op s () -> CompilerM op s [C.BlockItem]
collect m = pass $ do
  ((), w) <- listen m
  return (DL.toList $ accItems w,
          const w { accItems = mempty })

collect' :: CompilerM op s a -> CompilerM op s (a, [C.BlockItem])
collect' m = pass $ do
  (x, w) <- listen m
  return ((x, DL.toList $ accItems w),
          const w { accItems = mempty})

lookupFunction :: Name -> CompilerM op s [Type]
lookupFunction name = do
  res <- asks $ M.lookup name . envFtable
  case res of
    Nothing -> fail $ "Function " ++ nameToString name ++ " not found."
    Just ts -> return ts

item :: C.BlockItem -> CompilerM op s ()
item x = tell $ mempty { accItems = DL.singleton x }

instance C.ToIdent VName where
  toIdent = C.toIdent . zEncodeString . pretty

instance C.ToExp VName where
  toExp v _ = [C.cexp|$id:v|]

instance C.ToExp IntValue where
  toExp (Int8Value v) = C.toExp v
  toExp (Int16Value v) = C.toExp v
  toExp (Int32Value v) = C.toExp v
  toExp (Int64Value v) = C.toExp v

instance C.ToExp FloatValue where
  toExp (Float32Value v) = C.toExp v
  toExp (Float64Value v) = C.toExp v

instance C.ToExp PrimValue where
  toExp (IntValue v) = C.toExp v
  toExp (FloatValue v) = C.toExp v
  toExp (BoolValue True) = C.toExp (1::Int8)
  toExp (BoolValue False) = C.toExp (0::Int8)
  toExp Checked = C.toExp (1::Int8)

headerDecl :: HeaderSection -> C.Definition -> CompilerM op s ()
headerDecl sec def = modify $ \s ->
  s { compHeaderDecls = M.unionWith (<>) (compHeaderDecls s)
                              (M.singleton sec (DL.singleton def)) }

libDecl :: C.Definition -> CompilerM op s ()
libDecl def = modify $ \s ->
  s { compLibDecls = compLibDecls s <> DL.singleton def }

earlyDecls :: [C.Definition] -> CompilerM op s ()
earlyDecls def = modify $ \s ->
  s { compEarlyDecls = compEarlyDecls s <> DL.fromList def }

contextField :: String -> C.Type -> Maybe C.Exp -> CompilerM op s ()
contextField name ty initial = modify $ \s ->
  s { compCtxFields = compCtxFields s <> DL.singleton (name,ty,initial) }

debugReport :: C.BlockItem -> CompilerM op s ()
debugReport x = modify $ \s ->
  s { compDebugItems = compDebugItems s <> DL.singleton x }

stm :: C.Stm -> CompilerM op s ()
stm (C.Block items _) = mapM_ item items
stm (C.Default s _) = stm s
stm s = item [C.citem|$stm:s|]

stms :: [C.Stm] -> CompilerM op s ()
stms = mapM_ stm

decl :: C.InitGroup -> CompilerM op s ()
decl x = item [C.citem|$decl:x;|]

addrOf :: C.Exp -> C.Exp
addrOf e = [C.cexp|&$exp:e|]

-- | Public names must have a consitent prefix.
publicName :: String -> CompilerM op s String
publicName s = return $ "futhark_" ++ s

-- | The generated code must define a struct with this name.
contextType :: CompilerM op s C.Type
contextType = do
  name <- publicName "context"
  return [C.cty|struct $id:name|]

memToCType :: Space -> CompilerM op s C.Type
memToCType space = do
  refcount <- asks envFatMemory
  if refcount
     then return $ fatMemType space
     else rawMemCType space

rawMemCType :: Space -> CompilerM op s C.Type
rawMemCType DefaultSpace = return defaultMemBlockType
rawMemCType (Space sid) = join $ asks envMemoryType <*> pure sid

fatMemType :: Space -> C.Type
fatMemType space =
  [C.cty|struct $id:name|]
  where name = case space of
          DefaultSpace -> "memblock"
          Space sid    -> "memblock_" ++ sid

fatMemSet :: Space -> String
fatMemSet DefaultSpace = "memblock_set"
fatMemSet (Space sid) = "memblock_set_" ++ sid

fatMemAlloc :: Space -> String
fatMemAlloc DefaultSpace = "memblock_alloc"
fatMemAlloc (Space sid) = "memblock_alloc_" ++ sid

fatMemUnRef :: Space -> String
fatMemUnRef DefaultSpace = "memblock_unref"
fatMemUnRef (Space sid) = "memblock_unref_" ++ sid

rawMem :: C.ToExp a => a -> CompilerM op s C.Exp
rawMem v = rawMem' <$> asks envFatMemory <*> pure v

rawMem' :: C.ToExp a => Bool -> a -> C.Exp
rawMem' True  e = [C.cexp|$exp:e.mem|]
rawMem' False e = [C.cexp|$exp:e|]

defineMemorySpace :: Space -> CompilerM op s (C.Definition, [C.Definition], C.BlockItem)
defineMemorySpace space = do
  rm <- rawMemCType space
  let structdef =
        [C.cedecl|struct $id:sname { int *references;
                                     $ty:rm mem;
                                     typename int64_t size; };|]

  contextField peakname [C.cty|typename int64_t|] $ Just [C.cexp|0|]
  contextField usagename [C.cty|typename int64_t|] $ Just [C.cexp|0|]

  -- Unreferencing a memory block consists of decreasing its reference
  -- count and freeing the corresponding memory if the count reaches
  -- zero.
  free <- case space of
    Space sid -> do free_mem <- asks envDeallocate
                    collect $ free_mem [C.cexp|block->mem|] sid
    DefaultSpace -> return [[C.citem|free(block->mem);|]]
  ctx_ty <- contextType
  let unrefdef = [C.cedecl|static void $id:(fatMemUnRef space) ($ty:ctx_ty *ctx, $ty:mty *block) {
  if (block->references != NULL) {
    *(block->references) -= 1;
    if (ctx->detail_memory) {
      fprintf(stderr, $string:("Unreferencing block in " ++ spacedesc ++ ": %d references remaining.\n"),
              *(block->references));
    }
    if (*(block->references) == 0) {
      ctx->$id:usagename -= block->size;
      $items:free
      free(block->references);
      block->references = NULL;
      if (ctx->detail_memory) {
        fprintf(stderr, "%ld bytes freed (now allocated: %ld bytes)\n",
                block->size, ctx->$id:usagename);
      }
    }
  }
}|]

  -- When allocating a memory block we initialise the reference count to 1.
  alloc <- collect $
    case space of
      DefaultSpace ->
        stm [C.cstm|block->mem = (char*) malloc(size);|]
      Space sid ->
        join $ asks envAllocate <*> pure [C.cexp|block->mem|] <*>
        pure [C.cexp|size|] <*> pure sid
  let allocdef = [C.cedecl|static void $id:(fatMemAlloc space) ($ty:ctx_ty *ctx, $ty:mty *block, typename int32_t size) {
  $id:(fatMemUnRef space)(ctx, block);
  $items:alloc
  block->references = (int*) malloc(sizeof(int));
  *(block->references) = 1;
  block->size = size;
  ctx->$id:usagename += size;
  if (ctx->detail_memory) {
    fprintf(stderr, $string:("Allocated %d bytes in " ++ spacedesc ++ " (now allocated: %ld bytes)"), size, ctx->$id:usagename);
  }
  if (ctx->$id:usagename > ctx->$id:peakname) {
    ctx->$id:peakname = ctx->$id:usagename;
    if (ctx->detail_memory) {
      fprintf(stderr, " (new peak).\n");
    }
  } else if (ctx->detail_memory) {
    fprintf(stderr, ".\n");
  }
  }|]

  -- Memory setting - unreference the destination and increase the
  -- count of the source by one.
  let setdef = [C.cedecl|static void $id:(fatMemSet space) ($ty:ctx_ty *ctx, $ty:mty *lhs, $ty:mty *rhs) {
  $id:(fatMemUnRef space)(ctx, lhs);
  (*(rhs->references))++;
  *lhs = *rhs;
}
|]

  return (structdef,
          [unrefdef, allocdef, setdef],
          [C.citem|fprintf(stderr, $string:("Peak memory usage for " ++ spacedesc ++ ": %ld bytes.\n"),
                           ctx->$id:peakname);|])
  where mty = fatMemType space
        (peakname, usagename, sname, spacedesc) = case space of
          DefaultSpace -> ("peak_mem_usage_default",
                           "cur_mem_usage_default",
                            "memblock",
                            "default space")
          Space sid    -> ("peak_mem_usage_" ++ sid,
                           "cur_mem_usage_" ++ sid,
                           "memblock_" ++ sid,
                           "space '" ++ sid ++ "'")

declMem :: VName -> Space -> CompilerM op s ()
declMem name space = do
  ty <- memToCType space
  decl [C.cdecl|$ty:ty $id:name;|]
  resetMem name
  tell $ mempty { accDeclaredMem = [(name, space)] }

resetMem :: C.ToExp a => a -> CompilerM op s ()
resetMem mem = do
  refcount <- asks envFatMemory
  when refcount $
    stm [C.cstm|$exp:mem.references = NULL;|]

setMem :: (C.ToExp a, C.ToExp b) => a -> b -> Space -> CompilerM op s ()
setMem dest src space = do
  refcount <- asks envFatMemory
  if refcount
    then stm [C.cstm|$id:(fatMemSet space)(ctx, &$exp:dest, &$exp:src);|]
    else stm [C.cstm|$exp:dest = $exp:src;|]

unRefMem :: C.ToExp a => a -> Space -> CompilerM op s ()
unRefMem mem space =
  stm [C.cstm|$id:(fatMemUnRef space)(ctx, &$exp:mem);|]

allocMem :: (C.ToExp a, C.ToExp b) =>
            a -> b -> Space -> CompilerM op s ()
allocMem name size space = do
  refcount <- asks envFatMemory
  if refcount
    then stm [C.cstm|$id:(fatMemAlloc space)(ctx, &$exp:name, $exp:size);|]
    else alloc name
  where alloc dest = case space of
          DefaultSpace ->
            stm [C.cstm|$exp:dest = (char*) malloc($exp:size);|]
          Space sid ->
            join $ asks envAllocate <*> rawMem name <*>
            pure [C.cexp|$exp:size|] <*> pure sid

oneTypeToCType :: Type -> CompilerM op s C.Type
oneTypeToCType (Scalar bt) = return $ primTypeToCType bt
oneTypeToCType (Mem _ space) = memToCType space

typeToCType :: [Type] -> CompilerM op s C.Type
typeToCType t = do
  ty <- gets $ find (sameRepresentation t . fst) . compTypeStructs
  case ty of
    Just (_, (cty, _)) -> return cty
    Nothing -> do
      members <- zipWithM field t [(0::Int)..]
      let name = "futrts_" ++ intercalate "_" (map valueTypeName t)
          struct = [C.cedecl|struct $id:name { $sdecls:members };|]
          stype  = [C.cty|struct $id:name|]
      modify $ \s -> s { compTypeStructs = (t, (stype,struct)) : compTypeStructs s }
      return stype
        where field et i = do
                ct <- oneTypeToCType et
                return [C.csdecl|$ty:ct $id:(tupleField i);|]

  where valueTypeName (Scalar bt) = pretty $ primTypeToCType bt
        valueTypeName (Mem _ (Space space)) = space ++ "_mem"
        valueTypeName (Mem _ DefaultSpace) = "mem"

primTypeInfo :: PrimType -> Signedness -> C.Exp
primTypeInfo (IntType it) t = case (it, t) of
  (Int8,  TypeUnsigned) -> [C.cexp|u8|]
  (Int16, TypeUnsigned) -> [C.cexp|u16|]
  (Int32, TypeUnsigned) -> [C.cexp|u32|]
  (Int64, TypeUnsigned) -> [C.cexp|u64|]
  (Int8,  _) -> [C.cexp|i8|]
  (Int16, _) -> [C.cexp|i16|]
  (Int32, _) -> [C.cexp|i32|]
  (Int64, _) -> [C.cexp|i64|]
primTypeInfo (FloatType Float32) _ = [C.cexp|f32|]
primTypeInfo (FloatType Float64) _ = [C.cexp|f64|]
primTypeInfo Bool _ = [C.cexp|bool|]
primTypeInfo Cert _ = [C.cexp|bool|]

copyMemoryDefaultSpace :: C.Exp -> C.Exp -> C.Exp -> C.Exp -> C.Exp ->
                          CompilerM op s ()
copyMemoryDefaultSpace destmem destidx srcmem srcidx nbytes =
  stm [C.cstm|memmove($exp:destmem + $exp:destidx,
                      $exp:srcmem + $exp:srcidx,
                      $exp:nbytes);|]

paramsTypes :: [Param] -> [Type]
paramsTypes = map paramType
  -- Let's hope we don't need the size for anything, because we are
  -- just making something up.
  where paramType (MemParam _ space) = Mem (ConstSize 0) space
        paramType (ScalarParam _ t) = Scalar t

--- Entry points.

arrayName :: PrimType -> Signedness -> Int -> String
arrayName pt signed rank =
  prettySigned (signed==TypeUnsigned) pt ++ "_" ++ show rank ++ "d"

opaqueName :: String -> [ValueDesc] -> String
opaqueName s vds = "opaque_" ++ zEncodeString (show (hash $ s ++ concatMap p vds)) -- FIXME
  where p (ScalarValue pt signed _) =
          show (pt, signed)
        p (ArrayValue _ _ space pt signed dims) =
          show (space, pt, signed, length dims)

arrayLibraryFunctions :: Space -> PrimType -> Signedness -> [DimSize]
                      -> CompilerM op s [C.Definition]
arrayLibraryFunctions space pt signed shape = do
  let rank = length shape
      pt' = signedPrimTypeToCType signed pt
      name = arrayName pt signed rank
      array_type = [C.cty|struct $id:("futhark_" ++ arrayName pt signed rank)|]

      new_array = "futhark_new_" ++ name
      free_array = "futhark_free_" ++ name
      values_array = "futhark_values_" ++ name
      shape_array = "futhark_shape_" ++ name

      shape_names = [ "dim"++show i | i <- [0..rank-1] ]
      shape_params = [ [C.cparam|int $id:k|] | k <- shape_names ]
      arr_size = cproduct [ [C.cexp|$id:k|] | k <- shape_names ]
      arr_size_array = cproduct [ [C.cexp|arr->shape[$int:i]|] | i <- [0..rank-1] ]
  copy <- asks envCopy

  arr_raw_mem <- rawMem [C.cexp|arr->mem|]

  new_body <- collect $ do
    resetMem [C.cexp|arr->mem|]
    allocMem [C.cexp|arr->mem|] [C.cexp|$exp:arr_size * sizeof($ty:pt')|] space
    copy arr_raw_mem [C.cexp|0|] space
         [C.cexp|data|] [C.cexp|0|] DefaultSpace
         [C.cexp|$exp:arr_size * sizeof($ty:pt')|]
    forM_ [0..rank-1] $ \i ->
      stm [C.cstm|arr->shape[$int:i] = $id:("dim"++show i);|]

  free_body <- collect $ unRefMem [C.cexp|arr->mem|] space

  values_body <- collect $
    copy [C.cexp|data|] [C.cexp|0|] DefaultSpace
         arr_raw_mem [C.cexp|0|] space
         [C.cexp|$exp:arr_size_array * sizeof($ty:pt')|]

  ctx_ty <- contextType

  headerDecl (ArrayDecl name)
    [C.cedecl|$ty:array_type* $id:new_array($ty:ctx_ty *ctx, $ty:pt' *data, $params:shape_params);|]
  headerDecl (ArrayDecl name)
    [C.cedecl|int $id:free_array($ty:ctx_ty *ctx, $ty:array_type *arr);|]
  headerDecl (ArrayDecl name)
    [C.cedecl|int $id:values_array($ty:ctx_ty *ctx, $ty:array_type *arr, $ty:pt' *data);|]
  headerDecl (ArrayDecl name)
    [C.cedecl|typename int64_t* $id:shape_array($ty:ctx_ty *ctx, $ty:array_type *arr);|]

  return [C.cunit|
          $ty:array_type* $id:new_array($ty:ctx_ty *ctx, $ty:pt' *data, $params:shape_params) {
            $ty:array_type *arr = malloc(sizeof($ty:array_type));
            if (arr == NULL) {
              return NULL;
            }
            $items:new_body
            return arr;
          }

          int $id:free_array($ty:ctx_ty *ctx, $ty:array_type *arr) {
            $items:free_body
            free(arr);
            return 0;
          }

          int $id:values_array($ty:ctx_ty *ctx, $ty:array_type *arr, $ty:pt' *data) {
            $items:values_body
            return 0;
          }

          typename int64_t* $id:shape_array($ty:ctx_ty *ctx, $ty:array_type *arr) {
            return arr->shape;
          }
          |]

opaqueLibraryFunctions :: String -> [ValueDesc]
                       -> CompilerM op s [C.Definition]
opaqueLibraryFunctions desc vds = do
  let name = "futhark_" ++ opaqueName desc vds
      free_opaque = "futhark_free_" ++ opaqueName desc vds
      opaque_type = [C.cty|struct $id:name|]

  let freeComponent _ ScalarValue{} =
        return ()
      freeComponent i (ArrayValue _ _ _ pt signed shape) = do
        let rank = length shape
            free_array = "futhark_free_" ++ arrayName pt signed rank
        stm [C.cstm|if ((tmp = $id:free_array(ctx, obj->$id:(tupleField i))) != 0) {
                ret = tmp;
             }|]

  ctx_ty <- contextType

  free_body <- collect $ zipWithM_ freeComponent [0..] vds

  headerDecl (OpaqueDecl desc)
    [C.cedecl|int $id:free_opaque($ty:ctx_ty *ctx, $ty:opaque_type *obj);|]

  return [C.cunit|
          int $id:free_opaque($ty:ctx_ty *ctx, $ty:opaque_type *obj) {
            int ret = 0, tmp;
            $items:free_body
            free(obj);
            return ret;
          }
           |]

valueDescToCType :: ValueDesc -> CompilerM op s C.Type
valueDescToCType (ScalarValue pt signed _) =
  return $ signedPrimTypeToCType signed pt
valueDescToCType (ArrayValue _ _ space pt signed shape) = do
  let pt' = signedPrimTypeToCType signed pt
      rank = length shape
  exists <- gets $ lookup (pt',rank) . compArrayStructs
  case exists of
    Just (cty, _) -> return cty
    Nothing -> do
      memty <- memToCType space
      let name = "futhark_" ++ arrayName pt signed rank
          struct = [C.cedecl|struct $id:name { $ty:memty mem; typename int64_t shape[$int:rank]; };|]
          stype = [C.cty|struct $id:name|]
      headerDecl (ArrayDecl name) [C.cedecl|struct $id:name;|]
      library <- arrayLibraryFunctions space pt signed shape
      modify $ \s -> s { compArrayStructs =
                           ((pt', rank), (stype, struct : library)) : compArrayStructs s
                       }
      return stype

opaqueToCType :: String -> [ValueDesc] -> CompilerM op s C.Type
opaqueToCType desc vds = do
  let name = "futhark_" ++ opaqueName desc vds
  exists <- gets $ lookup name . compOpaqueStructs
  case exists of
    Just (ty, _) -> return ty
    Nothing -> do
      members <- zipWithM field vds [(0::Int)..]
      let struct = [C.cedecl|struct $id:name { $sdecls:members };|]
          stype = [C.cty|struct $id:name|]
      headerDecl (OpaqueDecl desc) [C.cedecl|struct $id:name;|]
      library <- opaqueLibraryFunctions desc vds
      modify $ \s -> s { compOpaqueStructs =
                           (name, (stype, struct : library)) :
                           compOpaqueStructs s }
      return stype
  where field vd@ScalarValue{} i = do
          ct <- valueDescToCType vd
          return [C.csdecl|$ty:ct $id:(tupleField i);|]
        field vd i = do
          ct <- valueDescToCType vd
          return [C.csdecl|$ty:ct *$id:(tupleField i);|]

externalValueToCType :: ExternalValue -> CompilerM op s C.Type
externalValueToCType (TransparentValue vd) = valueDescToCType vd
externalValueToCType (OpaqueValue desc vds) = opaqueToCType desc vds

prepareEntryInputs :: [ExternalValue] -> CompilerM op s [C.Param]
prepareEntryInputs = fmap snd . mapAccumLM prepare mempty . zip [(0::Int)..]
  where prepare known_sizes (pno, TransparentValue vd) = do
          let pname = "in" ++ show pno
          (known_sizes', ty) <- prepareValue known_sizes ([C.cexp|$id:pname|], vd)
          return (known_sizes',
                  [C.cparam|$ty:ty $id:pname|])

        prepare known_sizes (pno, OpaqueValue desc vds) = do
          ty <- opaqueToCType desc vds
          let pname = "in" ++ show pno
              field i ScalarValue{} = [C.cexp|$id:pname->$id:(tupleField i)|]
              field i ArrayValue{} = [C.cexp|$id:pname->$id:(tupleField i)|]
          (known_sizes', _) <-
            mapAccumLM prepareValue known_sizes $ zip (zipWith field [0..] vds) vds
          return (known_sizes',
                  [C.cparam|$ty:ty *$id:pname|])

        prepareValue known_sizes (src, ScalarValue pt signed name) = do
          let pt' = signedPrimTypeToCType signed pt
          stm [C.cstm|$id:name = $exp:src;|]
          return (known_sizes, pt')

        prepareValue known_sizes (src, vd@(ArrayValue mem mem_size _ _ _ shape)) = do
          ty <- valueDescToCType vd

          stm [C.cstm|$exp:mem = $exp:src->mem;|]
          case mem_size of
            VarSize v -> stm [C.cstm|$id:v = $exp:src->mem.size;|]
            ConstSize _ -> return ()


          let rank = length shape
              maybeCopyDim (ConstSize x) i =
                assertSameSize x [C.cexp|$exp:src->shape[$int:i]|]
              maybeCopyDim (VarSize d) i
                | d `elem` known_sizes =
                    assertSameSize d [C.cexp|$exp:src->shape[$int:i]|]
                | otherwise =
                    [C.cstm|$id:d = $exp:src->shape[$int:i];|]

          stms $ zipWith maybeCopyDim shape [0..rank-1]

          return (known_sizes ++ wrote_sizes, [C.cty|$ty:ty*|])

          where wrote_sizes = mapMaybe isVarSize shape
                isVarSize ConstSize{} = Nothing
                isVarSize (VarSize d) = Just d

                assertSameSize expected got =
                  [C.cstm|if ($exp:expected != $exp:got) {
                            fprintf(stderr, "Parameter %s has bad dimension (expected %d, got %d).\n",
                                    $string:(pretty src), $exp:expected, $exp:got);
                            exit(1);
                          }|]

prepareEntryOutputs :: [ExternalValue] -> CompilerM op s [C.Param]
prepareEntryOutputs = zipWithM prepare [(0::Int)..]
  where prepare pno (TransparentValue vd) = do
          let pname = "out" ++ show pno
          ty <- valueDescToCType vd

          case vd of
            ArrayValue{} -> do
              stm [C.cstm|assert((*$id:pname = malloc(sizeof($ty:ty))) != NULL);|]
              prepareValue [C.cexp|*$id:("out" ++ show pno)|] vd
              return [C.cparam|$ty:ty **$id:pname|]
            ScalarValue{} -> do
              prepareValue [C.cexp|*$id:("out" ++ show pno)|] vd
              return [C.cparam|$ty:ty *$id:pname|]

        prepare pno (OpaqueValue desc vds) = do
          let pname = "out" ++ show pno
          ty <- opaqueToCType desc vds
          vd_ts <- mapM valueDescToCType vds

          stm [C.cstm|assert((*$id:pname = malloc(sizeof($ty:ty))) != NULL);|]


          forM_ (zip3 [0..] vd_ts vds) $ \(i,ct,vd) -> do
            let field = [C.cexp|(*$id:("out" ++ show pno))->$id:(tupleField i)|]
            case vd of
              ScalarValue{} -> return ()
              _ -> stm [C.cstm|assert(($exp:field = malloc(sizeof($ty:ct))) != NULL);|]
            prepareValue field vd

          return [C.cparam|$ty:ty **$id:pname|]

        prepareValue dest (ScalarValue _ _ name) =
          stm [C.cstm|$exp:dest = $id:name;|]

        prepareValue dest (ArrayValue mem _ _ _ _ shape) = do
          stm [C.cstm|$exp:dest->mem = $id:mem;|]

          let rank = length shape
              maybeCopyDim (ConstSize x) i =
                [C.cstm|$exp:dest->shape[$int:i] = $int:x;|]
              maybeCopyDim (VarSize d) i =
                [C.cstm|$exp:dest->shape[$int:i] = $id:d;|]
          stms $ zipWith maybeCopyDim shape [0..rank-1]

unpackResults :: VName -> [Param] -> [C.Stm]
unpackResults ret outparams =
  zipWith assign outparams [0..]
  where assign p i = [C.cstm|$id:(paramName p) = $exp:(tupleFieldExp ret i);|]

onEntryPoint :: Name -> Function op
             -> CompilerM op s (C.Definition, C.Definition, C.Initializer)
onEntryPoint fname function@(Function _ outputs inputs _ results args) = do
  ret <- newVName "ret"
  crettype <- typeToCType $ paramsTypes outputs

  let argexps = map (\p -> [C.cexp|$id:(paramName p)|]) inputs

  inputdecls <- collect $ mapM_ stubParam inputs
  outputdecls <- collect $ mapM_ stubParam outputs

  let entry_point_name = nameToString fname
      entry_point_function_name = "futhark_" ++ entry_point_name

  (entry_point_input_params, unpack_entry_inputs) <-
    collect' $ prepareEntryInputs args
  (entry_point_output_params, pack_entry_outputs) <-
    collect' $ prepareEntryOutputs results

  let unpack_ret = unpackResults ret outputs

  (cli_entry_point, cli_init) <- cliEntryPoint fname function

  ctx_ty <- contextType

  headerDecl EntryDecl [C.cedecl|int $id:entry_point_function_name
                                     ($ty:ctx_ty *ctx,
                                      $params:entry_point_output_params,
                                      $params:entry_point_input_params);|]

  return ([C.cedecl|int $id:entry_point_function_name
                         ($ty:ctx_ty *ctx,
                          $params:entry_point_output_params,
                          $params:entry_point_input_params) {
    $items:inputdecls
    $items:outputdecls

    $items:unpack_entry_inputs

    $ty:crettype $id:ret;
    $id:ret = $id:(funName fname)(ctx, $args:argexps);

    $stms:unpack_ret
    $items:pack_entry_outputs

    return 0;
}
    |],
          cli_entry_point,
          cli_init)
  where stubParam (MemParam name space) =
          declMem name space
        stubParam (ScalarParam name ty) = do
          let ty' = primTypeToCType ty
          decl [C.cdecl|$ty:ty' $id:name;|]

--- CLI interface
--
-- Our strategy for CLI entry points is to parse everything into
-- host memory ('DefaultSpace') and copy the result into host memory
-- after the entry point has returned.  We have some ad-hoc frobbery
-- to copy the host-level memory blocks to another memory space if
-- necessary.  This will break if the Futhark entry point uses
-- non-trivial index functions for its input or output.
--
-- The idea here is to keep the nastyness in the wrapper, whilst not
-- messing up anything else.

printPrimStm :: (C.ToExp a, C.ToExp b) => a -> b -> PrimType -> Signedness -> C.Stm
printPrimStm dest val bt ept =
  [C.cstm|write_scalar($exp:dest, binary_output, &$exp:(primTypeInfo bt ept), &$exp:val);|]

-- | Return a statement printing the given external value.
printStm :: ExternalValue -> C.Exp -> CompilerM op s C.Stm
printStm (OpaqueValue desc _) _ =
  return [C.cstm|printf("#<opaque %s>", $string:desc);|]
printStm (TransparentValue (ScalarValue bt ept _)) e =
  return $ printPrimStm [C.cexp|stdout|] e bt ept
printStm (TransparentValue (ArrayValue _ _ _ bt ept shape)) e =
  return [C.cstm|{
      $ty:bt' *arr = calloc(sizeof($ty:bt'), $exp:num_elems);
      assert(arr != NULL);
      assert($id:values_array(ctx, $exp:e, arr) == 0);
      write_array(stdout, binary_output, &$exp:(primTypeInfo bt ept), arr,
                  $id:shape_array(ctx, $exp:e), $int:rank);
      free(arr);
  }|]
  where rank = length shape
        bt' = primTypeToCType bt
        num_elems = cproduct [ [C.cexp|$id:shape_array(ctx, $exp:e)[$int:i]|] | i <- [0..rank-1] ]
        name = arrayName bt ept rank
        values_array = "futhark_values_" ++ name
        shape_array = "futhark_shape_" ++ name

readPrimStm :: C.ToExp a => a -> PrimType -> Signedness -> C.Stm
readPrimStm place t ept =
  [C.cstm|if (read_scalar(&$exp:(primTypeInfo t ept),&$exp:place) != 0) {
        panic(1, "Error when reading input of type %s (errno: %s).\n",
              $exp:(primTypeInfo t ept).type_name,
              strerror(errno));
      }|]

readInputs :: [ExternalValue] -> CompilerM op s [(C.Stm, C.Stm, C.Stm, C.Exp)]
readInputs = mapM readInput

readInput :: ExternalValue -> CompilerM op s (C.Stm, C.Stm, C.Stm, C.Exp)
readInput (OpaqueValue desc _) = do
  stm [C.cstm|panic(1, "Cannot read value of type %s\n", $string:desc);|]
  return ([C.cstm|;|], [C.cstm|;|], [C.cstm|;|], [C.cexp|NULL|])
readInput (TransparentValue (ScalarValue t ept _)) = do
  dest <- newVName "read_value"
  item [C.citem|$ty:(primTypeToCType t) $id:dest;|]
  stm $ readPrimStm dest t ept
  return ([C.cstm|;|], [C.cstm|;|], [C.cstm|;|], [C.cexp|$id:dest|])
readInput (TransparentValue vd@(ArrayValue _ _ _ t ept dims)) = do
  dest <- newVName "read_value"
  shape <- newVName "read_shape"
  arr <- newVName "read_arr"
  ty <- valueDescToCType vd
  item [C.citem|$ty:ty *$id:dest;|]

  let t' = primTypeToCType t
      rank = length dims
      name = arrayName t ept rank
      new_array = "futhark_new_" ++ name
      free_array = "futhark_free_" ++ name
      dims_exps = [ [C.cexp|$id:shape[$int:i]|] | i <- [0..rank-1] ]

  stm [C.cstm|{
     typename int64_t $id:shape[$int:rank];
     $ty:t' *$id:arr = NULL;
     errno = 0;
     if (read_array(&$exp:(primTypeInfo t ept),
                    (void**) &$id:arr,
                    $id:shape,
                    $int:(length dims))
         != 0) {
       panic(1, "Failed reading input of type %s%s (errno: %s).\n",
                 $string:(concat $ replicate rank "[]"),
                 $exp:(primTypeInfo t ept).type_name,
                 strerror(errno));
     }
   }|]

  return ([C.cstm|assert(($exp:dest = $id:new_array(ctx, $id:arr, $args:dims_exps)) != 0);|],
          [C.cstm|assert($id:free_array(ctx, $exp:dest) == 0);|],
          [C.cstm|free($id:arr);|],
          [C.cexp|$id:dest|])

prepareOutputs :: [ExternalValue] -> CompilerM op s [(C.Exp, C.Stm)]
prepareOutputs = mapM prepareResult
  where prepareResult ev = do
          ty <- externalValueToCType ev
          result <- newVName "result"

          case ev of
            TransparentValue ScalarValue{} -> do
              item [C.citem|$ty:ty $id:result;|]
              return ([C.cexp|$id:result|], [C.cstm|;|])
            TransparentValue (ArrayValue _ _ _ t ept dims) -> do
              let name = arrayName t ept $ length dims
                  free_array = "futhark_free_" ++ name
              item [C.citem|$ty:ty *$id:result;|]
              return ([C.cexp|$id:result|],
                      [C.cstm|assert($id:free_array(ctx, $exp:result) == 0);|])
            OpaqueValue desc vds -> do
              let free_opaque = "futhark_free_" ++ opaqueName desc vds
              item [C.citem|$ty:ty *$id:result;|]
              return ([C.cexp|$id:result|],
                      [C.cstm|assert($id:free_opaque(ctx, $exp:result) == 0);|])

printResult :: [(ExternalValue,C.Exp)] -> CompilerM op s [C.Stm]
printResult vs = fmap concat $ forM vs $ \(v,e) -> do
  p <- printStm v e
  return [p, [C.cstm|printf("\n");|]]

cliEntryPoint :: Name
              -> FunctionT a
              -> CompilerM op s (C.Definition, C.Initializer)
cliEntryPoint fname (Function _ _ _ _ results args) = do
  ((pack_input, free_input, free_parsed, input_args), input_items) <-
    collect' $ unzip4 <$> readInputs args

  ((output_vals, free_outputs), output_decls) <-
    collect' $ unzip <$> prepareOutputs results
  printstms <- printResult $ zip results output_vals

  ctx_ty <- contextType
  sync_ctx <- publicName "context_sync"

  let entry_point_name = nameToString fname
      cli_entry_point_function_name = "futrts_cli_entry_" ++ entry_point_name
      entry_point_function_name = "futhark_" ++ entry_point_name

      run_it = [C.citems|
                  /* Run the program once. */
                  $stms:pack_input
                  assert($id:sync_ctx(ctx) == 0);
                  t_start = get_wall_time();
                  assert($id:entry_point_function_name(ctx,
                                                       $args:(map addrOf output_vals),
                                                       $args:input_args) == 0);
                  assert($id:sync_ctx(ctx) == 0);
                  t_end = get_wall_time();
                  long int elapsed_usec = t_end - t_start;
                  if (time_runs && runtime_file != NULL) {
                    fprintf(runtime_file, "%ld\n", elapsed_usec);
                  }
                  $stms:free_input
                |]

  return ([C.cedecl|static void $id:cli_entry_point_function_name($ty:ctx_ty *ctx) {
    typename int64_t t_start, t_end;
    int time_runs;

    /* Declare and read input. */
    $items:input_items
    $items:output_decls

    /* Warmup run */
    if (perform_warmup) {
      time_runs = 0;
      $items:run_it
      $stms:free_outputs
    }
    time_runs = 1;
    /* Proper run. */
    for (int run = 0; run < num_runs; run++) {
      $items:run_it
      if (run < num_runs-1) {
        $stms:free_outputs
      }
    }

    /* Free the parsed input. */
    $stms:free_parsed

    /* Print the final result. */
    $stms:printstms

    $stms:free_outputs
  }
                |],
          [C.cinit|{ .name = $string:entry_point_name,
                      .fun = $id:cli_entry_point_function_name }|]
    )

benchmarkOptions :: [Option]
benchmarkOptions =
   [ Option { optionLongName = "write-runtime-to"
            , optionShortName = Just 't'
            , optionArgument = RequiredArgument
            , optionAction = set_runtime_file
            }
   , Option { optionLongName = "runs"
            , optionShortName = Just 'r'
            , optionArgument = RequiredArgument
            , optionAction = set_num_runs
            }
   , Option { optionLongName = "debugging"
            , optionShortName = Just 'D'
            , optionArgument = NoArgument
            , optionAction = [C.cstm|futhark_context_config_set_debugging(cfg, 1);|]
            }
   , Option { optionLongName = "entry-point"
            , optionShortName = Just 'e'
            , optionArgument = RequiredArgument
            , optionAction = [C.cstm|entry_point = optarg;|]
            }
   , Option { optionLongName = "binary-output"
            , optionShortName = Just 'b'
            , optionArgument = NoArgument
            , optionAction = [C.cstm|binary_output = 1;|]
            }
   ]
  where set_runtime_file = [C.cstm|{
          runtime_file = fopen(optarg, "w");
          if (runtime_file == NULL) {
            panic(1, "Cannot open %s: %s\n", optarg, strerror(errno));
          }
        }|]
        set_num_runs = [C.cstm|{
          num_runs = atoi(optarg);
          perform_warmup = 1;
          if (num_runs <= 0) {
            panic(1, "Need a positive number of runs, not %s\n", optarg);
          }
        }|]

-- | The result of compilation to C is four parts, which can be put
-- together in various ways.  The obvious way is to concatenate all of
-- them, which yields a CLI program.  Another is to compile the
-- library part by itself, and use the header file to call into it.
data CParts = CParts { cHeader :: String
                     , cUtils :: String
                       -- ^ Utility definitions that must be visible
                       -- to both CLI and library parts.
                     , cCLI :: String
                     , cLib :: String
                     }

-- | Produce header and implementation files.
asLibrary :: CParts -> (String, String)
asLibrary parts = (cHeader parts, cUtils parts <> cLib parts)

-- | As executable with command-line interface.
asExecutable :: CParts -> String
asExecutable (CParts a b c d) = a <> b <> c <> d

-- | Compile imperative program to a C program.  Always uses the
-- function named "main" as entry point, so make sure it is defined.
compileProg :: MonadFreshNames m =>
               Operations op s
            -> CompilerM op s ()
            -> s
            -> [Space]
            -> [Option]
            -> Functions op
            -> m CParts
compileProg ops extra userstate spaces options prog@(Functions funs) = do
  src <- getNameSource
  let ((prototypes, definitions, entry_points), endstate) =
        runCompilerM prog ops src userstate compileProg'
      (entry_point_decls, cli_entry_point_decls, entry_point_inits) =
        unzip3 entry_points

  let headerdefs = [C.cunit|
$esc:("#include <stdint.h>")

$esc:("\n/*\n * Initialisation\n*/\n")
$edecls:(initDecls endstate)

$esc:("\n/*\n * Arrays\n*/\n")
$edecls:(arrayDecls endstate)

$esc:("\n/*\n * Opaque values\n*/\n")
$edecls:(opaqueDecls endstate)

$esc:("\n/*\n * Entry points\n*/\n")
$edecls:(entryDecls endstate)

$esc:("\n/*\n * Miscellaneous\n*/\n")
$edecls:(miscDecls endstate)
                           |]

  let utildefs = [C.cunit|
$esc:("#include <stdio.h>")
$esc:("#include <stdlib.h>")
$esc:("#include <assert.h>")

$esc:panic_h

$esc:timing_h
|]

  let clidefs = [C.cunit|
$esc:("#include <string.h>")
$esc:("#include <stdint.h>")
$esc:("#include <inttypes.h>")
$esc:("#include <errno.h>")
$esc:("#include <ctype.h>")
$esc:("#include <errno.h>")
$esc:("#include <getopt.h>")

$esc:values_h

static int binary_output = 0;
static typename FILE *runtime_file;
static int perform_warmup = 0;
static int num_runs = 1;
static const char *entry_point = "main";

$func:(generateOptionParser "parse_options" (benchmarkOptions++options))

$edecls:cli_entry_point_decls

typedef void entry_point_fun(struct futhark_context*);

struct entry_point_entry {
  const char *name;
  entry_point_fun *fun;
};

int main(int argc, char** argv) {
  fut_progname = argv[0];

  struct entry_point_entry entry_points[] = {
    $inits:entry_point_inits
  };

  struct futhark_context_config *cfg = futhark_context_config_new();
  assert(cfg != NULL);

  int parsed_options = parse_options(cfg, argc, argv);
  argc -= parsed_options;
  argv += parsed_options;

  struct futhark_context *ctx = futhark_context_new(cfg);
  assert (ctx != NULL);

  int num_entry_points = sizeof(entry_points) / sizeof(entry_points[0]);
  entry_point_fun *entry_point_fun = NULL;
  for (int i = 0; i < num_entry_points; i++) {
    if (strcmp(entry_points[i].name, entry_point) == 0) {
      entry_point_fun = entry_points[i].fun;
      break;
    }
  }

  if (entry_point_fun == NULL) {
    fprintf(stderr, "No entry point '%s'.  Select another with --entry-point.  Options are:\n",
                    entry_point);
    for (int i = 0; i < num_entry_points; i++) {
      fprintf(stderr, "%s\n", entry_points[i].name);
    }
    return 1;
  }

  entry_point_fun(ctx);

  if (runtime_file != NULL) {
    fclose(runtime_file);
  }

  futhark_debugging_report(ctx);

  futhark_context_free(ctx);
  futhark_context_config_free(cfg);
  return 0;
}
                        |]

  let libdefs = [C.cunit|
$esc:("#ifdef _MSC_VER\n#define inline __inline\n#endif")
$esc:("#include <string.h>")
$esc:("#include <stdint.h>")
$esc:("#include <inttypes.h>")
$esc:("#include <math.h>")
$esc:("#include <ctype.h>")
$esc:("#include <errno.h>")
$esc:("#include <assert.h>")

$edecls:(DL.toList (compEarlyDecls endstate))

$edecls:(DL.toList (compLibDecls endstate))

$edecls:(tupleDefinitions endstate)

$edecls:prototypes

$edecls:builtin

$edecls:(map funcToDef definitions)

$edecls:(arrayDefinitions endstate)

$edecls:(opaqueDefinitions endstate)

$edecls:entry_point_decls
  |]

  return $ CParts (pretty headerdefs) (pretty utildefs) (pretty clidefs) (pretty libdefs)
  where compileProg' = do
          (memstructs, memfuns, memreport) <- unzip3 <$> mapM defineMemorySpace spaces

          (prototypes, definitions) <- unzip <$> mapM compileFun funs

          mapM_ libDecl memstructs
          extra
          mapM_ libDecl $ concat memfuns
          debugreport <- gets $ DL.toList . compDebugItems

          ctx_ty <- contextType
          headerDecl MiscDecl [C.cedecl|void futhark_debugging_report($ty:ctx_ty *ctx);|]
          libDecl [C.cedecl|void futhark_debugging_report($ty:ctx_ty *ctx) {
  if (ctx->detail_memory) {
    $items:memreport
  }
  if (ctx->debugging) {
    $items:debugreport
  }
}|]

          entry_points <- mapM (uncurry onEntryPoint) $
                          filter (functionEntry . snd) funs

          return (prototypes, definitions, entry_points)
        funcToDef func = C.FuncDef func loc
          where loc = case func of
                        C.OldFunc _ _ _ _ _ _ l -> l
                        C.Func _ _ _ _ _ l      -> l

        builtin = cIntOps ++ cFloat32Ops ++ cFloat64Ops ++ cFloatConvOps ++
                  cFloat32Funs ++ cFloat64Funs

        panic_h = $(embedStringFile "rts/c/panic.h")
        values_h = $(embedStringFile "rts/c/values.h")
        timing_h = $(embedStringFile "rts/c/timing.h")

compileFun :: (Name, Function op) -> CompilerM op s (C.Definition, C.Func)
compileFun (fname, Function _ outputs inputs body _ _) = do
  args' <- mapM compileInput inputs
  (retval, body') <- blockScope' $ do
    mapM_ compileOutput outputs
    compileFunBody outputs body
  crettype <- typeToCType $ paramsTypes outputs
  ctx_ty <- contextType
  return ([C.cedecl|static $ty:crettype $id:(funName fname)($ty:ctx_ty *ctx, $params:args');|],
          [C.cfun|static $ty:crettype $id:(funName fname)($ty:ctx_ty *ctx, $params:args') {
             $items:body'
             return $id:retval;
}|])
  where compileInput (ScalarParam name bt) = do
          let ctp = primTypeToCType bt
          return [C.cparam|$ty:ctp $id:name|]
        compileInput (MemParam name space) = do
          ty <- memToCType space
          return [C.cparam|$ty:ty $id:name|]

        compileOutput (ScalarParam name bt) = do
          let ctp = primTypeToCType bt
          decl [C.cdecl|$ty:ctp $id:name;|]
        compileOutput (MemParam name space) =
          declMem name space

compilePrimValue :: PrimValue -> C.Exp

compilePrimValue (IntValue (Int8Value k)) = [C.cexp|$int:k|]
compilePrimValue (IntValue (Int16Value k)) = [C.cexp|$int:k|]
compilePrimValue (IntValue (Int32Value k)) = [C.cexp|$int:k|]
compilePrimValue (IntValue (Int64Value k)) = [C.cexp|$int:k|]

compilePrimValue (FloatValue (Float64Value x))
  | isInfinite x =
      if x > 0 then [C.cexp|INFINITY|] else [C.cexp|-INFINITY|]
  | isNaN x =
      [C.cexp|NAN|]
  | otherwise =
      [C.cexp|$double:x|]
compilePrimValue (FloatValue (Float32Value x))
  | isInfinite x =
      if x > 0 then [C.cexp|INFINITY|] else [C.cexp|-INFINITY|]
  | isNaN x =
      [C.cexp|NAN|]
  | otherwise =
      [C.cexp|$float:x|]

compilePrimValue (BoolValue b) =
  [C.cexp|$int:b'|]
  where b' :: Int
        b' = if b then 1 else 0

compilePrimValue Checked =
  [C.cexp|0|]

dimSizeToExp :: DimSize -> C.Exp
dimSizeToExp (ConstSize x) = [C.cexp|$int:x|]
dimSizeToExp (VarSize v)   = [C.cexp|$exp:v|]

derefPointer :: C.Exp -> C.Exp -> C.Type -> C.Exp
derefPointer ptr i res_t =
  [C.cexp|*(($ty:res_t)&($exp:ptr[$exp:i]))|]

writeScalarPointerWithQuals :: PointerQuals op s -> WriteScalar op s
writeScalarPointerWithQuals quals_f dest i elemtype space vol v = do
  quals <- quals_f space
  let quals' = case vol of Volatile -> [C.ctyquals|volatile|] ++ quals
                           Nonvolatile -> quals
      deref = derefPointer dest i
              [C.cty|$tyquals:quals' $ty:elemtype*|]
  stm [C.cstm|$exp:deref = $exp:v;|]

readScalarPointerWithQuals :: PointerQuals op s -> ReadScalar op s
readScalarPointerWithQuals quals_f dest i elemtype space vol = do
  quals <- quals_f space
  let quals' = case vol of Volatile -> [C.ctyquals|volatile|] ++ quals
                           Nonvolatile -> quals
  return $ derefPointer dest i [C.cty|$tyquals:quals' $ty:elemtype*|]

compileExpToName :: String -> PrimType -> Exp -> CompilerM op s VName
compileExpToName _ _ (LeafExp (ScalarVar v) _) =
  return v
compileExpToName desc t e = do
  desc' <- newVName desc
  e' <- compileExp e
  decl [C.cdecl|$ty:(primTypeToCType t) $id:desc' = $e';|]
  return desc'

compileExp :: Exp -> CompilerM op s C.Exp

compileExp = compilePrimExp compileLeaf
  where compileLeaf (ScalarVar src) =
          return [C.cexp|$id:src|]

        compileLeaf (Index src (Count iexp) restype DefaultSpace vol) = do
          src' <- rawMem src
          derefPointer src'
            <$> compileExp iexp
            <*> pure [C.cty|$tyquals:vol' $ty:(primTypeToCType restype)*|]
            where vol' = case vol of Volatile -> [C.ctyquals|volatile|]
                                     Nonvolatile -> []

        compileLeaf (Index src (Count iexp) restype (Space space) vol) =
          join $ asks envReadScalar
          <*> rawMem src <*> compileExp iexp
          <*> pure (primTypeToCType restype) <*> pure space <*> pure vol

        compileLeaf (SizeOf t) =
          return [C.cexp|(sizeof($ty:t'))|]
          where t' = primTypeToCType t

-- | Tell me how to compile a @v@, and I'll Compile any @PrimExp v@ for you.
compilePrimExp :: Monad m => (v -> m C.Exp) -> PrimExp v -> m C.Exp

compilePrimExp _ (ValueExp val) =
  return $ compilePrimValue val

compilePrimExp f (LeafExp v _) =
  f v

compilePrimExp f (UnOpExp Complement{} x) = do
  x' <- compilePrimExp f x
  return [C.cexp|~$exp:x'|]

compilePrimExp f (UnOpExp Not{} x) = do
  x' <- compilePrimExp f x
  return [C.cexp|!$exp:x'|]

compilePrimExp f (UnOpExp Abs{} x) = do
  x' <- compilePrimExp f x
  return [C.cexp|abs($exp:x')|]

compilePrimExp f (UnOpExp (FAbs Float32) x) = do
  x' <- compilePrimExp f x
  return [C.cexp|(float)fabs($exp:x')|]

compilePrimExp f (UnOpExp (FAbs Float64) x) = do
  x' <- compilePrimExp f x
  return [C.cexp|fabs($exp:x')|]

compilePrimExp f (UnOpExp SSignum{} x) = do
  x' <- compilePrimExp f x
  return [C.cexp|($exp:x' > 0) - ($exp:x' < 0)|]

compilePrimExp f (UnOpExp USignum{} x) = do
  x' <- compilePrimExp f x
  return [C.cexp|($exp:x' > 0) - ($exp:x' < 0) != 0|]

compilePrimExp f (CmpOpExp cmp x y) = do
  x' <- compilePrimExp f x
  y' <- compilePrimExp f y
  return $ case cmp of
    CmpEq{} -> [C.cexp|$exp:x' == $exp:y'|]

    FCmpLt{} -> [C.cexp|$exp:x' < $exp:y'|]
    FCmpLe{} -> [C.cexp|$exp:x' <= $exp:y'|]

    _ -> [C.cexp|$id:(pretty cmp)($exp:x', $exp:y')|]

compilePrimExp f (ConvOpExp conv x) = do
  x' <- compilePrimExp f x
  return [C.cexp|$id:(pretty conv)($exp:x')|]

compilePrimExp f (BinOpExp bop x y) = do
  x' <- compilePrimExp f x
  y' <- compilePrimExp f y
  return $ case bop of
             Add{} -> [C.cexp|$exp:x' + $exp:y'|]
             FAdd{} -> [C.cexp|$exp:x' + $exp:y'|]
             Sub{} -> [C.cexp|$exp:x' - $exp:y'|]
             FSub{} -> [C.cexp|$exp:x' - $exp:y'|]
             Mul{} -> [C.cexp|$exp:x' * $exp:y'|]
             FMul{} -> [C.cexp|$exp:x' * $exp:y'|]
             FDiv{} -> [C.cexp|$exp:x' / $exp:y'|]
             Xor{} -> [C.cexp|$exp:x' ^ $exp:y'|]
             And{} -> [C.cexp|$exp:x' & $exp:y'|]
             Or{} -> [C.cexp|$exp:x' | $exp:y'|]
             Shl{} -> [C.cexp|$exp:x' << $exp:y'|]
             LogAnd{} -> [C.cexp|$exp:x' && $exp:y'|]
             LogOr{} -> [C.cexp|$exp:x' || $exp:y'|]
             _ -> [C.cexp|$id:(pretty bop)($exp:x', $exp:y')|]

compileCode :: Code op -> CompilerM op s ()

compileCode (Op op) =
  join $ asks envOpCompiler <*> pure op

compileCode Skip = return ()

compileCode (Comment s code) = do
  items <- blockScope $ compileCode code
  stm [C.cstm|$comment:("// " ++ s)
              { $items:items }
             |]

compileCode (DebugPrint s _ e) = do
  e' <- compileExp e
  stm [C.cstm|if (ctx->debugging) {
          fprintf(stderr, "%s: %d\n", $exp:s, (int)$exp:e');
       }|]

compileCode c
  | Just (name, t, e, c') <- declareAndSet c = do
    let ct = primTypeToCType t
    e' <- compileExp e
    item [C.citem|$ty:ct $id:name = $exp:e';|]
    compileCode c'

compileCode (c1 :>>: c2) = compileCode c1 >> compileCode c2

compileCode (Assert e msg (loc, locs)) = do
  e' <- compileExp e
  stm [C.cstm|if (!$exp:e') {
                   fprintf(stderr, "Assertion failed at %s: %s\n",
                                   $string:stacktrace, $string:msg);
                   exit(1);
                 }|]
  where stacktrace = intercalate " -> " (reverse $ map locStr $ loc:locs)

compileCode (Allocate name (Count e) space) = do
  size <- compileExp e
  allocMem name size space

compileCode (For i it bound body) = do
  let i' = C.toIdent i
      it' = intTypeToCType it
  bound' <- compileExp bound
  body'  <- blockScope $ compileCode body
  stm [C.cstm|for ($ty:it' $id:i' = 0; $id:i' < $exp:bound'; $id:i'++) {
            $items:body'
          }|]

compileCode (While cond body) = do
  cond' <- compileExp cond
  body' <- blockScope $ compileCode body
  stm [C.cstm|while ($exp:cond') {
            $items:body'
          }|]

compileCode (If cond tbranch fbranch) = do
  cond' <- compileExp cond
  tbranch' <- blockScope $ compileCode tbranch
  fbranch' <- blockScope $ compileCode fbranch
  stm $ case (tbranch', fbranch') of
    (_, []) ->
      [C.cstm|if ($exp:cond') { $items:tbranch' }|]
    ([], _) ->
      [C.cstm|if (!($exp:cond')) { $items:fbranch' }|]
    _ ->
      [C.cstm|if ($exp:cond') { $items:tbranch' } else { $items:fbranch' }|]

compileCode (Copy dest (Count destoffset) DefaultSpace src (Count srcoffset) DefaultSpace (Count size)) = do
  destoffset' <- compileExp destoffset
  srcoffset' <- compileExp srcoffset
  size' <- compileExp size
  dest' <- rawMem dest
  src' <- rawMem src
  stm [C.cstm|memmove($exp:dest' + $exp:destoffset',
                      $exp:src' + $exp:srcoffset',
                      $exp:size');|]

compileCode (Copy dest (Count destoffset) destspace src (Count srcoffset) srcspace (Count size)) = do
  copy <- asks envCopy
  join $ copy
    <$> rawMem dest <*> compileExp destoffset <*> pure destspace
    <*> rawMem src <*> compileExp srcoffset <*> pure srcspace
    <*> compileExp size

compileCode (Write dest (Count idx) elemtype DefaultSpace vol elemexp) = do
  dest' <- rawMem dest
  deref <- derefPointer dest'
           <$> compileExp idx
           <*> pure [C.cty|$tyquals:vol' $ty:(primTypeToCType elemtype)*|]
  elemexp' <- compileExp elemexp
  stm [C.cstm|$exp:deref = $exp:elemexp';|]
  where vol' = case vol of Volatile -> [C.ctyquals|volatile|]
                           Nonvolatile -> []

compileCode (Write dest (Count idx) elemtype (Space space) vol elemexp) =
  join $ asks envWriteScalar
    <*> rawMem dest
    <*> compileExp idx
    <*> pure (primTypeToCType elemtype)
    <*> pure space
    <*> pure vol
    <*> compileExp elemexp

compileCode (DeclareMem name space) =
  declMem name space

compileCode (DeclareScalar name t) = do
  let ct = primTypeToCType t
  decl [C.cdecl|$ty:ct $id:name;|]

compileCode (DeclareArray name DefaultSpace t vs) = do
  let ct = primTypeToCType t
      vs' = [[C.cinit|$exp:(compilePrimValue v)|] | v <- vs]
  name_realtype <- newVName $ baseString name ++ "_realtype"
  libDecl [C.cedecl|static $ty:ct $id:name_realtype[$int:(length vs)] = {$inits:vs'};|]
  -- Fake a memory block.
  contextField (pretty name)
    [C.cty|struct memblock|] $
    Just [C.cexp|(struct memblock){NULL, (char*)$id:name_realtype, 0}|]
  item [C.citem|struct memblock $id:name = ctx->$id:name;|]

compileCode (DeclareArray name (Space space) t vs) =
  join $ asks envStaticArray <*>
  pure name <*> pure space <*> pure t <*> pure vs

-- For assignments of the form 'x = x OP e', we generate C assignment
-- operators to make the resulting code slightly nicer.  This has no
-- effect on performance.
compileCode (SetScalar dest (BinOpExp op (LeafExp (ScalarVar x) _) y))
  | dest == x, Just f <- assignmentOperator op = do
      y' <- compileExp y
      stm [C.cstm|$exp:(f dest y');|]

compileCode (SetScalar dest src) = do
  src' <- compileExp src
  stm [C.cstm|$id:dest = $exp:src';|]

compileCode (SetMem dest src space) =
  setMem dest src space

compileCode (Call dests fname args) = do
  args' <- mapM compileArg args
  outtypes <- lookupFunction fname
  crestype <- typeToCType outtypes
  let args'' | isBuiltInFunction fname = args'
             | otherwise = [C.cexp|ctx|] : args'
  case dests of
    [dest] | isBuiltInFunction fname ->
      stm [C.cstm|$id:dest = $id:(funName fname)($args:args'');|]
    _        -> do
      ret <- newVName "call_ret"
      decl [C.cdecl|$ty:crestype $id:ret;|]
      stm [C.cstm|$id:ret = $id:(funName fname)($args:args'');|]
      forM_ (zip [0..] dests) $ \(i,dest) ->
        stm [C.cstm|$id:dest = $exp:(tupleFieldExp ret i);|]
  where compileArg (MemArg m) = return [C.cexp|$exp:m|]
        compileArg (ExpArg e) = compileExp e

blockScope :: CompilerM op s () -> CompilerM op s [C.BlockItem]
blockScope = fmap snd . blockScope'

blockScope' :: CompilerM op s a -> CompilerM op s (a, [C.BlockItem])
blockScope' m = pass $ do
  (x, w) <- listen m
  let items = DL.toList $ accItems w
  releases <- collect $ mapM_ (uncurry unRefMem) $ accDeclaredMem w
  return ((x, items ++ releases),
          const mempty)

compileFunBody :: [Param] -> Code op -> CompilerM op s VName
compileFunBody outputs code = do
  retval <- newVName "retval"
  bodytype <- typeToCType $ paramsTypes outputs
  compileCode code
  decl [C.cdecl|$ty:bodytype $id:retval;|]
  let setRetVal' i (MemParam name space) = do
        let field = tupleFieldExp retval i
        resetMem field
        setMem field name space
      setRetVal' i (ScalarParam name _) =
        stm [C.cstm|$exp:(tupleFieldExp retval i) = $id:name;|]
  zipWithM_ setRetVal' [0..] outputs
  return retval

declareAndSet :: Code op -> Maybe (VName, PrimType, Exp, Code op)
declareAndSet (DeclareScalar name t :>>: (SetScalar dest e :>>: c))
  | name == dest = Just (name, t, e, c)
declareAndSet ((DeclareScalar name t :>>: SetScalar dest e) :>>: c)
  | name == dest = Just (name, t, e, c)
declareAndSet _ = Nothing

assignmentOperator :: BinOp -> Maybe (VName -> C.Exp -> C.Exp)
assignmentOperator Add{}  = Just $ \d e -> [C.cexp|$id:d += $exp:e|]
assignmentOperator Sub{} = Just $ \d e -> [C.cexp|$id:d -= $exp:e|]
assignmentOperator Mul{} = Just $ \d e -> [C.cexp|$id:d *= $exp:e|]
assignmentOperator _     = Nothing

-- | Return an expression multiplying together the given expressions.
-- If an empty list is given, the expression @1@ is returned.
cproduct :: [C.Exp] -> C.Exp
cproduct []     = [C.cexp|1|]
cproduct (e:es) = foldl mult e es
  where mult x y = [C.cexp|$exp:x * $exp:y|]
