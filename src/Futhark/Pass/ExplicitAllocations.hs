{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, FlexibleContexts, TupleSections, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Futhark.Pass.ExplicitAllocations
       ( explicitAllocations
       , simplifiable

       , arraySizeInBytesExp
       )
where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.RWS.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe

import Prelude hiding (div, mod, quot, rem)

import Futhark.Representation.Kernels
import Futhark.Optimise.Simplifier.Lore
  (mkWiseBody,
   mkWiseLetStm,
   removeExpWisdom,

   removeScopeWisdom)
import Futhark.MonadFreshNames
import Futhark.Representation.ExplicitMemory
import qualified Futhark.Representation.ExplicitMemory.IndexFunction as IxFun
import Futhark.Tools
import qualified Futhark.Analysis.SymbolTable as ST
import Futhark.Optimise.Simplifier.Engine (SimpleOps (..))
import qualified Futhark.Optimise.Simplifier.Engine as Engine
import Futhark.Pass
import Futhark.Util (splitFromEnd)

type InInKernel = Futhark.Representation.Kernels.InKernel
type OutInKernel = Futhark.Representation.ExplicitMemory.InKernel

data AllocStm = SizeComputation VName (PrimExp VName)
              | Allocation VName SubExp Space
              | ArrayCopy VName Bindage VName
                    deriving (Eq, Ord, Show)

bindAllocStm :: (MonadBinder m, Op (Lore m) ~ MemOp inner) =>
                AllocStm -> m ()
bindAllocStm (SizeComputation name pe) =
  letBindNames'_ [name] =<< toExp (coerceIntPrimExp Int64 pe)
bindAllocStm (Allocation name size space) =
  letBindNames'_ [name] $ Op $ Alloc size space
bindAllocStm (ArrayCopy name bindage src) =
  letBindNames_ [(name,bindage)] $ BasicOp $ Copy src

class (MonadFreshNames m, HasScope lore m, ExplicitMemorish lore) =>
      Allocator lore m where
  addAllocStm :: AllocStm -> m ()
  -- | The subexpression giving the number of elements we should
  -- allocate space for.  See 'ChunkMap' comment.
  dimAllocationSize :: SubExp -> m SubExp

  expHints :: Exp lore -> m [ExpHint]
  expHints e = return $ replicate (expExtTypeSize e) NoHint

allocateMemory :: Allocator lore m =>
                  String -> SubExp -> Space -> m VName
allocateMemory desc size space = do
  v <- newVName desc
  addAllocStm $ Allocation v size space
  return v

computeSize :: Allocator lore m =>
               String -> PrimExp VName -> m SubExp
computeSize desc se = do
  v <- newVName desc
  addAllocStm $ SizeComputation v se
  return $ Var v

type Allocable fromlore tolore =
  (ExplicitMemorish tolore,
   SameScope fromlore Kernels,
   RetType fromlore ~ RetType Kernels,
   BranchType fromlore ~ BranchType Kernels,
   BodyAttr fromlore ~ (),
   BodyAttr tolore ~ (),
   ExpAttr tolore ~ (),
   SizeSubst (Op tolore))

-- | A mapping from chunk names to their maximum size.  XXX FIXME
-- HACK: This is part of a hack to add loop-invariant allocations to
-- reduce kernels, because memory expansion does not use range
-- analysis yet (it should).
type ChunkMap = M.Map VName SubExp

data AllocEnv fromlore tolore  =
  AllocEnv { chunkMap :: ChunkMap
           , allocInOp :: Op fromlore -> AllocM fromlore tolore (Op tolore)
           }

boundDims :: ChunkMap -> AllocEnv fromlore tolore
          -> AllocEnv fromlore tolore
boundDims m env = env { chunkMap = m <> chunkMap env }

boundDim :: VName -> SubExp -> AllocEnv fromlore tolore
         -> AllocEnv fromlore tolore
boundDim name se = boundDims $ M.singleton name se

-- | Monad for adding allocations to an entire program.
newtype AllocM fromlore tolore a =
  AllocM (BinderT tolore (ReaderT (AllocEnv fromlore tolore) (State VNameSource)) a)
  deriving (Applicative, Functor, Monad,
             MonadFreshNames,
             HasScope tolore,
             LocalScope tolore,
             MonadReader (AllocEnv fromlore tolore))

instance (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
         MonadBinder (AllocM fromlore tolore) where
  type Lore (AllocM fromlore tolore) = tolore

  mkExpAttrM _ _ = return ()

  mkLetNamesM names e = do
    pat <- patternWithAllocations names e
    return $ Let pat (defAux ()) e

  mkBodyM bnds res = return $ Body () bnds res

  addStm binding =
    AllocM $ addBinderStm binding
  collectStms (AllocM m) =
    AllocM $ collectBinderStms m
  certifying cs (AllocM m) =
    AllocM $ certifyingBinder cs m

instance Allocable fromlore OutInKernel =>
         Allocator ExplicitMemory (AllocM fromlore ExplicitMemory) where
  addAllocStm (SizeComputation name se) =
    letBindNames'_ [name] =<< toExp (coerceIntPrimExp Int64 se)
  addAllocStm (Allocation name size space) =
    letBindNames'_ [name] $ Op $ Alloc size space
  addAllocStm (ArrayCopy name bindage src) =
    letBindNames_ [(name, bindage)] $ BasicOp $ Copy src

  dimAllocationSize (Var v) =
    -- It is important to recurse here, as the substitution may itself
    -- be a chunk size.
    maybe (return $ Var v) dimAllocationSize =<< asks (M.lookup v . chunkMap)
  dimAllocationSize size =
    return size

  expHints = kernelExpHints

instance Allocable fromlore OutInKernel =>
         Allocator OutInKernel (AllocM fromlore OutInKernel) where
  addAllocStm (SizeComputation name se) =
    letBindNames'_ [name] =<< toExp (coerceIntPrimExp Int64 se)
  addAllocStm (Allocation name size space) =
    letBindNames'_ [name] $ Op $ Alloc size space
  addAllocStm (ArrayCopy name bindage src) =
    letBindNames_ [(name, bindage)] $ BasicOp $ Copy src

  dimAllocationSize (Var v) =
    -- It is important to recurse here, as the substitution may itself
    -- be a chunk size.
    maybe (return $ Var v) dimAllocationSize =<< asks (M.lookup v . chunkMap)
  dimAllocationSize size =
    return size

  expHints = inKernelExpHints

runAllocM :: (MonadFreshNames m, BinderOps tolore) =>
             (Op fromlore -> AllocM fromlore tolore (Op tolore))
          -> AllocM fromlore tolore a -> m a
runAllocM handleOp (AllocM m) =
  fmap fst $ modifyNameSource $ runState $ runReaderT (runBinderT m mempty) env
  where env = AllocEnv mempty handleOp

subAllocM :: (SameScope tolore1 tolore2, ExplicitMemorish tolore2, BinderOps tolore1) =>
             (Op fromlore1 -> AllocM fromlore1 tolore1 (Op tolore1))
          -> AllocM fromlore1 tolore1 a
          -> AllocM fromlore2 tolore2 a
subAllocM handleOp (AllocM m) = do
  scope <- castScope <$> askScope
  chunks <- asks chunkMap
  let env = AllocEnv chunks handleOp
  fmap fst $ modifyNameSource $ runState $ runReaderT (runBinderT m scope) env

-- | Monad for adding allocations to a single pattern.
newtype PatAllocM lore a = PatAllocM (RWS
                                      (Scope lore)
                                      [AllocStm]
                                      VNameSource
                                      a)
                    deriving (Applicative, Functor, Monad,
                              HasScope lore,
                              MonadWriter [AllocStm],
                              MonadFreshNames)

instance Allocator ExplicitMemory (PatAllocM ExplicitMemory) where
  addAllocStm = tell . pure
  dimAllocationSize = return

instance Allocator OutInKernel (PatAllocM OutInKernel) where
  addAllocStm = tell . pure
  dimAllocationSize = return

runPatAllocM :: MonadFreshNames m =>
                PatAllocM lore a -> Scope lore
             -> m (a, [AllocStm])
runPatAllocM (PatAllocM m) mems =
  modifyNameSource $ frob . runRWS m mems
  where frob (a,s,w) = ((a,w),s)

arraySizeInBytesExp :: Type -> PrimExp VName
arraySizeInBytesExp t =
  product
    [ toInt64 $ product $ map (primExpFromSubExp int32) (arrayDims t)
    , ValueExp $ IntValue $ Int64Value $ primByteSize $ elemType t ]
  where toInt64 = ConvOpExp $ SExt Int32 Int64

arraySizeInBytesExpM :: Allocator lore m => Type -> m (PrimExp VName)
arraySizeInBytesExpM t = do
  dims <- mapM dimAllocationSize (arrayDims t)
  let dim_prod_i32 = product $ map (primExpFromSubExp int32) dims
  let elm_size_i64 = ValueExp $ IntValue $ Int64Value $ primByteSize $ elemType t
  return $ product [ toInt64 dim_prod_i32, elm_size_i64 ]
  where toInt64 = ConvOpExp $ SExt Int32 Int64

arraySizeInBytes :: Allocator lore m => Type -> m SubExp
arraySizeInBytes = computeSize "bytes" <=< arraySizeInBytesExpM

allocForArray :: Allocator lore m =>
                 Type -> Space -> m (SubExp, VName)
allocForArray t space = do
  size <- arraySizeInBytes t
  m <- allocateMemory "mem" size space
  return (size, m)

allocsForStm :: (Allocator lore m, ExpAttr lore ~ ()) =>
                [Ident] -> [(Ident,Bindage)] -> Exp lore
             -> m (Stm lore, [AllocStm])
allocsForStm sizeidents validents e = do
  rts <- expReturns e
  hints <- expHints e
  (ctxElems, valElems, postbnds) <- allocsForPattern sizeidents validents rts hints
  return (Let (Pattern ctxElems valElems) (defAux ()) e,
          postbnds)

patternWithAllocations :: (Allocator lore m, ExpAttr lore ~ ()) =>
                          [(VName, Bindage)]
                       -> Exp lore
                       -> m (Pattern lore)
patternWithAllocations names e = do
  (ts',sizes) <- instantiateShapes' =<< expExtType e
  let identForBindage name t BindVar =
        pure (Ident name t, BindVar)
      identForBindage name _ bindage@(BindInPlace src _) = do
        t <- lookupType src
        pure (Ident name t, bindage)
  vals <- sequence [ identForBindage name t bindage  |
                     ((name,bindage), t) <- zip names ts' ]
  (Let pat _ _, extrabnds) <- allocsForStm sizes vals e
  case extrabnds of
    [] -> return pat
    _  -> fail $ "Cannot make allocations for pattern of " ++ pretty e

allocsForPattern :: Allocator lore m =>
                    [Ident] -> [(Ident,Bindage)] -> [ExpReturns] -> [ExpHint]
                 -> m ([PatElem ExplicitMemory],
                       [PatElem ExplicitMemory],
                       [AllocStm])
allocsForPattern sizeidents validents rts hints = do
  let sizes' = [ PatElem size BindVar $ MemPrim int32 | size <- map identName sizeidents ]
  (vals,(mems_and_sizes, postbnds)) <-
    runWriterT $ forM (zip3 validents rts hints) $ \((ident,bindage), rt, hint) -> do
      let shape = arrayShape $ identType ident
      case rt of
        MemPrim _ -> do
          summary <- lift $ summaryForBindage (identType ident) bindage hint
          return $ PatElem (identName ident) bindage summary

        MemMem (Free size) space ->
          return $ PatElem (identName ident) bindage $
          MemMem size space

        MemMem Ext{} space ->
          return $ PatElem (identName ident) bindage $
          MemMem (intConst Int32 0) space

        MemArray bt _ u (Just (ReturnsInBlock mem ixfun)) -> do
          ixfun' <- instantiateIxFun ixfun
          case bindage of
            BindVar ->
              return $ PatElem (identName ident) bindage $
              MemArray bt shape u $ ArrayIn mem ixfun'
            BindInPlace src slice -> do
              (destmem,destixfun) <- lift $ lookupArraySummary src
              if destmem == mem && destixfun == ixfun'
                then return $ PatElem (identName ident) bindage $
                     MemArray bt shape u $ ArrayIn mem ixfun'
                else do
                -- The expression returns at some specific memory
                -- location, but we want to put the result somewhere
                -- else.  This means we need to store it in the memory
                -- it wants to first, then copy it to our intended
                -- destination in an extra binding.
                tmp_buffer <- lift $
                              newIdent (baseString (identName ident)<>"_ext_buffer")
                              (identType ident `setArrayDims` sliceDims slice)
                tell ([],
                      [ArrayCopy (identName ident) bindage $
                       identName tmp_buffer])
                return $ PatElem (identName tmp_buffer) BindVar $
                  MemArray bt (arrayShape $ identType tmp_buffer) u $
                  ArrayIn mem ixfun'

        MemArray _ extshape _ Nothing
          | Just _ <- knownShape extshape -> do
            summary <- lift $ summaryForBindage (identType ident) bindage hint
            return $ PatElem (identName ident) bindage summary

        MemArray bt _ u (Just ReturnsNewBlock{})
          | BindInPlace _ slice <- bindage -> do
              -- The expression returns its own memory, but the pattern
              -- wants to store it somewhere else.  We first let it
              -- store the value where it wants, then we copy it to the
              -- intended destination.  In some cases, the copy may be
              -- optimised away later, but in some cases it may not be
              -- possible (e.g. function calls).
              tmp_buffer <- lift $
                            newIdent (baseString (identName ident)<>"_ext_buffer")
                            (identType ident `setArrayDims` sliceDims slice)
              (memsize,mem,(_,ixfun)) <- lift $ memForBindee tmp_buffer
              tell ([PatElem (identName memsize) BindVar $ MemPrim int64,
                     PatElem (identName mem)     BindVar $ MemMem (Var $ identName memsize) DefaultSpace],
                    [ArrayCopy (identName ident) bindage $
                     identName tmp_buffer])
              return $ PatElem (identName tmp_buffer) BindVar $
                MemArray bt (arrayShape $ identType tmp_buffer) u $
                ArrayIn (identName mem) ixfun

        MemArray bt _ u _ -> do
          (memsize,mem,(ident',ixfun)) <- lift $ memForBindee ident
          tell ([PatElem (identName memsize) BindVar $ MemPrim int64,
                 PatElem (identName mem)     BindVar $ MemMem (Var $ identName memsize) DefaultSpace],
                [])
          return $ PatElem (identName ident') bindage $ MemArray bt shape u $
            ArrayIn (identName mem) ixfun

  return (sizes' <> mems_and_sizes,
          vals,
          postbnds)
  where knownShape = mapM known . shapeDims
        known (Free v) = Just v
        known Ext{} = Nothing

instantiateIxFun :: Monad m => ExtIxFun -> m IxFun
instantiateIxFun = traverse $ traverse inst
  where inst Ext{} = fail "instantiateIxFun: not yet"
        inst (Free x) = return x

summaryForBindage :: (ExplicitMemorish lore, Allocator lore m) =>
                     Type -> Bindage -> ExpHint
                  -> m (MemBound NoUniqueness)
summaryForBindage (Prim bt) BindVar _ =
  return $ MemPrim bt
summaryForBindage (Mem size space) BindVar _ =
  return $ MemMem size space
summaryForBindage t@(Array bt shape u) BindVar NoHint = do
  (_, m) <- allocForArray t DefaultSpace
  return $ directIndexFunction bt shape u m t
summaryForBindage t BindVar (Hint ixfun space) = do
  let bt = elemType t
  bytes <- computeSize "bytes" $ product $
           fromIntegral (primByteSize (elemType t)::Int64) :
           map (ConvOpExp (SExt Int32 Int64)) (IxFun.base ixfun)
  m <- allocateMemory "mem" bytes space
  return $ MemArray bt (arrayShape t) NoUniqueness $ ArrayIn m ixfun
summaryForBindage _ (BindInPlace src _) _ =
  lookupMemInfo src

memForBindee :: (MonadFreshNames m) =>
                Ident
             -> m (Ident,
                   Ident,
                   (Ident, IxFun))
memForBindee ident = do
  size <- newIdent (memname <> "_size") (Prim int64)
  mem <- newIdent memname $ Mem (Var $ identName size) DefaultSpace
  return (size,
          mem,
          (ident, IxFun.iota $ map (primExpFromSubExp int32) $ arrayDims t))
  where  memname = baseString (identName ident) <> "_mem"
         t       = identType ident

directIndexFunction :: PrimType -> Shape -> u -> VName -> Type -> MemBound u
directIndexFunction bt shape u mem t =
  MemArray bt shape u $ ArrayIn mem $
  IxFun.iota $ map (primExpFromSubExp int32) $ arrayDims t

allocInFParams :: (Allocable fromlore tolore) =>
                  [FParam fromlore] ->
                  ([FParam tolore] -> AllocM fromlore tolore a)
               -> AllocM fromlore tolore a
allocInFParams params m = do
  (valparams, memparams) <-
    runWriterT $ mapM allocInFParam params
  let params' = memparams <> valparams
      summary = scopeOfFParams params'
  localScope summary $ m params'

allocInFParam :: (Allocable fromlore tolore) =>
                 FParam fromlore
              -> WriterT [FParam tolore]
                 (AllocM fromlore tolore) (FParam tolore)
allocInFParam param =
  case paramDeclType param of
    Array bt shape u -> do
      let memname = baseString (paramName param) <> "_mem"
          ixfun = IxFun.iota $ map (primExpFromSubExp int32) $ shapeDims shape
      memsize <- lift $ newVName (memname <> "_size")
      mem <- lift $ newVName memname
      tell [ Param memsize $ MemPrim int64
           , Param mem $ MemMem (Var memsize) DefaultSpace]
      return param { paramAttr =  MemArray bt shape u $ ArrayIn mem ixfun }
    Prim bt ->
      return param { paramAttr = MemPrim bt }
    Mem size space ->
      return param { paramAttr = MemMem size space }

allocInMergeParams :: (Allocable fromlore tolore,
                       Allocator tolore (AllocM fromlore tolore)) =>
                      [VName]
                   -> [(FParam fromlore,SubExp)]
                   -> ([FParam tolore]
                       -> [FParam tolore]
                       -> ([SubExp] -> AllocM fromlore tolore ([SubExp], [SubExp]))
                       -> AllocM fromlore tolore a)
                   -> AllocM fromlore tolore a
allocInMergeParams variant merge m = do
  ((valparams, handle_loop_subexps), mem_and_size_params) <-
    runWriterT $ unzip <$> mapM allocInMergeParam merge
  let mergeparams' = mem_and_size_params <> valparams
      summary = scopeOfFParams mergeparams'

      mk_loop_res ses = do
        (valargs, memargs) <-
          runWriterT $ zipWithM ($) handle_loop_subexps ses
        return (memargs, valargs)

  localScope summary $ m mem_and_size_params valparams mk_loop_res
  where allocInMergeParam (mergeparam, Var v)
          | Array bt shape Unique <- paramDeclType mergeparam,
            loopInvariantShape mergeparam = do
              (mem, ixfun) <- lift $ lookupArraySummary v
              if IxFun.isDirect ixfun
                then return (mergeparam { paramAttr = MemArray bt shape Unique $ ArrayIn mem ixfun },
                             lift . ensureArrayIn (paramType mergeparam) mem ixfun)
                else doDefault mergeparam
        allocInMergeParam (mergeparam, _) = doDefault mergeparam

        doDefault mergeparam = do
          mergeparam' <- allocInFParam mergeparam
          return (mergeparam', linearFuncallArg $ paramType mergeparam)

        variant_names = variant ++ map (paramName . fst) merge
        loopInvariantShape =
          not . any (`elem` variant_names) . subExpVars . arrayDims . paramType

ensureArrayIn :: (Allocable fromlore tolore,
                  Allocator tolore (AllocM fromlore tolore)) =>
                 Type -> VName -> IxFun -> SubExp
              -> AllocM fromlore tolore SubExp
ensureArrayIn _ _ _ (Constant v) =
  fail $ "ensureArrayIn: " ++ pretty v ++ " cannot be an array."
ensureArrayIn t mem ixfun (Var v) = do
  (src_mem, src_ixfun) <- lookupArraySummary v
  if src_mem == mem && src_ixfun == ixfun
    then return $ Var v
    else do copy <- newIdent (baseString v ++ "_ensure_copy") t
            let summary = MemArray (elemType t) (arrayShape t) NoUniqueness $
                          ArrayIn mem ixfun
                pat = Pattern [] [PatElem (identName copy) BindVar summary]
            letBind_ pat $ BasicOp $ Copy v
            return $ Var $ identName copy

ensureDirectArray :: (Allocable fromlore tolore,
                      Allocator tolore (AllocM fromlore tolore)) =>
                     VName -> AllocM fromlore tolore (SubExp, VName, SubExp)
ensureDirectArray v = do
  res <- lookupMemInfo v
  case res of
    MemArray _ shape _ (ArrayIn mem ixfun)
      | fullyDirect shape ixfun -> do
        memt <- lookupType mem
        case memt of
          Mem size _ -> return (size, mem, Var v)
          _          -> fail $
                        pretty mem ++
                        " should be a memory block but has type " ++
                        pretty memt
    _ ->
      -- We need to do a new allocation, copy 'v', and make a new
      -- binding for the size of the memory block.
      allocLinearArray (baseString v) v

allocLinearArray :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
                    String -> VName
                 -> AllocM fromlore tolore (SubExp, VName, SubExp)
allocLinearArray s v = do
  t <- lookupType v
  (size, mem) <- allocForArray t DefaultSpace
  v' <- newIdent s t
  let pat = Pattern [] [PatElem (identName v') BindVar $
                        directIndexFunction (elemType t) (arrayShape t)
                        NoUniqueness mem t]
  addStm $ Let pat (defAux ()) $ BasicOp $ Copy v
  return (size, mem, Var $ identName v')

funcallArgs :: (Allocable fromlore tolore,
                Allocator tolore (AllocM fromlore tolore)) =>
               [(SubExp,Diet)] -> AllocM fromlore tolore [(SubExp,Diet)]
funcallArgs args = do
  (valargs, mem_and_size_args) <- runWriterT $ forM args $ \(arg,d) -> do
    t <- lift $ subExpType arg
    arg' <- linearFuncallArg t arg
    return (arg', d)
  return $ map (,Observe) mem_and_size_args <> valargs

linearFuncallArg :: (Allocable fromlore tolore,
                     Allocator tolore (AllocM fromlore tolore)) =>
                    Type -> SubExp
                 -> WriterT [SubExp] (AllocM fromlore tolore) SubExp
linearFuncallArg Array{} (Var v) = do
  (size, mem, arg') <- lift $ ensureDirectArray v
  tell [size, Var mem]
  return arg'
linearFuncallArg _ arg =
  return arg

explicitAllocations :: Pass Kernels ExplicitMemory
explicitAllocations = simplePass
                      "explicit allocations"
                      "Transform program to explicit memory representation" $
                      intraproceduralTransformation allocInFun

memoryInRetType :: [RetType Kernels] -> [RetType ExplicitMemory]
memoryInRetType ts = evalState (mapM addAttr ts) $ startOfFreeIDRange ts
  where addAttr (Prim t) = return $ MemPrim t
        addAttr Mem{} = fail "memoryInRetType: too much memory"
        addAttr (Array bt shape u) = do
          i <- get <* modify (+2)
          return $ MemArray bt shape u $ ReturnsNewBlock DefaultSpace (i+1) (Ext i) $
            IxFun.iota $ map convert $ shapeDims shape

        convert (Ext i) = LeafExp (Ext i) int32
        convert (Free v) = Free <$> primExpFromSubExp int32 v

startOfFreeIDRange :: [TypeBase ExtShape u] -> Int
startOfFreeIDRange = S.size . shapeContext

allocInFun :: MonadFreshNames m => FunDef Kernels -> m (FunDef ExplicitMemory)
allocInFun (FunDef entry fname rettype params fbody) =
  runAllocM handleOp $ allocInFParams params $ \params' -> do
    fbody' <- insertStmsM $ allocInFunBody (length rettype) fbody
    return $ FunDef entry fname (memoryInRetType rettype) params' fbody'
    where handleOp GroupSize =
            return $ Inner GroupSize
          handleOp NumGroups =
            return $ Inner NumGroups
          handleOp TileSize =
            return $ Inner TileSize
          handleOp (SufficientParallelism se) =
            return $ Inner $ SufficientParallelism se
          handleOp (Kernel desc space ts kbody) = subAllocM handleKernelExp $
            Inner . Kernel desc space ts <$>
            localScope (scopeOfKernelSpace space)
            (allocInKernelBody kbody)

          handleKernelExp (SplitSpace o w i elems_per_thread) =
            return $ Inner $ SplitSpace o w i elems_per_thread
          handleKernelExp (Combine cspace ts active body) =
            Inner . Combine cspace ts active <$> allocInBodyNoDirect body
          handleKernelExp (GroupReduce w lam input) = do
            summaries <- mapM lookupArraySummary arrs
            lam' <- allocInReduceLambda lam summaries
            return $ Inner $ GroupReduce w lam' input
            where arrs = map snd input
          handleKernelExp (GroupScan w lam input) = do
            summaries <- mapM lookupArraySummary arrs
            lam' <- allocInReduceLambda lam summaries
            return $ Inner $ GroupScan w lam' input
            where arrs = map snd input
          handleKernelExp (GroupStream w maxchunk lam accs arrs) = do
            acc_summaries <- mapM accSummary accs
            arr_summaries <- mapM lookupArraySummary arrs
            lam' <- allocInGroupStreamLambda maxchunk lam acc_summaries arr_summaries
            return $ Inner $ GroupStream w maxchunk lam' accs arrs
            where accSummary (Constant v) = return $ MemPrim $ primValueType v
                  accSummary (Var v) = lookupMemInfo v

allocInBodyNoDirect :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
                       Body fromlore -> AllocM fromlore tolore (Body tolore)
allocInBodyNoDirect (Body _ bnds res) =
  allocInStms bnds $ \bnds' ->
    return $ Body () bnds' res

bodyReturnMemCtx :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
                    SubExp -> AllocM fromlore tolore [SubExp]
bodyReturnMemCtx Constant{} =
  return []
bodyReturnMemCtx (Var v) = do
  info <- lookupMemInfo v
  case info of
    MemPrim{} -> return []
    MemMem{} -> return [] -- should not happen
    MemArray _ _ _ (ArrayIn mem _) -> do
      size <- lookupMemSize mem
      return [size, Var mem]

allocInFunBody :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
                  Int -> Body fromlore -> AllocM fromlore tolore (Body tolore)
allocInFunBody num_vals (Body _ bnds res) =
  allocInStms bnds $ \bnds' -> do
    (res'', allocs) <- collectStms $ do
      res' <- mapM ensureDirect res
      let (ctx_res, val_res) = splitFromEnd num_vals res'
      mem_ctx_res <- concat <$> mapM bodyReturnMemCtx val_res
      return $ ctx_res <> mem_ctx_res <> val_res
    return $ Body () (bnds'<>allocs) res''
  where ensureDirect se@Constant{} = return se
        ensureDirect (Var v) = do
          bt <- primType <$> lookupType v
          if bt
            then return $ Var v
            else do (_, _, v') <- ensureDirectArray v
                    return v'

allocInStms :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
               [Stm fromlore] -> ([Stm tolore] -> AllocM fromlore tolore a)
            -> AllocM fromlore tolore a
allocInStms origbnds m = allocInStms' origbnds []
  where allocInStms' [] bnds' =
          m bnds'
        allocInStms' (x:xs) bnds' = do
          allocbnds <- allocInStm' x
          let summaries = scopeOf allocbnds
          localScope summaries $
            local (boundDims $ mconcat $ map sizeSubst allocbnds) $
            allocInStms' xs (bnds'++allocbnds)
        allocInStm' bnd = do
          ((),bnds') <- collectStms $ certifying (stmCerts bnd) $ allocInStm bnd
          return bnds'

allocInStm :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
              Stm fromlore -> AllocM fromlore tolore ()
allocInStm (Let (Pattern sizeElems valElems) _ e) = do
  e' <- allocInExp e
  let sizeidents = map patElemIdent sizeElems
      validents = [ (Ident name t, bindage) | PatElem name bindage t <- valElems ]
  (bnd, bnds) <- allocsForStm sizeidents validents e'
  addStm bnd
  mapM_ addAllocStm bnds

allocInExp :: (Allocable fromlore tolore, Allocator tolore (AllocM fromlore tolore)) =>
              Exp fromlore -> AllocM fromlore tolore (Exp tolore)
allocInExp (DoLoop ctx val form (Body () bodybnds bodyres)) =
  allocInMergeParams mempty ctx $ \_ ctxparams' _ ->
  allocInMergeParams (map paramName ctxparams') val $
  \new_ctx_params valparams' mk_loop_val -> do
  form' <- allocInLoopForm form
  localScope (scopeOf form') $ do
    (valinit_ctx, valinit') <- mk_loop_val valinit
    body' <- insertStmsM $ allocInStms bodybnds $ \bodybnds' -> do
      ((val_ses,valres'),val_retbnds) <- collectStms $ mk_loop_val valres
      return $ Body () (bodybnds'<>val_retbnds) (ctxres++val_ses++valres')
    return $
      DoLoop
      (zip (ctxparams'++new_ctx_params) (ctxinit++valinit_ctx))
      (zip valparams' valinit')
      form' body'
  where (_ctxparams, ctxinit) = unzip ctx
        (_valparams, valinit) = unzip val
        (ctxres, valres) = splitAt (length ctx) bodyres
allocInExp (Apply fname args rettype loc) = do
  args' <- funcallArgs args
  return $ Apply fname args' (memoryInRetType rettype) loc
allocInExp (If cond tbranch fbranch (IfAttr rets ifsort)) = do
  tbranch' <- allocInFunBody (length rets) tbranch
  fbranch' <- allocInFunBody (length rets) fbranch
  let rets' = createBodyReturns rets
  return $ If cond tbranch' fbranch' $ IfAttr rets' ifsort
allocInExp e = mapExpM alloc e
  where alloc =
          identityMapper { mapOnBody = fail "Unhandled Body in ExplicitAllocations"
                         , mapOnRetType = fail "Unhandled RetType in ExplicitAllocations"
                         , mapOnBranchType = fail "Unhandled BranchType in ExplicitAllocations"
                         , mapOnFParam = fail "Unhandled FParam in ExplicitAllocations"
                         , mapOnLParam = fail "Unhandled LParam in ExplicitAllocations"
                         , mapOnOp = \op -> do handle <- asks allocInOp
                                               handle op
                         }

createBodyReturns :: [ExtType] -> [BodyReturns]
createBodyReturns ts =
  evalState (mapM inspect ts) $ S.size $ shapeContext ts
  where inspect (Array pt shape u) = do
          i <- get <* modify (+2)
          return $ MemArray pt shape u $ ReturnsNewBlock DefaultSpace (i+1) (Ext i) $
            IxFun.iota $ map convert $ shapeDims shape
        inspect (Prim pt) =
          return $ MemPrim pt
        inspect (Mem size space) =
          return $ MemMem (Free size) space

        convert (Ext i) = LeafExp (Ext i) int32
        convert (Free v) = Free <$> primExpFromSubExp int32 v

allocInLoopForm :: (Allocable fromlore tolore,
                    Allocator tolore (AllocM fromlore tolore)) =>
                   LoopForm fromlore -> AllocM fromlore tolore (LoopForm tolore)
allocInLoopForm (WhileLoop v) = return $ WhileLoop v
allocInLoopForm (ForLoop i it n loopvars) =
  ForLoop i it n <$> mapM allocInLoopVar loopvars
  where allocInLoopVar (p,a) = do
          (mem, ixfun) <- lookupArraySummary a
          case paramType p of
            Array bt shape u ->
              let ixfun' = IxFun.slice ixfun $
                           fullSliceNum (IxFun.shape ixfun) [DimFix $ LeafExp i int32]
              in return (p { paramAttr = MemArray bt shape u $ ArrayIn mem ixfun' }, a)
            Prim bt ->
              return (p { paramAttr = MemPrim bt }, a)
            Mem size space ->
              return (p { paramAttr = MemMem size space }, a)

allocInReduceLambda :: Lambda InInKernel
                    -> [(VName, IxFun)]
                    -> AllocM InInKernel OutInKernel (Lambda OutInKernel)
allocInReduceLambda lam input_summaries = do
  let (i, other_offset_param, actual_params) =
        partitionChunkedKernelLambdaParameters $ lambdaParams lam
      (acc_params, arr_params) =
        splitAt (length input_summaries) actual_params
      this_index = LeafExp i int32
      other_offset = LeafExp (paramName other_offset_param) int32
  acc_params' <-
    allocInReduceParameters this_index 0 $
    zip acc_params input_summaries
  arr_params' <-
    allocInReduceParameters this_index other_offset $
    zip arr_params input_summaries

  allocInLambda (Param i (MemPrim int32) :
                 other_offset_param { paramAttr = MemPrim int32 } :
                 acc_params' ++ arr_params')
    (lambdaBody lam) (lambdaReturnType lam)

allocInReduceParameters :: PrimExp VName
                        -> PrimExp VName
                        -> [(LParam InInKernel, (VName, IxFun))]
                        -> AllocM InInKernel OutInKernel [LParam ExplicitMemory]
allocInReduceParameters my_id offset = mapM allocInReduceParameter
  where allocInReduceParameter (p, (mem, ixfun)) =
          case paramType p of
            (Array bt shape u) ->
              let ixfun' = IxFun.slice ixfun $
                           fullSliceNum (IxFun.shape ixfun) [DimFix $ my_id + offset]
              in return p { paramAttr = MemArray bt shape u $ ArrayIn mem ixfun' }
            Prim bt ->
              return p { paramAttr = MemPrim bt }
            Mem size space ->
              return p { paramAttr = MemMem size space }

allocInChunkedParameters :: PrimExp VName
                        -> [(LParam InInKernel, (VName, IxFun))]
                        -> AllocM InInKernel OutInKernel [LParam OutInKernel]
allocInChunkedParameters offset = mapM allocInChunkedParameter
  where allocInChunkedParameter (p, (mem, ixfun)) =
          case paramType p of
            Array bt shape u ->
              let ixfun' = IxFun.offsetIndex ixfun offset
              in return p { paramAttr = MemArray bt shape u $ ArrayIn mem ixfun' }
            Prim bt ->
              return p { paramAttr = MemPrim bt }
            Mem size space ->
              return p { paramAttr = MemMem size space }

allocInLambda :: [LParam OutInKernel] -> Body InInKernel -> [Type]
              -> AllocM InInKernel OutInKernel (Lambda OutInKernel)
allocInLambda params body rettype = do
  body' <- localScope (scopeOfLParams params) $
           allocInStms (bodyStms body) $ \bnds' ->
           return $ Body () bnds' $ bodyResult body
  return $ Lambda params body' rettype

allocInKernelBody :: KernelBody InInKernel
                  -> AllocM InInKernel OutInKernel (KernelBody OutInKernel)
allocInKernelBody (KernelBody () stms res) =
  allocInStms stms $ \stms' ->
    return $ KernelBody () stms' res

class SizeSubst op where
  opSizeSubst :: PatternT attr -> op -> ChunkMap

instance SizeSubst (Kernel lore) where
  opSizeSubst _ _ = mempty

instance SizeSubst op => SizeSubst (MemOp op) where
  opSizeSubst pat (Inner op) = opSizeSubst pat op
  opSizeSubst _ _ = mempty

instance SizeSubst (KernelExp lore) where
  opSizeSubst (Pattern _ [size]) (SplitSpace _ _ _ elems_per_thread) =
    M.singleton (patElemName size) elems_per_thread
  opSizeSubst _ _ = mempty

sizeSubst :: SizeSubst (Op lore) => Stm lore -> ChunkMap
sizeSubst (Let pat _ (Op op)) = opSizeSubst pat op
sizeSubst _ = mempty

allocInGroupStreamLambda :: SubExp
                         -> GroupStreamLambda InInKernel
                         -> [MemBound NoUniqueness]
                         -> [(VName, IxFun)]
                         -> AllocM InInKernel OutInKernel (GroupStreamLambda OutInKernel)
allocInGroupStreamLambda maxchunk lam acc_summaries arr_summaries = do
  let GroupStreamLambda block_size block_offset acc_params arr_params body = lam

  acc_params' <-
    allocInAccParameters acc_params acc_summaries
  arr_params' <-
    allocInChunkedParameters (LeafExp block_offset int32) $
    zip arr_params arr_summaries

  body' <- localScope (M.insert block_size (IndexInfo Int32) $
                       M.insert block_offset (IndexInfo Int32) $
                       scopeOfLParams $ acc_params' ++ arr_params')  $
           local (boundDim block_size maxchunk) $ do
           body' <- allocInBodyNoDirect body
           insertStmsM $ do
             -- We copy the result of the body to whereever the accumulators are stored.
             mapM_ addStm (bodyStms body')
             let maybeCopyResult r p =
                   case paramAttr p of
                     MemArray _ _ _ (ArrayIn mem ixfun) ->
                       ensureArrayIn (paramType p) mem ixfun r
                     _ ->
                       return r
             resultBodyM =<<
               zipWithM maybeCopyResult (bodyResult body') acc_params'
  return $
    GroupStreamLambda block_size block_offset acc_params' arr_params' body'

allocInAccParameters :: [LParam InInKernel]
                     -> [MemBound NoUniqueness]
                     -> AllocM InInKernel OutInKernel [LParam OutInKernel]
allocInAccParameters = zipWithM allocInAccParameter
  where allocInAccParameter p attr = return p { paramAttr = attr }


mkLetNamesB' :: (ExpAttr (Lore m) ~ (),
                 Op (Lore m) ~ MemOp inner,
                 MonadBinder m,
                 Allocator (Lore m) (PatAllocM (Lore m))) =>
                [(VName, Bindage)] -> Exp (Lore m) -> m (Stm (Lore m))
mkLetNamesB' names e = do
  scope <- askScope
  pat <- bindPatternWithAllocations scope names e
  return $ Let pat (defAux ()) e

instance BinderOps ExplicitMemory where
  mkExpAttrB _ _ = return ()
  mkBodyB stms res = return $ Body () stms res
  mkLetNamesB = mkLetNamesB'

instance BinderOps OutInKernel where
  mkExpAttrB _ _ = return ()
  mkBodyB stms res = return $ Body () stms res
  mkLetNamesB = mkLetNamesB'

simplifiable :: (Engine.SimplifiableLore lore,
                 ExpAttr lore ~ (),
                 BodyAttr lore ~ (),
                 Op lore ~ MemOp inner,
                 Allocator lore (PatAllocM lore)) =>
                (inner -> Engine.SimpleM lore (Engine.OpWithWisdom inner))
             -> SimpleOps lore
simplifiable simplifyInnerOp =
  SimpleOps mkExpAttrS' mkBodyS' mkLetNamesS' simplifyOp
  where mkExpAttrS' _ pat e =
          return $ Engine.mkWiseExpAttr pat () e

        mkBodyS' _ bnds res = return $ mkWiseBody () bnds res

        mkLetNamesS' vtable names e = do
          pat' <- bindPatternWithAllocations env names $
                  removeExpWisdom e
          return $ mkWiseLetStm pat' (defAux ()) e
          where env = removeScopeWisdom $ ST.toScope vtable

        simplifyOp (Alloc size space) = Alloc <$> Engine.simplify size <*> pure space
        simplifyOp (Inner k) = Inner <$> simplifyInnerOp k

bindPatternWithAllocations :: (MonadBinder m,
                               ExpAttr lore ~ (),
                               Op (Lore m) ~ MemOp inner,
                               Allocator lore (PatAllocM lore)) =>
                              Scope lore -> [(VName, Bindage)] -> Exp lore
                           -> m (Pattern lore)
bindPatternWithAllocations types names e = do
  (pat,prebnds) <- runPatAllocM (patternWithAllocations names e) types
  mapM_ bindAllocStm prebnds
  return pat

data ExpHint = NoHint
             | Hint IxFun Space

kernelExpHints :: (Allocator lore m, Op lore ~ MemOp (Kernel somelore)) =>
                  Exp lore -> m [ExpHint]
kernelExpHints (BasicOp (Manifest perm v)) = do
  dims <- arrayDims <$> lookupType v
  let perm_inv = rearrangeInverse perm
      dims' = rearrangeShape perm dims
      ixfun = IxFun.permute (IxFun.iota $ map (primExpFromSubExp int32) dims')
              perm_inv
  return [Hint ixfun DefaultSpace]
kernelExpHints (Op (Inner (Kernel _ space rets kbody))) =
  zipWithM hint rets $ kernelBodyResult kbody
  where num_threads = spaceNumThreads space

        spacy AllThreads = Just [num_threads]
        spacy ThreadsInSpace = Just $ map snd $ spaceDimensions space
        spacy _ = Nothing

        -- Heuristic: do not rearrange for returned arrays that are
        -- sufficiently small.
        coalesceReturnOfShape _ [] = False
        coalesceReturnOfShape bs [Constant (IntValue (Int32Value d))] = bs * d > 4
        coalesceReturnOfShape _ _ = True

        innermost space_dims t_dims =
          let r = length t_dims
              dims = space_dims ++ t_dims
              perm = [length space_dims..length space_dims+r-1] ++
                     [0..length space_dims-1]
              perm_inv = rearrangeInverse perm
              dims_perm = rearrangeShape perm dims
              ixfun_base = IxFun.iota $ map (primExpFromSubExp int32) dims_perm
              ixfun_rearranged = IxFun.permute ixfun_base perm_inv
          in ixfun_rearranged

        hint t (ThreadsReturn threads _)
          | coalesceReturnOfShape (primByteSize (elemType t)) $ arrayDims t,
            Just space_dims <- spacy threads = do
              t_dims <- mapM dimAllocationSize $ arrayDims t
              return $ Hint (innermost space_dims t_dims) DefaultSpace

        hint t (ConcatReturns SplitStrided{} w _ _ _) = do
          t_dims <- mapM dimAllocationSize $ arrayDims t
          return $ Hint (innermost [w] t_dims) DefaultSpace

        -- TODO: Can we make hint for ConcatRetuns when it has an offset?
        hint Prim{} (ConcatReturns SplitContiguous w elems_per_thread Nothing _) = do
          let ixfun_base = IxFun.iota $ map (primExpFromSubExp int32) [num_threads,elems_per_thread]
              ixfun_tr = IxFun.permute ixfun_base [1,0]
              ixfun = IxFun.reshape ixfun_tr $ map (DimNew . primExpFromSubExp int32) [w]
          return $ Hint ixfun DefaultSpace

        hint _ _ = return NoHint
kernelExpHints e =
  return $ replicate (expExtTypeSize e) NoHint

inKernelExpHints :: (Allocator lore m, Op lore ~ MemOp (KernelExp somelore)) =>
                    Exp lore -> m [ExpHint]
inKernelExpHints (Op (Inner (Combine cspace ts _ _))) =
  forM ts $ \t -> do
    alloc_dims <- mapM dimAllocationSize $ dims ++ arrayDims t
    let ixfun = IxFun.iota $ map (primExpFromSubExp int32) alloc_dims
    return $ Hint ixfun $ Space "local"
  where dims = map snd cspace

inKernelExpHints e =
  return $ replicate (expExtTypeSize e) NoHint
