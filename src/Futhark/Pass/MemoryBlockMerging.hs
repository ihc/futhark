{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Merge memory blocks where possible.
module Futhark.Pass.MemoryBlockMerging
  ( mergeMemoryBlocks
  ) where

import System.IO.Unsafe (unsafePerformIO) -- Just for debugging!

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.List as L
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Pass
import Futhark.Representation.AST
import qualified Futhark.Representation.ExplicitMemory as ExpMem
import Futhark.Analysis.Alias (aliasAnalysis)

import qualified Futhark.Pass.MemoryBlockMerging.DataStructs as DataStructs
import qualified Futhark.Pass.MemoryBlockMerging.LastUse as LastUse
import qualified Futhark.Pass.MemoryBlockMerging.ArrayCoalescing as ArrayCoalescing
-- import qualified Futhark.Pass.MemoryBlockMerging.Interference as Interference


mergeMemoryBlocks :: Pass ExpMem.ExplicitMemory ExpMem.ExplicitMemory
mergeMemoryBlocks = simplePass
                    "merge memory blocks"
                    "Transform program to reuse non-interfering memory blocks"
                    transformProg


transformProg :: MonadFreshNames m => Prog ExpMem.ExplicitMemory -> m (Prog ExpMem.ExplicitMemory)
transformProg prog = do
  let luTabPrg = LastUse.lastUsePrg $ aliasAnalysis prog
      -- envtab = Interference.intrfAnPrg lutab prog
      coaltab = ArrayCoalescing.mkCoalsTab $ aliasAnalysis prog

  let debug = unsafePerformIO $ do
        putStrLn $ replicate 10 '*' ++ " Last use result " ++ replicate 10 '*'
        putStrLn $ replicate 70 '-'
        forM_ (M.assocs luTabPrg) $ \(funName, luTabFun) -> do
          forM_ (M.assocs luTabFun) $ \(stmtName, luNames) -> do
            putStrLn $ "Last uses in function " ++ pretty funName ++ ", statement " ++ pretty stmtName ++ ":"
            putStrLn $ L.intercalate "   " $ map pretty $ S.toList luNames
            putStrLn $ replicate 70 '-'

        -- putStrLn "Allocations result:"
        -- putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (S.toList . Interference.alloc) (M.elems envtab))

        -- putStrLn "Alias result:"
        -- putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (map (Control.Arrow.second S.toList) . M.toList . Interference.alias) (M.elems envtab))

        -- putStrLn "Interference result:"
        -- putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (map (Control.Arrow.second S.toList) . M.toList . Interference.intrf) (M.elems envtab))

        replicateM_ 5 $ putStrLn ""
        putStrLn $ replicate 10 '*' ++ " Coalescings result " ++ "(" ++ show (M.size coaltab) ++ ") " ++ replicate 10 '*'
        putStrLn $ replicate 70 '-'
        forM_ (M.assocs coaltab) $ \(xMem, entry) -> do
          putStrLn $ "Source memory block: " ++ pretty xMem
          putStrLn $ "Destination memory block: " ++ pretty (DataStructs.dstmem entry)
          -- putStrLn $ "Destination index function: " ++ show (DataStructs.dstind entry)
          putStrLn $ "Aliased destination memory blocks: " ++ L.intercalate "   " (map pretty $ S.toList $ DataStructs.alsmem entry)
          putStrLn $ "Variables currently using the source memory block:"
          putStrLn $ L.intercalate "   " $ map pretty (M.keys (DataStructs.vartab entry))
          putStrLn $ replicate 70 '-'

  debug `seq` intraproceduralTransformation (transformFunDef coaltab) prog

transformFunDef :: MonadFreshNames m
                => DataStructs.CoalsTab
                -> FunDef ExpMem.ExplicitMemory
                -> m (FunDef ExpMem.ExplicitMemory)
transformFunDef coaltab fundef = do
  body' <- modifyNameSource $ runState $ runReaderT m coaltab
  return fundef { funDefBody = body' }
  where m = transformBody $ funDefBody fundef

type MergeM = ReaderT DataStructs.CoalsTab (State VNameSource)

transformBody :: Body ExpMem.ExplicitMemory -> MergeM (Body ExpMem.ExplicitMemory)
transformBody (Body () bnds res) = do
  bnds' <- concat <$> mapM transformStm bnds
  let body' = Body () bnds' res

  let debug = unsafePerformIO $ do
        return ()
        -- putStrLn $ pretty body'
        -- putStrLn $ replicate 70 '-'

  debug `seq` return body'

transformStm :: Stm ExpMem.ExplicitMemory -> MergeM [Stm ExpMem.ExplicitMemory]
-- transformStm (Let (Pattern patCtxElems patValElems) () (DoLoop arginis_ctx arginis lform body)) = do
--   arginis' <- mapM (\(Param x m@(ExpMem.ArrayMem _pt _shape u xmem _xixfun), se) -> do
--                        mem <- (findMem x xmem u)
--                        return (Param x (fromMaybe m mem), se)) arginis

--   e' <- mapExpM transform (DoLoop arginis_ctx arginis' lform body)
--   patValElems' <- mapM transformPatValElemT patValElems
--   let pat' = Pattern patCtxElems patValElems'

--   return [Let pat' () e']
--   where transform = identityMapper { mapOnBody = const transformBody }

transformStm (Let (Pattern patCtxElems patValElems) () e) = do
  e' <- mapExpM transform e
  -- patCtxElems' <- mapM transformPatCtxElemT patCtxElems
  patValElems' <- mapM transformPatValElemT patValElems
  let pat' = Pattern patCtxElems patValElems'

  let debug = unsafePerformIO $ do
        return ()
        -- print e'
        -- print pat'
        -- print pat
        -- print pat'
        -- putStrLn $ replicate 70 '-'

  debug `seq` return [Let pat' () e']
  where transform = identityMapper { mapOnBody = const transformBody
                                   , mapOnFParam = transformFParam
                                   }

transformFParam :: FParam ExpMem.ExplicitMemory -> MergeM (FParam ExpMem.ExplicitMemory)
transformFParam (Param x
                 membound_orig@(ExpMem.ArrayMem _pt _shape u xmem _xixfun)) = do
  membound <- newMemBound x xmem u
  return $ Param x $ fromMaybe membound_orig membound
transformFParam fp = return fp

transformPatValElemT :: PatElemT (LetAttr ExpMem.ExplicitMemory)
                     -> MergeM (PatElemT (LetAttr ExpMem.ExplicitMemory))
transformPatValElemT (PatElem x bindage
                      membound_orig@(ExpMem.ArrayMem _pt _shape u xmem _xixfun)) = do
  membound <- newMemBound x xmem u
  return $ PatElem x bindage $ fromMaybe membound_orig membound
transformPatValElemT pe = return pe

newMemBound :: VName -> VName -> u -> MergeM (Maybe (ExpMem.MemBound u))
newMemBound x xmem u = do
  coaltab <- ask
  return $ do
    entry <- M.lookup xmem coaltab
    DataStructs.Coalesced _ (DataStructs.MemBlock pt shape _ xixfun) _ <-
      M.lookup x $ DataStructs.vartab entry
    return $ ExpMem.ArrayMem pt shape u (DataStructs.dstmem entry) xixfun
