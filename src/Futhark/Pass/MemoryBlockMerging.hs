{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Merge memory blocks where possible.
module Futhark.Pass.MemoryBlockMerging
  ( mergeMemoryBlocks
  ) where

import System.IO.Unsafe (unsafePerformIO) -- Just for debugging!

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Arrow
import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set      as S


import Prelude hiding (div, quot)

import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Pass
import Futhark.Representation.AST
import Futhark.Representation.ExplicitMemory
       hiding (Prog, Body, Stm, Pattern, PatElem,
               BasicOp, Exp, Lambda, ExtLambda, FunDef, FParam, LParam, RetType)
import Futhark.Analysis.Alias (aliasAnalysis)

import qualified Futhark.Pass.MemoryBlockMerging.Cosmin.DataStructs as CDataStructs
import qualified Futhark.Pass.MemoryBlockMerging.Cosmin.LastUse as CLastUse
import qualified Futhark.Pass.MemoryBlockMerging.Cosmin.ArrayCoalescing as CArrayCoalescing
import qualified Futhark.Pass.MemoryBlockMerging.Cosmin.Interference as CInterference

import Futhark.Pass.MemoryBlockMerging.ArrayCoalescing (findCoalescings)


mergeMemoryBlocks :: Pass ExplicitMemory ExplicitMemory
mergeMemoryBlocks = simplePass
                    "merge memory blocks"
                    "Transform program to reuse non-interfering memory blocks"
                    transformProg

cosminCode :: Prog ExplicitMemory -> IO ()
cosminCode prog = do
  let lutab = CLastUse.lastUsePrg $ aliasAnalysis prog
      envtab = CInterference.intrfAnPrg lutab prog
      coaltab = CArrayCoalescing.mkCoalsTab $ aliasAnalysis prog
      coal_info = map (\env ->
                          (CDataStructs.dstmem env, CDataStructs.dstind env,
                           S.toList $ CDataStructs.alsmem env, M.toList $ CDataStructs.optdeps env,
                           map (\(k, CDataStructs.Coalesced _ (CDataStructs.MemBlock _ _ b indfun) sbst) ->
                                   (k,(b,indfun,M.toList sbst)))
                            $ M.toList $ CDataStructs.vartab env)
                      ) $ M.elems coaltab

  putStrLn "Last use result:"
  putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (map (Control.Arrow.second S.toList) . M.toList) (M.elems lutab))

  putStrLn "Allocations result:"
  putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (S.toList . CInterference.alloc) (M.elems envtab))

  putStrLn "Alias result:"
  putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (map (Control.Arrow.second S.toList) . M.toList . CInterference.alias) (M.elems envtab))

  putStrLn "Interference result:"
  putStrLn $ unlines (map ("  "++) $ lines $ pretty $ concatMap (map (Control.Arrow.second S.toList) . M.toList . CInterference.intrf) (M.elems envtab))

  putStrLn $ "Coalescing result: " ++ pretty (length coaltab)
  putStrLn $ unlines (map ("  "++) $ lines $ pretty coal_info)



analyseProg :: Prog ExplicitMemory -> IO ()
analyseProg prog = do
  let coalescings = findCoalescings prog

  putStrLn "Coalescings:"
  putStrLn $ show coalescings




transformProg :: MonadFreshNames m => Prog ExplicitMemory -> m (Prog ExplicitMemory)
transformProg prog = do

  let debug = unsafePerformIO $ do
        cosminCode prog
        analyseProg prog

  debug `seq` intraproceduralTransformation transformFunDef prog

transformFunDef :: MonadFreshNames m => FunDef ExplicitMemory -> m (FunDef ExplicitMemory)
transformFunDef fundef = do
  -- let (ExpMem.FunDef _ fname _ params body) = fundef
  body' <- modifyNameSource $ runState m
  return fundef { funDefBody = body' }
  where m = transformBody $ funDefBody fundef

type MergeM = State VNameSource

transformBody :: Body ExplicitMemory -> MergeM (Body ExplicitMemory)
transformBody (Body () bnds res) = do
  bnds' <- concat <$> mapM transformStm bnds
  return $ Body () bnds' res

transformStm :: Stm ExplicitMemory -> MergeM [Stm ExplicitMemory]
transformStm (Let pat () e) = do
  (bnds, e') <- transformExp pat =<< mapExpM transform e
  return $ bnds ++ [Let pat () e']
  where transform = identityMapper { mapOnBody = const transformBody
                                   }

transformExp :: Pattern ExplicitMemory -> Exp ExplicitMemory
             -> MergeM ([Stm ExplicitMemory], Exp ExplicitMemory)
transformExp pat (Op (Alloc se sp)) = do
  let se' = se

  let debug = unsafePerformIO $ do
        print pat
        print se
        print sp
        putStrLn "-----"

  -- debug `seq`
  return ([], Op (Alloc se' sp))

transformExp _ e =
  return ([], e)
