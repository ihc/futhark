{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Merge memory blocks where possible.
module Futhark.Pass.MemoryBlockMerging
       ( mergeMemoryBlocks )
       where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.List

import Prelude hiding (div, quot)

import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Pass
import Futhark.Representation.AST
import Futhark.Representation.ExplicitMemory
       hiding (Prog, Body, Stm, Pattern, PatElem,
               BasicOp, Exp, Lambda, ExtLambda, FunDef, FParam, LParam, RetType)

mergeMemoryBlocks :: Pass ExplicitMemory ExplicitMemory
mergeMemoryBlocks = simplePass
                    "merge memory blocks"
                    "Transform program to reuse non-interfering memory blocks" $
                    intraproceduralTransformation transformFunDef

transformFunDef :: MonadFreshNames m => FunDef ExplicitMemory -> m (FunDef ExplicitMemory)
transformFunDef fundec = do
  body' <- modifyNameSource $ runState m
  return fundec { funDefBody = body' }
  where m = transformBody $ funDefBody fundec

type MergeM = State VNameSource

transformBody :: Body ExplicitMemory -> MergeM (Body ExplicitMemory)
transformBody (Body () bnds res) = do
  bnds' <- concat <$> mapM transformStm bnds
  return $ Body () bnds' res

transformStm :: Stm ExplicitMemory -> MergeM [Stm ExplicitMemory]
transformStm (Let pat () e) = do
  (bnds, e') <- transformExp =<< mapExpM transform e
  return $ bnds ++ [Let pat () e']
  where transform = identityMapper { mapOnBody = const transformBody
                                   }
transformExp :: Exp ExplicitMemory -> MergeM ([Stm ExplicitMemory], Exp ExplicitMemory)
transformExp e =
  return ([], e)
