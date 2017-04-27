{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Array coalescing.
module Futhark.Pass.MemoryBlockMerging.ArrayCoalescing
  ( findCoalescings
  ) where

import System.IO.Unsafe (unsafePerformIO) -- Just for debugging!

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Futhark.Representation.AST.Attributes.Scope
import Futhark.Analysis.Alias (aliasAnalysis)
import Futhark.Analysis.PrimExp.Convert
import Futhark.Representation.Aliases
import qualified Futhark.Representation.ExplicitMemory as ExpMem
import qualified Futhark.Representation.ExplicitMemory.IndexFunction as IxFun


data MemoryBlock = MemoryBlock
  { dest :: VName
    -- ^ destination memory block
  , destIx :: ExpMem.IxFun
    -- ^ index function of the destination (used for rebasing)
  }
  deriving (Show)

-- | A mapping from source variables to their new memory blocks.
type Coalescings = M.Map VName MemoryBlock

findCoalescings :: Prog ExpMem.ExplicitMemory -> Coalescings
findCoalescings prog =
  let prog' = aliasAnalysis prog

      debug = unsafePerformIO $ do
        putStrLn $ pretty prog'

  in debug `seq` undefined
