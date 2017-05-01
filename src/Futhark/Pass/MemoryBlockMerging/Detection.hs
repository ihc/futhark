{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Array coalescing.
module Futhark.Pass.MemoryBlockMerging.Detection
  ( findCoalescings
  ) where

import System.IO.Unsafe (unsafePerformIO) -- Just for debugging!

import qualified Data.Map.Strict as M
import qualified Data.List as L
import Control.Monad
import Data.Monoid

import Futhark.Representation.AST.Attributes.Scope
import Futhark.Analysis.Alias (aliasAnalysis)
import Futhark.Analysis.PrimExp.Convert
import Futhark.Representation.Aliases
import qualified Futhark.Representation.ExplicitMemory as ExpMem
import qualified Futhark.Representation.ExplicitMemory.IndexFunction as IxFun

-- Types.

data MemoryBlock = MemoryBlock
  { dest :: VName
    -- ^ destination memory block
  , destMemoryOffset :: ExpMem.IxFun
    -- ^ offset into the memory block
  }
  deriving (Show)

-- | A mapping from source variables to their new memory blocks.
type Coalescings = M.Map VName MemoryBlock

data OptimisticContext = OptimisticContext
  { oStmsPrev :: [Stm (Aliases ExpMem.ExplicitMemory)]
  , oStmsNext :: [Stm (Aliases ExpMem.ExplicitMemory)]
  , oStmsFinalResult :: Result -- necessary?
  , oContextParent :: Maybe OptimisticContext
  }
  deriving (Show)

scopePrev :: OptimisticContext -> Scope (Aliases ExpMem.ExplicitMemory)
scopePrev oc = scopeOf $ oStmsPrev oc

scopeNext :: OptimisticContext -> Scope (Aliases ExpMem.ExplicitMemory)
scopeNext oc = scopeOf $ oStmsNext oc -- might also need the scope of oStmsFinalResult oc

data OptimisticCoalescing = OptimisticCoalescing
  { oSource :: VName
  , oDest :: VName
  , oDestMemory :: VName -- necessary?
  , oDestMemoryOffset :: ExpMem.IxFun
  , oContext :: OptimisticContext
  }
  deriving (Show)


-- | Find all possible coalescings in the program.
findCoalescings :: Prog ExpMem.ExplicitMemory -> Coalescings
findCoalescings prog =
  let prog' = aliasAnalysis prog
      optimistics = concatMap findOptimisticsFun $ progFunctions prog'
      optimistics' = filter isCorrectMerge optimistics
      coalescings = finaliseCoalescings optimistics'

      debug = unsafePerformIO $ do
        putStrLn $ pretty prog'
        forM_ optimistics $ \o -> do
          putStrLn $ "source: " ++ show (oSource o)
          putStrLn $ "dest: " ++ show (oDest o)
          putStrLn $ "dest memory: " ++ show (oDestMemory o)
          putStrLn $ "dest memory offset: " ++ show (oDestMemoryOffset o)
          putStrLn "--------------------"

  in debug `seq` coalescings


-- Finding them.

findOptimisticsFun :: FunDef (Aliases ExpMem.ExplicitMemory)
                   -> [OptimisticCoalescing]
findOptimisticsFun (FunDef _ _ _ fParams body) =
  let stms = bodyStms body
      stms' = zip3 (L.inits stms) stms (L.tail $ L.tails stms)
      optimistics = concatMap (\stm' -> findOptimisticsStm
                                        Nothing
                                        (scopeOfFParams fParams)
                                        stm'
                                        (bodyResult body)) stms'
  in optimistics

findOptimisticsStm :: Maybe OptimisticContext
                   -> Scope (Aliases ExpMem.ExplicitMemory)
                   -> ([Stm (Aliases ExpMem.ExplicitMemory)],
                       Stm (Aliases ExpMem.ExplicitMemory),
                       [Stm (Aliases ExpMem.ExplicitMemory)])
                   -> Result
                   -> [OptimisticCoalescing]
findOptimisticsStm parent startScope (prevs, cur, nexts) finalResult =
  let context = OptimisticContext { oStmsPrev = prevs
                                  , oStmsNext = nexts
                                  , oStmsFinalResult = finalResult
                                  , oContextParent = parent
                                  }

      curScope :: Scope (Aliases ExpMem.ExplicitMemory)
      curScope = startScope <> scopeOfContext context scopePrev

      (dst, dstMemory, ixFun) =
        case patternValueElements $ bindingPattern cur of
          [PatElem dst BindVar
           (_, ExpMem.ArrayMem _ _ _ dstMemory ixFun)] ->
            (dst, dstMemory, ixFun)
          [PatElem dst (BindInPlace _ _dstIx dstSlice)
           (_, ExpMem.ArrayMem _ _ _ dstMemory ixFun)] ->
            let dstSlice' = map (fmap (primExpFromSubExp (IntType Int32))) dstSlice
                ixFun' = IxFun.slice ixFun dstSlice'
            in (dst, dstMemory, ixFun')
          _ -> error "Should we handle this?"

  in case bindingExp cur of
       -- Cases:
       --
       --   + @let dst = copy src@
       --
       --   + @let dst[i] = src@ -- the right-hand side can be just @src@ in the
       --     source language, but is @copy src@ in the internal representation.
       BasicOp (Copy src) ->
         [OptimisticCoalescing { oSource = src
                               , oDest = dst
                               , oDestMemory = dstMemory
                               , oDestMemoryOffset = ixFun
                               , oContext = context
                               }]

       -- Cases:
       --
       --   + @let dst = concat(..., src, ...)@
       --
       --   + @let dst[i] = concat(..., src, ...)@
       (BasicOp (Concat _ 0 src0 srcs _)) ->
         let offsetZero = primExpFromSubExp (IntType Int32) (constant (0 :: Int32))
         in reverse $ fst $ foldl findOptimisticsConcatSrc
            ([], offsetZero) (src0 : srcs)

         where findOptimisticsConcatSrc :: ([OptimisticCoalescing], PrimExp VName)
                                        -> VName
                                        -> ([OptimisticCoalescing], PrimExp VName)
               findOptimisticsConcatSrc (optimistics, offset) src =
                 let ixFun' = IxFun.offsetIndex ixFun offset
                     oc = OptimisticCoalescing { oSource = src
                                               , oDest = dst
                                               , oDestMemory = dstMemory
                                               , oDestMemoryOffset = ixFun'
                                               , oContext = context
                                               } : optimistics
                     offsetAfterSrc
                       | Just scopeInfo <- M.lookup src curScope,
                         Array _ shape _ <- typeOf scopeInfo,
                         (se : _) <- shapeDims shape =
                           primExpFromSubExp (IntType Int32) se
                       | otherwise = error "This should not happen."
                     offset' = BinOpExp (Add Int32) offset offsetAfterSrc
                 in (oc, offset')

       -- Recursively consider the sub-bodies.
       -- ...

       -- No other cases to handle (for now).
       _ -> []

scopeOfContext :: OptimisticContext
               -> (OptimisticContext -> Scope (Aliases ExpMem.ExplicitMemory))
               -> Scope (Aliases ExpMem.ExplicitMemory)
scopeOfContext oc getScope =
  getScope oc <> maybe mempty scopeOfContext (oContextParent oc) getScope


-- Filtering them.

isCorrectMerge :: OptimisticCoalescing -> Bool
isCorrectMerge oc = all ($ oc)
  [ isCorrectMergeCond1
  , isCorrectMergeCond2
  , isCorrectMergeCond3
  , isCorrectMergeCond4
  , isCorrectMergeCond5
  ]

isCorrectMergeCond1 :: OptimisticCoalescing -> Bool
isCorrectMergeCond1 oc = True

isCorrectMergeCond2 :: OptimisticCoalescing -> Bool
isCorrectMergeCond2 oc = True

isCorrectMergeCond3 :: OptimisticCoalescing -> Bool
isCorrectMergeCond3 oc = True

isCorrectMergeCond4 :: OptimisticCoalescing -> Bool
isCorrectMergeCond4 oc = True

isCorrectMergeCond5 :: OptimisticCoalescing -> Bool
isCorrectMergeCond5 oc = True

finaliseCoalescings :: [OptimisticCoalescing] -> Coalescings
finaliseCoalescings = undefined
