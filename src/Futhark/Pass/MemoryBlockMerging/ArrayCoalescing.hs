{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Array coalescing.
module Futhark.Pass.MemoryBlockMerging.ArrayCoalescing
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


data MemoryBlock = MemoryBlock
  { destName :: VName
    -- ^ destination memory block
  , destOffset :: ExpMem.IxFun
    -- ^ offset into the memory block
  }
  deriving (Show)

-- | A mapping from source variables to their new memory blocks.
type Coalescings = M.Map VName MemoryBlock

data OptimisticCoalescing = OptimisticCoalescing
  { oSource :: VName
  , oDest :: VName
  , oDestMemory :: VName
  , oDestMemoryOffset :: ExpMem.IxFun
  , oStmsPrev :: [Stm (Aliases ExpMem.ExplicitMemory)]
  , oStmsNext :: [Stm (Aliases ExpMem.ExplicitMemory)]
  , oStmsFinalResult :: Result
  }
  deriving (Show)

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

findOptimisticsFun :: FunDef (Aliases ExpMem.ExplicitMemory)
                   -> [OptimisticCoalescing]
findOptimisticsFun (FunDef _ _ _ fParams body) =
  let stms = bodyStms body
      stms' = zip3 (L.inits stms) stms (L.tail $ L.tails stms)
      optimistics = concatMap (findOptimisticsStm (scopeOfFParams fParams) (bodyResult body)) stms'
  in optimistics

findOptimisticsStm :: Scope (Aliases ExpMem.ExplicitMemory)
                   -> Result
                   -> ([Stm (Aliases ExpMem.ExplicitMemory)],
                       Stm (Aliases ExpMem.ExplicitMemory),
                       [Stm (Aliases ExpMem.ExplicitMemory)])
                   -> [OptimisticCoalescing]
findOptimisticsStm startScope finalResult (prevs, cur, nexts) =
  case (patternValueElements $ bindingPattern cur,
        bindingExp cur) of

    -- @let dst = copy src@
    ([PatElem dst BindVar (_, ExpMem.ArrayMem _ _ _ dstMemory ixFun)],
     BasicOp (Copy src)) ->
      [OptimisticCoalescing { oSource = src
                            , oDest = dst
                            , oDestMemory = dstMemory
                            , oDestMemoryOffset = ixFun
                            , oStmsPrev = prevs
                            , oStmsNext = nexts
                            , oStmsFinalResult = finalResult
                            }]

    -- @let dst[i] = src@
    ([PatElem dst (BindInPlace _ _dstIx dstSlice) (_, ExpMem.ArrayMem _ _ _ dstMemory ixFun)],
     BasicOp (Copy src)) ->
      let ixFun' = updateIxFunSlice ixFun dstSlice
      in [OptimisticCoalescing { oSource = src
                               , oDest = dst
                               , oDestMemory = dstMemory
                               , oDestMemoryOffset = ixFun'
                               , oStmsPrev = prevs
                               , oStmsNext = nexts
                               , oStmsFinalResult = finalResult
                               }]

    -- @let dst = concat(..., src)@
    ([PatElem dst BindVar (_, ExpMem.ArrayMem _ _ _ dstMemory ixFun)],
     BasicOp (Concat _ 0 src0 srcs _)) ->
      let scope = startScope <> scopeOf prevs
          offsetZero = primExpFromSubExp (IntType Int32) (constant (0 :: Int32))
      in reverse $ fst $ foldl (findOptimisticsConcatSrc scope) ([], offsetZero) (src0 : srcs)

      where findOptimisticsConcatSrc :: Scope (Aliases ExpMem.ExplicitMemory)
                                     -> ([OptimisticCoalescing], PrimExp VName)
                                     -> VName
                                     -> ([OptimisticCoalescing], PrimExp VName)
            findOptimisticsConcatSrc scope (optimistics, offset) src =
              let ixFun' = IxFun.offsetIndex ixFun offset
                  oc = OptimisticCoalescing { oSource = src
                                            , oDest = dst
                                            , oDestMemory = dstMemory
                                            , oDestMemoryOffset = ixFun'
                                            , oStmsPrev = prevs
                                            , oStmsNext = nexts
                                            , oStmsFinalResult = finalResult
                                            } : optimistics
                  offsetAfterSrc
                    | Just scopeInfo <- M.lookup src scope,
                      Array _ shape _ <- typeOf scopeInfo,
                      (se : _) <- shapeDims shape =
                        primExpFromSubExp (IntType Int32) se
                    | otherwise = error "This should not happen."
                  offset' = BinOpExp (Add Int32) offset offsetAfterSrc
              in (oc, offset')

    _ -> []

-- recursive?


updateIxFunSlice :: ExpMem.IxFun -> Slice SubExp -> ExpMem.IxFun
updateIxFunSlice ixFun slice =
  let slice' = map (fmap (primExpFromSubExp (IntType Int32))) slice
  in IxFun.slice ixFun slice'
