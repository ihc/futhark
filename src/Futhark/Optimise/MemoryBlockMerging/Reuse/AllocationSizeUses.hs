{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Find out where allocation sizes are used.  For each statement, which sizes
-- are in scope?
module Futhark.Optimise.MemoryBlockMerging.Reuse.AllocationSizeUses
  ( findSizeUsesFunDef
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Monad
import Control.Monad.RWS
import Control.Monad.Writer

import Futhark.Representation.AST
import Futhark.Representation.ExplicitMemory (
  ExplicitMemory, ExplicitMemorish)
import Futhark.Representation.Kernels.Kernel

import Futhark.Optimise.MemoryBlockMerging.Miscellaneous
import Futhark.Optimise.MemoryBlockMerging.Reuse.AllocationSizes
import Futhark.Optimise.MemoryBlockMerging.PrimExps


type SizeVars = Names
type DeclarationsSoFar = Names

-- The final return value.  Describes which size variables are in scope at the
-- creation of the key size variable.
type UsesBefore = M.Map VName Names

newtype FindM lore a = FindM { unFindM :: RWS SizeVars
                               UsesBefore DeclarationsSoFar a }
  deriving (Monad, Functor, Applicative,
            MonadReader SizeVars,
            MonadWriter UsesBefore,
            MonadState DeclarationsSoFar)

type LoreConstraints lore = (ExplicitMemorish lore,
                             FullWalk lore)

coerce :: (ExplicitMemorish flore, ExplicitMemorish tlore) =>
          FindM flore a -> FindM tlore a
coerce = FindM . unFindM

addDeclarations :: Names -> FindM lore ()
addDeclarations = modify . S.union

addUsesBefore :: VName -> Names -> FindM lore ()
addUsesBefore var declarations_so_far =
  tell $ M.singleton var declarations_so_far

findSizeUsesFunDef :: FunDef ExplicitMemory -> UsesBefore
findSizeUsesFunDef fundef =
  let size_vars = mapMaybe (fromVar . fst) $ M.elems $ memBlockSizesFunDef fundef
      var_to_pe = findPrimExpsFunDef fundef
      -- We want to find 'uses before' for all size vars *and* which variables
      -- they depend on.  This is a compromise between recording the
      -- relationship for only size variables and all variables.  We need this
      -- compromise for 'sizesCanBeMaxedKernelArray' in Reuse.Core.
      find_pe_vars v0 = fromMaybe S.empty $ do
        pe <- M.lookup v0 var_to_pe
        return $ S.insert v0 $ execWriter $ traverse
          (\v -> do
              tell $ S.singleton v
              tell $ find_pe_vars v
              return v) pe
      size_vars' = S.unions $ map find_pe_vars size_vars
      m = unFindM $ do
        forM_ (funDefParams fundef) lookInFParam
        lookInBody $ funDefBody fundef
      res = snd $ evalRWS m size_vars' S.empty
  in res

lookInFParam :: LoreConstraints lore =>
                FParam lore -> FindM lore ()
lookInFParam (Param x _) =
  lookAtNewDecls $ S.singleton x

lookInLParam :: LoreConstraints lore =>
                LParam lore -> FindM lore ()
lookInLParam (Param x _) =
  lookAtNewDecls $ S.singleton x

lookInBody :: LoreConstraints lore =>
              Body lore -> FindM lore ()
lookInBody (Body _ bnds _res) =
  mapM_ lookInStm bnds

lookInKernelBody :: LoreConstraints lore =>
                    KernelBody lore -> FindM lore ()
lookInKernelBody (KernelBody _ bnds _res) =
  mapM_ lookInStm bnds

lookInStm :: LoreConstraints lore =>
             Stm lore -> FindM lore ()
lookInStm stm@(Let _ _ e) = do
  let new_decls = S.fromList $ newDeclarationsStm stm
  lookAtNewDecls new_decls

  -- Recursive body walk.
  fullWalkExpM walker walker_kernel e
  where walker = identityWalker
          { walkOnBody = lookInBody
          , walkOnFParam = lookInFParam
          , walkOnLParam = lookInLParam
          }
        walker_kernel = identityKernelWalker
          { walkOnKernelBody = coerce . lookInBody
          , walkOnKernelKernelBody = coerce . lookInKernelBody
          , walkOnKernelLambda = coerce . lookInLambda
          , walkOnKernelLParam = lookInLParam
          }

lookInLambda :: LoreConstraints lore =>
                Lambda lore -> FindM lore ()
lookInLambda (Lambda params body _) = do
  forM_ params lookInLParam
  lookInBody body

lookAtNewDecls :: LoreConstraints lore =>
                  Names -> FindM lore ()
lookAtNewDecls new_decls = do
  all_size_vars <- ask
  declarations_so_far <- get
  let new_size_vars = S.intersection all_size_vars new_decls
  forM_ new_size_vars $ \var ->
    addUsesBefore var declarations_so_far
  addDeclarations new_size_vars
