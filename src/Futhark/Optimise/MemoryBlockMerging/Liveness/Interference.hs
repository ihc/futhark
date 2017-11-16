{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Find memory block interferences.  Maps a memory block to its interference
-- set.

module Futhark.Optimise.MemoryBlockMerging.Liveness.Interference
  ( findInterferences
  ) where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.List as L
import Data.Maybe (mapMaybe, fromMaybe, catMaybes)
import Control.Monad
import Control.Monad.RWS
import Control.Monad.Writer

import Futhark.Representation.AST
import Futhark.Representation.ExplicitMemory (
  ExplicitMemorish, ExplicitMemory, InKernel)
import qualified Futhark.Representation.ExplicitMemory as ExpMem
import Futhark.Representation.Kernels.Kernel

import Futhark.Optimise.MemoryBlockMerging.Miscellaneous
import Futhark.Optimise.MemoryBlockMerging.Types


data Context = Context { ctxVarToMem :: VarMemMappings MemorySrc
                       , ctxMemAliases :: MemAliases
                       , ctxFirstUses :: FirstUses
                       , ctxLastUses :: LastUses
                       , ctxExistentials :: Names
                       , ctxLoopCorrespondingVar :: M.Map VName (VName, SubExp)
                       }
  deriving (Show)

type InterferencesList = [(MName, MNames)]

getInterferencesMap :: InterferencesList -> Interferences
getInterferencesMap = M.unionsWith S.union . map (uncurry M.singleton)

data Current = Current { curAlive :: MNames

                       , curResPotentialKernelInterferences
                         :: PotentialKernelDataRaceInterferences
                       }
  deriving (Show)

newtype FindM lore a = FindM
  { unFindM :: RWS Context InterferencesList Current a }
  deriving (Monad, Functor, Applicative,
            MonadReader Context,
            MonadWriter InterferencesList,
            MonadState Current)

type LoreConstraints lore = (ExplicitMemorish lore,
                             KernelInterferences lore,
                             SpecialBodyExceptions lore,
                             FullWalk lore)

coerce :: (ExplicitMemorish flore, ExplicitMemorish tlore) =>
          FindM flore a -> FindM tlore a
coerce = FindM . unFindM

awaken :: MName -> FindM lore ()
awaken mem = modifyCurAlive $ S.insert mem

kill :: MName -> FindM lore ()
kill mem = modifyCurAlive $ S.delete mem

modifyCurAlive :: (MNames -> MNames) -> FindM lore ()
modifyCurAlive f = modify $ \c -> c { curAlive = f $ curAlive c }

addPotentialKernelInterferenceGroup ::
  PotentialKernelDataRaceInterferenceGroup -> FindM lore ()
addPotentialKernelInterferenceGroup set =
  modify $ \c -> c { curResPotentialKernelInterferences =
                       curResPotentialKernelInterferences c ++ [set] }

recordCurrentInterferences :: FindM lore ()
recordCurrentInterferences = do
  current <- gets curAlive
  -- Interferences are commutative.  Reflect that in the resulting data.
  forM_ (S.toList current) $ \mem ->
    tell [(mem, current)]

recordNewInterferences :: MNames -> FindM lore ()
recordNewInterferences mems_in_stm = do
  current <- gets curAlive
  -- Interferences are commutative.  Reflect that in the resulting data.
  forM_ (S.toList current) $ \mem ->
    tell [(mem, mems_in_stm)]
  forM_ (S.toList mems_in_stm) $ \mem ->
    tell [(mem, current)]

-- | Find all memory block interferences in a function definition.
findInterferences :: VarMemMappings MemorySrc -> MemAliases ->
                     FirstUses -> LastUses -> Names -> FunDef ExplicitMemory
                  -> (Interferences, PotentialKernelDataRaceInterferences)
findInterferences var_to_mem mem_aliases first_uses last_uses existentials fundef =
  let context = Context { ctxVarToMem = var_to_mem
                        , ctxMemAliases = mem_aliases
                        , ctxFirstUses = first_uses
                        , ctxLastUses = last_uses
                        , ctxExistentials = existentials
                        , ctxLoopCorrespondingVar = M.empty
                        }
      m = unFindM $ do
        forM_ (funDefParams fundef) lookInFunDefFParam
        lookInBody $ funDefBody fundef
      (cur, interferences_list) = execRWS m context (Current S.empty [])
      interferences = removeEmptyMaps $ removeKeyFromMapElems $ makeCommutativeMap
                      $ getInterferencesMap interferences_list
      potential_kernel_interferences = curResPotentialKernelInterferences cur
  in (interferences, potential_kernel_interferences)

lookInFunDefFParam :: LoreConstraints lore =>
                      FParam lore -> FindM lore ()
lookInFunDefFParam (Param var _) = do
  first_uses_var <- lookupEmptyable var <$> asks ctxFirstUses
  mapM_ awaken $ S.toList first_uses_var
  recordCurrentInterferences

lookInBody :: LoreConstraints lore =>
              Body lore -> FindM lore ()
lookInBody (Body _ bnds res) = do
  mapM_ lookInStm bnds
  lookInRes res

lookInKernelBody :: LoreConstraints lore =>
                    KernelBody lore -> FindM lore ()
lookInKernelBody (KernelBody _ bnds res) = do
  mapM_ lookInStm bnds
  lookInRes $ map kernelResultSubExp res

awakenFirstUses :: [PatElem lore] -> FindM lore ()
awakenFirstUses patvalelems =
  forM_ patvalelems $ \(PatElem var _ _) -> do
    first_uses_var <- lookupEmptyable var <$> asks ctxFirstUses
    mapM_ awaken $ S.toList first_uses_var

isNoOp :: Exp lore -> Bool
isNoOp (BasicOp bop) = case bop of
  Scratch{} -> True
  _ -> False
isNoOp _ = False

lookInStm :: LoreConstraints lore =>
             Stm lore -> FindM lore ()
lookInStm stm@(Let (Pattern _patctxelems patvalelems) _ e)
  | isNoOp e =
      awakenFirstUses patvalelems
    -- There is no reason to record interferences if the current statement will
    -- not generate any code in the end.  We have this check to use the result
    -- index sharing analysis on loop bodies and not get bogged down by the
    -- result of a Scratch statement hanging around.
  | otherwise = do
      awakenFirstUses patvalelems
      ctx <- ask
      let ctx' = ctx { ctxLoopCorrespondingVar =
                       M.union (ctxLoopCorrespondingVar ctx)
                       (findLoopCorrespondingVar ctx stm)
                     }
      let stm_exceptions = fromMaybe [] $ do
            indices <- specialBodyIndices e
            let walker_exc =
                  identityWalker
                  { walkOnBody = \body -> let (body', lcv) = innermostLoopNestBody ctx body
                                              ctx'' = ctx' { ctxLoopCorrespondingVar =
                                                             M.union (ctxLoopCorrespondingVar ctx') lcv }
                                          in tell $ interferenceExceptions ctx''
                                             (bodyStms body') (bodyResult body')
                                             indices Nothing }
                walker_kernel_exc =
                  identityKernelWalker
                  { walkOnKernelBody = \body -> let (body', lcv) = innermostLoopNestBody ctx body
                                                    ctx'' = ctx' { ctxLoopCorrespondingVar =
                                                                   M.union (ctxLoopCorrespondingVar ctx') lcv }
                                                in tell $ interferenceExceptions ctx''
                                                   (bodyStms body') (bodyResult body')
                                                   indices Nothing
                  , walkOnKernelKernelBody = \kbody -> tell $ interferenceExceptions ctx'
                                                       (kernelBodyStms kbody)
                                                       (mapMaybe (\kresult -> case kresult of
                                                                     ThreadsReturn _ se -> Just se
                                                                     _ -> Nothing)
                                                        $ kernelBodyResult kbody)
                                                       indices
                                                       (specialBodyWriteMems stm)
                  }
            return $ execWriter $ fullWalkExpM walker_exc walker_kernel_exc e

      first_uses <- asks ctxFirstUses
      last_uses <- asks ctxLastUses
      let stm_mems =
            S.unions $ map (\pelem ->
                              let v = patElemName pelem
                              in S.union
                                 (lookupEmptyable v first_uses)
                                 (lookupEmptyable (FromStm v) last_uses)) patvalelems

      ((), stm_interferences) <- censor (const []) $ listen $ do
        recordNewInterferences stm_mems
        local (const ctx') $ fullWalkExpM walker walker_kernel e
      let stm_interferences' =
            map (\(k, vs) ->
                    (k, S.fromList
                        $ filter (\v -> not ((k, v) `L.elem` stm_exceptions
                                             || (v, k) `L.elem` stm_exceptions))
                        $ S.toList vs))
            stm_interferences
      tell stm_interferences'

      potential_kernel_interferences <- findKernelDataRaceInterferences e
      onJust potential_kernel_interferences addPotentialKernelInterferenceGroup

      current <- gets curAlive
      forM_ patvalelems $ \(PatElem var _ _) -> do
        last_uses_var <- lookupEmptyable (FromStm var) <$> asks ctxLastUses
        mapM_ kill last_uses_var

      let debug = do
            putStrLn $ replicate 70 '~'
            putStrLn "Interference lookInStm:"
            print stm
            putStrLn ("current live: " ++ prettySet current)
            putStrLn ("stm mems: " ++ prettySet stm_mems)
            unless (L.null stm_exceptions)
              $ putStrLn ("exceptions: " ++ show stm_exceptions)
            putStrLn "interferences': "
            forM_ (M.assocs $ getInterferencesMap stm_interferences') $ \(v, ns) ->
              putStrLn ("  " ++ pretty v ++ ": " ++ prettySet ns)
            onJust potential_kernel_interferences $ \is ->
              unless (L.null is) $ putStrLn ("potential kernel interferences: " ++
                                             show potential_kernel_interferences)
            putStrLn $ replicate 70 '~'
      doDebug debug

        where walker = identityWalker
                { walkOnBody = lookInBody }
              walker_kernel = identityKernelWalker
                { walkOnKernelBody = coerce . lookInBody
                , walkOnKernelKernelBody = coerce . lookInKernelBody
                , walkOnKernelLambda = coerce . lookInBody . lambdaBody
                }

-- For perfectly nested loops.  Make it possible to find the index function for
-- the outer loop.
findLoopCorrespondingVar :: LoreConstraints lore =>
                            Context -> Stm lore -> M.Map VName (VName, SubExp)
findLoopCorrespondingVar ctx (Let (Pattern _patctxelems patvalelems) _
                         (DoLoop _ _ _ (Body _ stms res))) =
  M.fromList $ catMaybes $ zipWith findIt patvalelems res
  where findIt (PatElem pat_v _ (ExpMem.MemArray _ _ _ (ExpMem.ArrayIn pat_mem _))) (Var res_v)
          | not (L.null stms) = case L.last stms of
              -- This is how the program looks after coalescing.
              Let (Pattern _ [PatElem _last_v
                              (BindInPlace _ (DimFix slice_part : _))
                              (ExpMem.MemArray _ _ _ (ExpMem.ArrayIn last_stm_mem _))]) _
                                (BasicOp bop) ->
                if pat_mem == last_stm_mem
                then let res_v'
                           | Copy copy_v <- bop =
                               if (memSrcName <$> M.lookup copy_v (ctxVarToMem ctx))
                                  == Just last_stm_mem
                               then Just copy_v
                               else Nothing
                           | otherwise = Just res_v
                     in res_v' >>= \t -> Just (t, (pat_v, slice_part))
                -- Fix this mess.
                else Nothing
              _ -> Nothing
          | otherwise = Nothing
        findIt _ _ = Nothing
findLoopCorrespondingVar _ _ = M.empty

innermostLoopNestBody :: LoreConstraints lore =>
                         Context -> Body lore -> (Body lore, M.Map VName (VName, SubExp))
innermostLoopNestBody ctx body = case body of
  -- This checks for how perfect nested loops looks like after coalescing.  This
  -- is very brittle.  If it detects such a nesting, it will ask the
  -- interference exception algorithm to look in the innermost body.
  Body _ (Let _ _ (BasicOp Scratch{}) :
          loopstm@(Let _ _ (DoLoop _ _ _ body')) :
          _) _ -> let (body'', loop_corresponding_var) = innermostLoopNestBody ctx body'
                  in (body'', M.union
                              (findLoopCorrespondingVar ctx loopstm)
                              loop_corresponding_var)
  _ -> (body, M.empty)

lookInRes :: LoreConstraints lore =>
             [SubExp] -> FindM lore ()
lookInRes ses = do
  let vs = mapMaybe fromVar ses
  last_uses <- asks ctxLastUses
  let last_uses_v =
        S.unions $ map (\v -> lookupEmptyable (FromRes v) last_uses) vs
  recordNewInterferences last_uses_v
  mapM_ kill $ S.toList last_uses_v

firstUsesInStm :: LoreConstraints lore => FirstUses ->
                  Stm lore -> [KernelFirstUse]
firstUsesInStm first_uses stm =
  let m = lookFUInStm stm
  in snd $ evalRWS m first_uses ()

firstUsesInExp :: LoreConstraints lore =>
                  Exp lore -> FindM lore [KernelFirstUse]
firstUsesInExp e = do
  let m = lookFUInExp e
  first_uses <- asks ctxFirstUses
  return $ snd $ evalRWS m first_uses ()

lookFUInStm :: LoreConstraints lore =>
               Stm lore -> RWS FirstUses [KernelFirstUse] () ()
lookFUInStm (Let (Pattern _patctxelems patvalelems) _ e_stm) = do
  forM_ patvalelems $ \(PatElem patname _ membound) ->
    case membound of
      ExpMem.MemArray pt _ _ (ExpMem.ArrayIn _ ixfun) -> do
        fus <- lookupEmptyable patname <$> ask
        forM_ fus $ \fu -> tell [(fu, patname, pt, ixfun)]
      _ -> return ()
  lookFUInExp e_stm

lookFUInExp :: LoreConstraints lore =>
               Exp lore -> RWS FirstUses [KernelFirstUse] () ()
lookFUInExp = fullWalkExpM fu_walker fu_walker_kernel
  where fu_walker = identityWalker
          { walkOnBody = mapM_ lookFUInStm . bodyStms }
        fu_walker_kernel = identityKernelWalker
          { walkOnKernelBody = mapM_ lookFUInStm . bodyStms
          , walkOnKernelKernelBody = mapM_ lookFUInStm . kernelBodyStms
          , walkOnKernelLambda = mapM_ lookFUInStm . bodyStms . lambdaBody
          }

class KernelInterferences lore where
  findKernelDataRaceInterferences ::
    Exp lore -> FindM lore (Maybe PotentialKernelDataRaceInterferenceGroup)

instance KernelInterferences ExplicitMemory where
  findKernelDataRaceInterferences e = case e of
    Op (ExpMem.Inner Kernel{}) -> Just <$> firstUsesInExp e
    _ -> return Nothing

instance KernelInterferences InKernel where
  findKernelDataRaceInterferences _ = return Nothing

-- Base info for kernel bodies.
class SpecialBodyExceptions lore where
  specialBodyIndices :: Exp lore -> Maybe [MName]
  specialBodyWriteMems :: Stm lore -> Maybe [(MName, ExpMem.IxFun, PrimType)]

instance SpecialBodyExceptions ExplicitMemory where
  specialBodyIndices (Op (ExpMem.Inner (Kernel _ kernelspace _ _))) =
    Just $ map fst $ spaceDimensions kernelspace
  specialBodyIndices e = specialBodyIndicesBase e

  specialBodyWriteMems (Let (Pattern _patctxelems patvalelems) _
                        (Op (ExpMem.Inner Kernel{}))) =
    Just $ mapMaybe (\p -> case patElemAttr p of
                        ExpMem.MemArray t _ _ (ExpMem.ArrayIn mem ixfun) -> Just (mem, ixfun, t)
                        _ -> Nothing) patvalelems
  specialBodyWriteMems _ = Nothing

instance SpecialBodyExceptions InKernel where
  specialBodyIndices = specialBodyIndicesBase
  specialBodyWriteMems = const Nothing

specialBodyIndicesBase :: Exp lore -> Maybe [MName]
specialBodyIndicesBase (DoLoop _ _ (ForLoop i _ _ _) _) = Just [i]
specialBodyIndicesBase _ = Nothing

-- Use first use analysis and last use analysis to find any exceptions to the
-- naive interference recorded for a statement.
interferenceExceptions :: LoreConstraints lore =>
                          Context -> [Stm lore] -> [SubExp] -> [MName] ->
                          Maybe [(MName, ExpMem.IxFun, PrimType)] -> [(MName, MName)]
interferenceExceptions ctx stms res indices output_mems_may =
  let output_vars = mapMaybe fromVar res
      indices_slice = map (DimFix . Var) indices
      stms_first_uses = map (\(mem, _, _, _) -> mem)
                        $ concatMap (firstUsesInStm (ctxFirstUses ctx)) stms
      results =
        concat $ flip map stms $ \(Let (Pattern _patctxelems patvalelems) _ e) ->
        flip map patvalelems $ \(PatElem v bindage membound) ->
        let fromread = case (bindage, e) of
              (BindVar, BasicOp (Index orig slice)) -> do
                orig_mem <- M.lookup orig $ ctxVarToMem ctx
                if
                  -- These two extra requirements might be superfluous.
                  memSrcName orig_mem `L.notElem` stms_first_uses &&
                  not (memSrcName orig_mem `S.member` ctxExistentials ctx)
                  then return (v, typeOf membound, orig_mem, slice)
                  else Nothing
              _ -> Nothing
            fromwrite
              | (BindInPlace _orig _slice,
                 ExpMem.MemArray pt _ _ _) <- (bindage, membound)
              = do
                  -- The coalescing pass can have created a program where some
                  -- dependencies are a bit indirect.  We find the core index function.
                  let (orig', slice') =
                        fixpointIterateMay
                        (\(v0, ss0) -> do
                            (v1, s1) <- M.lookup v0 (ctxLoopCorrespondingVar ctx)
                            return (v1, DimFix s1 : ss0))
                        (v, [])

                  orig_mem <- M.lookup orig' $ ctxVarToMem ctx
                  if
                    -- These two extra requirements might be superfluous.
                    memSrcName orig_mem `L.notElem` stms_first_uses &&
                    not (memSrcName orig_mem `S.member` ctxExistentials ctx)
                    then return (v, Prim pt, orig_mem, slice')
                    else Nothing
              | otherwise = Nothing
        in (fromread, fromwrite)
      fromreads = mapMaybe fst results
      fromwrites = mapMaybe snd results
      fromwrites' = filter (\(v, _, _, _) -> v `L.elem` output_vars) fromwrites

      fus_input_vars = M.fromList $ map (\(v, _, mem, _) ->
                                           (v, S.singleton $ memSrcName mem)) fromreads
      lus_input_vars = mapFromListSetUnion $ mapMaybe
        (\(v, typ, mem, _) ->
           let check e_pat =
                 let frees = freeInExp e_pat

                     -- We need to handle scalars and arrays differently: A last
                     -- use of a scalar variable is the definite last use of the
                     -- memory it represents, while the last use of an array can
                     -- be distorted by reshapes and other aliasing operations,
                     -- so in that case we need to find the last use of the
                     -- memory block.
                     b = case typ of
                       Prim _ ->
                         v `S.member` frees
                       _ ->
                         memSrcName mem `L.elem`
                         mapMaybe ((memSrcName <$>) . (`M.lookup` ctxVarToMem ctx))
                         (S.toList frees)

                     debug0 = do
                       putStrLn $ replicate 70 '~'
                       putStrLn "interferenceExceptions check:"
                       putStrLn ("v: " ++ pretty v)
                       putStrLn ("mem: " ++ pretty (memSrcName mem))
                       putStrLn ("typ: " ++ show typ)
                       putStrLn "***"
                       putStrLn ("stm exp: " ++ show e_pat)
                       putStrLn ("frees: " ++ prettySet frees)
                       putStrLn ("result: " ++ show b)
                       putStrLn $ replicate 70 '~'

                 in withDebug debug0 b
               check' (Let _ _ e) = check e
           in (\stm -> (FromStm $ patElemName $ head $ patternValueElements $ stmPattern stm,
                        S.singleton $ memSrcName mem)) <$> L.find check' (reverse stms)) fromreads

      -- 'Just' if in kernel, 'Nothing' otherwise.
      fus_output_vars = mapFromListSetUnion $ case output_mems_may of
        Just _ -> []
        _ -> map (\(v, _, mem, _) -> (v, S.singleton $ memSrcName mem)) fromwrites'
      fus_result = mapFromListSetUnion $ case output_mems_may of
        Just mems -> zip output_vars $ map (S.singleton . (\(mem, _, _) -> mem)) mems
        _ -> []

      -- Extended first uses and last uses.
      fus = M.unionsWith S.union [ctxFirstUses ctx, fus_input_vars, fus_output_vars]
      lus = M.unionsWith S.union [ctxLastUses ctx, lus_input_vars]

      -- Memory-to-slice mappings.
      input_mem_slices = M.fromList $ map (\(_, _, mem, slice) ->
                                             (memSrcName mem, slice)) fromreads
      output_mem_slices = M.fromList $ case output_mems_may of
        Just mems ->
          map (\(mem, _, _) -> (mem, indices_slice)) mems
        _ ->
          map (\(_, _, mem, slice) -> (memSrcName mem, slice)) fromwrites'
      mem_slices = M.union input_mem_slices output_mem_slices

      -- Memory-to-ixfun mappings.
      input_mem_ixfuns = M.fromList $ map (\(_, _, mem, _) ->
                                             (memSrcName mem, memSrcIxFun mem)) fromreads
      output_mem_ixfuns = M.fromList $ case output_mems_may of
        Just mems -> map (\(mem, ixfun, _) -> (mem, ixfun)) mems
        _ -> map (\(_, _, mem, _) -> (memSrcName mem, memSrcIxFun mem)) fromwrites'
      mem_ixfuns = M.union input_mem_ixfuns output_mem_ixfuns

      -- Memory-to-primtype-size mappings.
      input_mem_primtypes = M.fromList
        $ map (\(_, t, mem, _) -> (memSrcName mem, elemType t)) fromreads
      output_mem_primtypes = M.fromList $ case output_mems_may of
        Just mems -> map (\(mem, _, pt) -> (mem, pt)) mems
        _ -> map (\(_, t, mem, _) -> (memSrcName mem, elemType t)) fromwrites'
      mem_primtypes = M.union input_mem_primtypes output_mem_primtypes

      -- Separation of input memory blocks and output memory blocks.
      mem_ins0 = S.fromList $ map (\(_, _, mem, _) -> memSrcName mem) fromreads
      mem_outs0 = S.fromList $ case output_mems_may of
        Just mems -> map (\(mem, _, _) -> mem) mems
        _ -> map (\(_, _, mem, _) -> memSrcName mem) fromwrites'
      -- An input memory must not be an output memory, and vice versa.
      mem_ins = S.difference mem_ins0 mem_outs0
      mem_outs = S.difference mem_outs0 mem_ins0

      exceptions = snd $ evalRWS (findExceptions fus fus_result lus
                                  mem_ins mem_outs mem_slices mem_ixfuns
                                  mem_primtypes output_vars) () S.empty

      debug = lus_input_vars `seq` do
        putStrLn $ replicate 70 '~'
        putStrLn "interferenceExceptions:"
        unless (L.null stms)
          $ putStrLn ("first stm: " ++ show (head stms))
        putStrLn ("indices: " ++ show indices)
        putStrLn ("output vars: " ++ show output_vars)
        putStrLn ("mem ins': " ++ prettySet mem_ins)
        putStrLn ("mem outs': " ++ prettySet mem_outs)
        putStrLn ("fromreads: " ++ show fromreads)
        putStrLn ("first uses input vars: " ++ show fus_input_vars)
        putStrLn ("first uses output vars: " ++ show fus_output_vars)
        putStrLn ("last uses input vars: " ++ show lus_input_vars)
        putStrLn ("first uses total: " ++ show fus)
        putStrLn ("last uses total: " ++ show lus)
        putStrLn ("mem slices: " ++ show mem_slices)
        putStrLn ("mem ixfuns: " ++ show mem_ixfuns)
        putStrLn ("mem primtypes: " ++ show mem_primtypes)
        putStrLn ("ctxLoopCorrespondingVar: " ++ show (ctxLoopCorrespondingVar ctx))
        unless (L.null exceptions)
          $ putStrLn ("interference exception result: " ++ show exceptions)
        putStrLn $ replicate 70 '~'
  in withDebug debug exceptions

  where findExceptions :: FirstUses -> FirstUses -> LastUses -> Names -> Names ->
                          M.Map VName (Slice SubExp) -> M.Map VName ExpMem.IxFun ->
                          M.Map VName PrimType -> [VName] ->
                          RWS () [(VName, VName)] LocalDeaths ()
        findExceptions fus fus_result lus mem_ins mem_outs mem_slices mem_ixfuns mem_primtypes output_vars = do
          forM_ stms $ \(Let (Pattern _patctxelems patvalelems) _ _) -> do
            let vs = map patElemName patvalelems
                fus_stm = S.unions $ map (`lookupEmptyable` fus) vs
                lus_stm = S.unions $ map ((`lookupEmptyable` lus) . FromStm) vs
            recordNewExceptions mem_ins mem_outs mem_slices mem_ixfuns mem_primtypes fus_stm
            modify $ S.union lus_stm
          forM_ output_vars $ \ov -> do
            let fus_ov = lookupEmptyable ov fus_result
            recordNewExceptions mem_ins mem_outs mem_slices mem_ixfuns mem_primtypes fus_ov

        recordNewExceptions :: Names -> Names ->
                               M.Map VName (Slice SubExp) -> M.Map VName ExpMem.IxFun ->
                               M.Map VName PrimType -> Names ->
                               RWS () [(VName, VName)] LocalDeaths ()
        recordNewExceptions mem_ins mem_outs mem_slices mem_ixfuns mem_primtypes fus_cur = do
          deaths <- get
          forM_ (S.toList fus_cur) $ \mem_fu -> forM_ deaths $ \mem_killed ->
            fromMaybe (return ()) $ do
            slice_fu <- M.lookup mem_fu mem_slices
            slice_killed <- M.lookup mem_killed mem_slices
            ixfun_fu <- M.lookup mem_fu mem_ixfuns
            ixfun_killed <- M.lookup mem_killed mem_ixfuns
            pt_fu <- M.lookup mem_fu mem_primtypes
            pt_killed <- M.lookup mem_killed mem_primtypes

            let debug = do
                  putStrLn $ replicate 70 '~'
                  putStrLn "recordNewExceptions:"
                  putStrLn ("slice first use: " ++ pretty slice_fu)
                  putStrLn ("slice killed: " ++ pretty slice_killed)
                  putStrLn ("ixfun first use: " ++ pretty ixfun_fu)
                  putStrLn ("ixfun killed: " ++ pretty ixfun_killed)
                  putStrLn $ replicate 70 '~'
            withDebug debug $ return $ when
              ( -- Is the killed memory read from and the first use memory
                -- written to?
                mem_fu `S.member` mem_outs && mem_killed `S.member` mem_ins &&
                -- Same index functions?
                ixfun_fu == ixfun_killed && -- too conservative?
                -- Same slices?
                slice_fu == slice_killed &&
                -- Same primitive type byte sizes?
                (primByteSize pt_fu :: Int) == primByteSize pt_killed
              ) $ tell [(mem_fu, mem_killed)]

-- Memory blocks that have had their last use locally in the body.
type LocalDeaths = Names
