{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Playground for work on merging memory blocks
module Futhark.Pass.MemoryBlockMerging.Miscellaneous where

import Prelude
import Data.Maybe
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS

import Debug.Trace

import Futhark.Representation.Aliases
import qualified Futhark.Representation.ExplicitMemory as ExpMem
import qualified Futhark.Analysis.Alias as AnlAls

import Futhark.Pass.MemoryBlockMerging.DataStructs


-----------------------------------
-----------------------------------
--- Inter-Kernel Memory Merging ---
-----------------------------------
-----------------------------------

type IntrfTab = HM.HashMap VName Names

data IntrfEnv = IntrfEnv { intrf :: IntrfTab
                         -- ^ the interference table: a memory block
                         --   may interfere with several other. Note
                         --   that the relation is commutative, but
                         --   we might not record both ways.
                         , alloc :: AllocTab
                         -- ^ contains the already allocated memory blocks
                         --   as keys and their corresponding sizes as values.
                         , alias :: AliasTab
                         -- ^ alias table between variables and between
                         --   memory block names (need to compute this
                         --   via a pass)
                         , v2mem :: V2MemTab
                         -- ^ records variable names to memory block mapping;
                         --   a var might map to several mem blocks due to aliasing.
                         , active:: Names
                         -- ^ the set of active memory blocks; subset of alloca;
                         --   a memory block is removed from active upon a last use
                         --   and added to active at array creation.
--                         , fresh :: Names
                         -- ^ array variables that are newly created, i.e., they "own"
                         --   their memory block during their life span.
                         }

emptyInterfEnv :: IntrfEnv
emptyInterfEnv = IntrfEnv { intrf = HM.empty, alloc = HS.empty
                          , alias = HM.empty, v2mem = HM.empty, active = HS.empty }

intrfAnPrg :: LUTabPrg -> ExpMem.Prog ExpMem.ExplicitMemory -> HM.HashMap Name IntrfEnv
intrfAnPrg lutab prg =
  let aliased_prg = AnlAls.aliasAnalysis prg
  in  HM.fromList $ map (intrfAnFun lutab) $ progFunctions aliased_prg


intrfAnFun :: LUTabPrg -> FunDef (Aliases ExpMem.ExplicitMemory) -> (Name,IntrfEnv)
intrfAnFun lutabprg (FunDef _ fname _ _ body) =
  let lutab = fromMaybe HM.empty (HM.lookup fname lutabprg)
      env = intrfAnBdy lutab emptyInterfEnv body
  in  (fname, env)

intrfAnBdy :: LUTabFun -> IntrfEnv -> Body (Aliases ExpMem.ExplicitMemory)
           -> IntrfEnv
intrfAnBdy lutab env (Body _ bnds _)  =
  foldl (intrfAnBnd lutab) env bnds

intrfAnBnd :: LUTabFun -> IntrfEnv -> Stm (Aliases ExpMem.ExplicitMemory)
           -> IntrfEnv
intrfAnBnd _ env (Let pat _ (Op (ExpMem.Alloc sz _)) ) =
  case patternNames pat of
    []   -> env
    nm:_ -> let nm' = trace ("AllocNode: "++pretty nm++" size: "++pretty sz) nm
            in  env { alloc = HS.insert nm' (alloc env)}

intrfAnBnd lutab env (Let pat _ (DoLoop memctx var_ses _ body)) =
  -- BUG!!! you need to handle the potential circular aliasing
  -- between loop-variant variables and their memory blocks;
  -- just borrow them from the pattern (via substitution)!
  let alias0 = updateAliasing (alias env) pat
      alias' = foldl (\acc ((fpar,_),patel) ->
                        let patnm = patElemName patel
                            parnm = paramName fpar
                        in  case trace ("LOOPMEMCTX: "++pretty patnm++" "++pretty parnm) $ HM.lookup patnm alias0 of
                                    Nothing -> acc
                                    Just al -> trace (" found alias set: "++pretty (HS.toList al)) HM.insert parnm al acc
                     ) (alias env) $ zip memctx $ patternContextElements pat
      -- ^ update the aliasing of the loop's memory-block context
      --   with the aliasing info borrowed from the pattern.

      (lvars, _) = unzip var_ses
      lvarmems =
        mapMaybe (\fpar -> case paramAttr fpar of
                             ExpMem.ArrayMem ptp shp _ mem_nm idxfun ->
                                 Just (paramName fpar, MemBlock ptp shp mem_nm idxfun)
                             _ -> Nothing
                 ) lvars
      v2mem' = HM.union (v2mem env) $ HM.fromList lvarmems
      -- ^ update the v2mem with the memory blocks of the loop vars.

      mems = HS.fromList $ map (\(MemBlock _ _ mn _) -> mn) $ snd $ unzip lvarmems
      active' = HS.union (active env) $ HS.intersection (alloc env) $
                aliasTransClos alias' mems
      -- ^ add the alias-transitive closure of loop-vars mem blocks to active
      env' = intrfAnBdy lutab (env{v2mem = v2mem', active = active', alias = alias'}) body
  in  defInterference lutab env' pat

intrfAnBnd lutab env (Let pat _ _) =
  defInterference lutab env pat

defInterference :: LUTabFun -> IntrfEnv -> Pattern (Aliases ExpMem.ExplicitMemory)
                -> IntrfEnv
defInterference lutab env pat =
  let alias' = updateAliasing (alias env) pat
      -- ^ record the aliasing of the current statement

      arrmems= map (\(a,b,_)->(a,b)) $ getArrMemAssoc pat
      v2mem' = HM.union (v2mem env) $ HM.fromList arrmems
      -- ^ update v2mem with pattern's (array-var -> mem-block) bindings

      patmems = map (\(MemBlock _ _ mn _) -> mn) $ snd $ unzip arrmems
      intrf' = updateInterference alias' (alloc env) (active env) (intrf env) patmems
      -- ^ update interference: get the alias-transitive closure of each memory
      --   block in pattern and mark its interference with the current active set.

      lus    = fromMaybe HS.empty (HM.lookup (head $ patternNames pat) lutab)
      lumems = getLastUseMem v2mem' lus
      active1= HS.difference (active env) lumems
      -- ^ get the memory blocks associated to the variables lastly used in this
      --   statement and subtract them from the active set.

      active'= HS.union active1 $ HS.intersection (alloc env) $
               aliasTransClos alias' $ HS.fromList patmems
      -- ^ update the active set with the alias-transitive closure of this stmt
      --   memory blocks (keep only the allocated ones of course).

  in env { alias = alias', v2mem = v2mem', intrf = intrf', active = active' }


updateInterference :: AliasTab -> AllocTab -> Names -> IntrfTab -> [VName] -> IntrfTab
updateInterference alias0 alloc0 active0 =
  foldl (\itrf mm -> let m_al = case HM.lookup mm alias0 of
                                  Just al -> HS.insert mm al
                                  Nothing -> HS.singleton mm
                         m_ad = HS.intersection m_al alloc0
                     in  HS.foldl' (\acc m -> case HM.lookup m acc of
                                               Just mst-> HM.insert m (mst `HS.union` active0) acc
                                               Nothing -> HM.insert m active0 acc
                                   ) itrf m_ad
        )

getLastUseMem :: V2MemTab -> Names -> Names
getLastUseMem v2mem0 =
  HS.foldl' (\acc lu ->
                case HM.lookup lu v2mem0 of
                  Nothing -> acc
                  Just (MemBlock _ _ m _)  -> HS.insert m acc
            ) HS.empty
