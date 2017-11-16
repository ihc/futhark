{-# LANGUAGE FlexibleContexts #-}
module Futhark.Internalise.AccurateSizes
  ( shapeBody
  , annotateArrayShape
  , argShapes
  , ensureResultShape
  , ensureResultExtShape
  , ensureExtShape
  , ensureShape
  , ensureArgShapes
  )
  where

import Control.Applicative
import Control.Monad
import Data.Loc
import qualified Data.Map.Strict as M

import Prelude

import Futhark.Construct
import Futhark.Representation.AST
import Futhark.MonadFreshNames

shapeBody :: (HasScope lore m, MonadFreshNames m, BinderOps lore, Bindable lore) =>
             [VName] -> [Type] -> Body lore
          -> m (Body lore)
shapeBody shapenames ts body =
  runBodyBinder $ do
    ses <- bodyBind body
    sets <- mapM subExpType ses
    return $ resultBody $ argShapes shapenames ts sets

annotateArrayShape :: ArrayShape shape =>
                      TypeBase shape u -> [Int] -> TypeBase Shape u
annotateArrayShape t newshape =
  t `setArrayShape` Shape (take (arrayRank t) $
                           map (intConst Int32 . toInteger) $ newshape ++ repeat 0)

argShapes :: [VName] -> [TypeBase Shape u0] -> [TypeBase Shape u1] -> [SubExp]
argShapes shapes valts valargts =
  map addShape shapes
  where mapping = shapeMapping valts valargts
        addShape name
          | Just se <- M.lookup name mapping = se
          | otherwise                        = intConst Int32 0

ensureResultShape :: MonadBinder m =>
                     (m Certificates -> m Certificates)
                  -> String -> SrcLoc -> [Type] -> Body (Lore m)
                  -> m (Body (Lore m))
ensureResultShape asserting msg loc =
  ensureResultExtShape asserting msg loc . staticShapes

ensureResultExtShape :: MonadBinder m =>
                        (m Certificates -> m Certificates)
                     -> String -> SrcLoc -> [ExtType] -> Body (Lore m)
                     -> m (Body (Lore m))
ensureResultExtShape asserting msg loc rettype body =
  insertStmsM $ do
    es <- bodyBind body
    es_ts <- mapM subExpType es
    let ext_mapping = shapeExtMapping rettype es_ts
        rettype' = foldr (uncurry fixExt) rettype $ M.toList ext_mapping
        assertProperShape t se =
          let name = "result_proper_shape"
          in ensureExtShape asserting msg loc t name se
    reses <- zipWithM assertProperShape rettype' es
    ts <- mapM subExpType reses
    let ctx = extractShapeContext rettype $ map arrayDims ts
    mkBodyM [] (ctx ++ reses)

ensureExtShape :: MonadBinder m =>
                  (m Certificates -> m Certificates)
               -> String -> SrcLoc -> ExtType -> String -> SubExp
               -> m SubExp
ensureExtShape asserting msg loc t name orig
  | Array{} <- t, Var v <- orig =
    Var <$> ensureShapeVar asserting msg loc t name v
  | otherwise = return orig

ensureShape :: MonadBinder m =>
               (m Certificates -> m Certificates)
            -> String -> SrcLoc -> Type -> String -> SubExp
            -> m SubExp
ensureShape asserting msg loc = ensureExtShape asserting msg loc . staticShapes1

-- | Reshape the arguments to a function so that they fit the expected
-- shape declarations.  Not used to change rank of arguments.  Assumes
-- everything is otherwise type-correct.
ensureArgShapes :: (MonadBinder m, Typed (TypeBase Shape u)) =>
                   (m Certificates -> m Certificates)
                -> String -> SrcLoc -> [VName] -> [TypeBase Shape u] -> [SubExp]
                -> m [SubExp]
ensureArgShapes asserting msg loc shapes paramts args =
  zipWithM ensureArgShape (expectedTypes shapes paramts args) args
  where ensureArgShape _ (Constant v) = return $ Constant v
        ensureArgShape t (Var v)
          | arrayRank t < 1 = return $ Var v
          | otherwise =
              ensureShape asserting msg loc t (baseString v) $ Var v


ensureShapeVar :: MonadBinder m =>
                  (m Certificates -> m Certificates)
               -> String -> SrcLoc -> ExtType -> String -> VName
               -> m VName
ensureShapeVar asserting msg loc t name v
  | Array{} <- t = do
    newshape <- arrayDims . removeExistentials t <$> lookupType v
    oldshape <- arrayDims <$> lookupType v
    let checkDim desired has =
          letExp "shape_cert" =<<
          eAssert (pure $ BasicOp $ CmpOp (CmpEq int32) desired has) msg loc
    certs <- asserting $ Certificates <$> zipWithM checkDim newshape oldshape
    certifying certs $
      letExp name $ shapeCoerce newshape v
  | otherwise = return v
