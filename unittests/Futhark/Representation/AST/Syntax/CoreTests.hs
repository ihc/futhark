{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Futhark.Representation.AST.Syntax.CoreTests
       ( tests )
       where

import Control.Applicative

import Test.HUnit hiding (Test)
import Test.Framework
import Test.Framework.Providers.HUnit
import Test.QuickCheck

import Prelude

import Language.Futhark.CoreTests ()
import Futhark.Representation.PrimitiveTests()
import Futhark.Representation.AST.Syntax.Core
import Futhark.Representation.AST.Pretty ()

tests :: [Test]
tests = subShapeTests

subShapeTests :: [Test]
subShapeTests =
  [ shape [free 1, free 2] `isSubShapeOf` shape [free 1, free 2]
  , shape [free 1, free 3] `isNotSubShapeOf` shape [free 1, free 2]
  , shape [free 1] `isNotSubShapeOf` shape [free 1, free 2]
  , shape [free 1, free 2] `isSubShapeOf` shape [free 1, Ext 3]
  , shape [Ext 1, Ext 2] `isNotSubShapeOf` shape [Ext 1, Ext 1]
  , shape [Ext 1, Ext 1] `isSubShapeOf` shape [Ext 1, Ext 2]
  ]
  where shape :: [ExtSize] -> ExtShape
        shape = Shape

        free :: Int -> ExtSize
        free = Free . Constant . IntValue . Int32Value . fromIntegral

        isSubShapeOf shape1 shape2 =
          subShapeTest shape1 shape2 True
        isNotSubShapeOf shape1 shape2 =
          subShapeTest shape1 shape2 False

        subShapeTest :: ExtShape -> ExtShape -> Bool -> Test
        subShapeTest shape1 shape2 expected =
          testCase ("subshapeOf " ++ pretty shape1 ++ " " ++
                    pretty shape2 ++ " == " ++
                    show expected) $
          shape1 `subShapeOf` shape2 @?= expected

instance Arbitrary NoUniqueness where
  arbitrary = pure NoUniqueness

instance (Arbitrary shape, Arbitrary u) => Arbitrary (TypeBase shape u) where
  arbitrary =
    oneof [ Prim <$> arbitrary
          , Array <$> arbitrary <*> arbitrary <*> arbitrary
          ]

instance Arbitrary Value where
  arbitrary = PrimVal <$> arbitrary

instance Arbitrary Ident where
  arbitrary = Ident <$> arbitrary <*> arbitrary

instance Arbitrary Rank where
  arbitrary = Rank <$> elements [1..9]

instance Arbitrary Shape where
  arbitrary = Shape . map intconst <$> listOf1 (elements [1..9])
    where intconst = Constant . IntValue . Int32Value
