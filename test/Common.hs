module Common where

import Test.QuickCheck

import SIL.TypeChecker
import SIL

class TestableExpr a where
  getIExpr :: a -> Expr

data TestExpr = TestExpr Expr

data ValidTestExpr = ValidTestExpr TestExpr

data ZeroTypedTestExpr = ZeroTypedTestExpr TestExpr

data ArrowTypedTestExpr = ArrowTypedTestExpr TestExpr

instance TestableExpr TestExpr where
  getIExpr (TestExpr x) = x

instance Show TestExpr where
  show (TestExpr t) = show t

instance TestableExpr ValidTestExpr where
  getIExpr (ValidTestExpr x) = getIExpr x

instance Show ValidTestExpr where
  show (ValidTestExpr v) = show v

instance TestableExpr ZeroTypedTestExpr where
  getIExpr (ZeroTypedTestExpr x) = getIExpr x

instance Show ZeroTypedTestExpr where
  show (ZeroTypedTestExpr v) = show v

instance TestableExpr ArrowTypedTestExpr where
  getIExpr (ArrowTypedTestExpr x) = getIExpr x

instance Show ArrowTypedTestExpr where
  show (ArrowTypedTestExpr x) = show x

lift1Texpr :: (Expr -> Expr) -> TestExpr -> TestExpr
lift1Texpr f (TestExpr x) = TestExpr $ f x

lift2Texpr :: (Expr -> Expr -> Expr) -> TestExpr -> TestExpr -> TestExpr
lift2Texpr f (TestExpr a) (TestExpr b) = TestExpr $ f a b

instance Arbitrary TestExpr where
  arbitrary = sized tree where
    tree i = let half = div i 2
                 pure2 = pure . TestExpr
             in case i of
                  0 -> oneof $ map pure2 [zero, var]
                  x -> oneof
                    [ pure2 zero
                    , pure2 var
                    , lift2Texpr pair <$> tree half <*> tree half
                    , lift1Texpr SetEnv <$> tree (i - 1)
                    , lift1Texpr Defer <$> tree (i - 1)
                    , lift2Texpr check <$> tree half <*> tree half
                    , lift1Texpr gate <$> tree (i - 1)
                    , lift1Texpr pleft <$> tree (i - 1)
                    , lift1Texpr pright <$> tree (i - 1)
                    , lift1Texpr Trace <$> tree (i - 1)
                    ]
  shrink (TestExpr x) = case x of
    Zero -> []
    Env -> []
    (Gate x) -> TestExpr x : (map (lift1Texpr gate) . shrink $ TestExpr x)
    (PLeft x) -> TestExpr x : (map (lift1Texpr pleft) . shrink $ TestExpr x)
    (PRight x) -> TestExpr x : (map (lift1Texpr pright) . shrink $ TestExpr x)
    (Trace x) -> TestExpr x : (map (lift1Texpr Trace) . shrink $ TestExpr x)
    (SetEnv x) -> TestExpr x : (map (lift1Texpr SetEnv) . shrink $ TestExpr x)
    (Defer x) -> TestExpr x : (map (lift1Texpr Defer) . shrink $ TestExpr x)
    (Abort x) -> TestExpr x : (map (lift1Texpr Abort) . shrink $ TestExpr x)
    (Pair a b) -> TestExpr a : TestExpr  b :
      [lift2Texpr pair a' b' | (a', b') <- shrink (TestExpr a, TestExpr b)]

typeable x = case inferType (getIExpr x) of
  Left _ -> False
  _ -> True

instance Arbitrary ValidTestExpr where
  arbitrary = ValidTestExpr <$> suchThat arbitrary typeable
  shrink (ValidTestExpr te) = map ValidTestExpr . filter typeable $ shrink te

zeroTyped x = inferType (getIExpr x) == Right DataOnlyTypeP

instance Arbitrary ZeroTypedTestExpr where
  arbitrary = ZeroTypedTestExpr <$> suchThat arbitrary zeroTyped
  shrink (ZeroTypedTestExpr ztte) = map ZeroTypedTestExpr . filter zeroTyped $ shrink ztte

simpleArrowTyped x = inferType (getIExpr x) == Right (ArrTypeP DataOnlyTypeP DataOnlyTypeP)

instance Arbitrary ArrowTypedTestExpr where
  arbitrary = ArrowTypedTestExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestExpr atte) = map ArrowTypedTestExpr . filter simpleArrowTyped $ shrink atte
