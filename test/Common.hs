module Common where

import Test.QuickCheck

import SIL.TypeChecker
import SIL


class TestableIExpr a where
  getIExpr :: a -> IExpr

data TestIExpr = TestIExpr IExpr

data ValidTestIExpr = ValidTestIExpr TestIExpr

data ZeroTypedTestIExpr = ZeroTypedTestIExpr TestIExpr

data ArrowTypedTestIExpr = ArrowTypedTestIExpr TestIExpr

instance TestableIExpr TestIExpr where
  getIExpr (TestIExpr x) = x

instance Show TestIExpr where
  show (TestIExpr t) = show t

instance TestableIExpr ValidTestIExpr where
  getIExpr (ValidTestIExpr x) = getIExpr x

instance Show ValidTestIExpr where
  show (ValidTestIExpr v) = show v

instance TestableIExpr ZeroTypedTestIExpr where
  getIExpr (ZeroTypedTestIExpr x) = getIExpr x

instance Show ZeroTypedTestIExpr where
  show (ZeroTypedTestIExpr v) = show v

instance TestableIExpr ArrowTypedTestIExpr where
  getIExpr (ArrowTypedTestIExpr x) = getIExpr x

instance Show ArrowTypedTestIExpr where
  show (ArrowTypedTestIExpr x) = show x

lift1Texpr :: (IExpr -> IExpr) -> TestIExpr -> TestIExpr
lift1Texpr f (TestIExpr x) = TestIExpr $ f x

lift2Texpr :: (IExpr -> IExpr -> IExpr) -> TestIExpr -> TestIExpr -> TestIExpr
lift2Texpr f (TestIExpr a) (TestIExpr b) = TestIExpr $ f a b

instance Arbitrary TestIExpr where
  arbitrary = sized tree where
    tree i = let half = div i 2
                 pure2 = pure . TestIExpr
             in case i of
                  0 -> oneof $ map pure2 [zero, var]
                  x -> oneof
                    [ pure2 zero
                    , pure2 var
                    , lift2Texpr pair <$> tree half <*> tree half
                    , lift1Texpr SetEnv <$> tree (i - 1)
                    , lift1Texpr Defer <$> tree (i - 1)
                    , lift1Texpr Twiddle <$> tree (i - 1)
                    , lift2Texpr check <$> tree half <*> tree half
                    , lift1Texpr gate <$> tree (i - 1)
                    , lift1Texpr pleft <$> tree (i - 1)
                    , lift1Texpr pright <$> tree (i - 1)
                    , lift1Texpr Trace <$> tree (i - 1)
                    ]
  shrink (TestIExpr x) = case x of
    Zero -> []
    Env -> []
    (Gate x) -> TestIExpr x : (map (lift1Texpr gate) . shrink $ TestIExpr x)
    (PLeft x) -> TestIExpr x : (map (lift1Texpr pleft) . shrink $ TestIExpr x)
    (PRight x) -> TestIExpr x : (map (lift1Texpr pright) . shrink $ TestIExpr x)
    (Trace x) -> TestIExpr x : (map (lift1Texpr Trace) . shrink $ TestIExpr x)
    (SetEnv x) -> TestIExpr x : (map (lift1Texpr SetEnv) . shrink $ TestIExpr x)
    (Defer x) -> TestIExpr x : (map (lift1Texpr Defer) . shrink $ TestIExpr x)
    (Twiddle x) -> TestIExpr x : (map (lift1Texpr Twiddle) . shrink $ TestIExpr x)
    (Abort x) -> TestIExpr x : (map (lift1Texpr Abort) . shrink $ TestIExpr x)
    (Pair a b) -> TestIExpr a : TestIExpr  b :
      [lift2Texpr pair a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]

typeable x = case inferType (getIExpr x) of
  Left _ -> False
  _ -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = map ValidTestIExpr . filter typeable $ shrink te

zeroTyped x = inferType (getIExpr x) == Right ZeroTypeP

instance Arbitrary ZeroTypedTestIExpr where
  arbitrary = ZeroTypedTestIExpr <$> suchThat arbitrary zeroTyped
  shrink (ZeroTypedTestIExpr ztte) = map ZeroTypedTestIExpr . filter zeroTyped $ shrink ztte

simpleArrowTyped x = inferType (getIExpr x) == Right (ArrTypeP ZeroTypeP ZeroTypeP)

instance Arbitrary ArrowTypedTestIExpr where
  arbitrary = ArrowTypedTestIExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestIExpr atte) = map ArrowTypedTestIExpr . filter simpleArrowTyped $ shrink atte
