{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Common where

--import Control.Monad.State (State)
import Test.QuickCheck
import Test.QuickCheck.Gen
--import qualified Control.Monad.State as State

import SIL.TypeChecker
import SIL.Parser
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
                    , lift2Texpr check <$> tree half <*> tree half
                    , lift2Texpr Gate <$> tree half <*> tree half
                    , lift1Texpr pleft <$> tree (i - 1)
                    , lift1Texpr pright <$> tree (i - 1)
                    , pure2 Trace
                    ]
  shrink (TestIExpr x) = case x of
    Zero -> []
    Env -> []
    Gate a b -> TestIExpr a : TestIExpr b :
      [lift2Texpr Gate a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]
    (PLeft x) -> TestIExpr x : (map (lift1Texpr pleft) . shrink $ TestIExpr x)
    (PRight x) -> TestIExpr x : (map (lift1Texpr pright) . shrink $ TestIExpr x)
    Trace -> []
    (SetEnv x) -> TestIExpr x : (map (lift1Texpr SetEnv) . shrink $ TestIExpr x)
    (Defer x) -> TestIExpr x : (map (lift1Texpr Defer) . shrink $ TestIExpr x)
    Abort -> []
    (Pair a b) -> TestIExpr a : TestIExpr  b :
      [lift2Texpr pair a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]

typeable x = case inferType (fromSIL $ getIExpr x) of
  Left _ -> False
  _ -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = map ValidTestIExpr . filter typeable $ shrink te

zeroTyped x = inferType (fromSIL $ getIExpr x) == Right ZeroTypeP

instance Arbitrary ZeroTypedTestIExpr where
  arbitrary = ZeroTypedTestIExpr <$> suchThat arbitrary zeroTyped
  shrink (ZeroTypedTestIExpr ztte) = map ZeroTypedTestIExpr . filter zeroTyped $ shrink ztte

simpleArrowTyped x = inferType (fromSIL $ getIExpr x) == Right (ArrTypeP ZeroTypeP ZeroTypeP)

instance Arbitrary ArrowTypedTestIExpr where
  arbitrary = ArrowTypedTestIExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestIExpr atte) = map ArrowTypedTestIExpr . filter simpleArrowTyped $ shrink atte

instance Arbitrary UnprocessedParsedTerm where
  arbitrary = sized (genTree []) where
    {-
      leaves varList = oneof $
            (pure $ StringUP <$> chooseAny)
            : (IntUP <$> chooseAny)
            : (ChurchUP <$> chooseAny)
            : (pure UnsizedRecursionUP)
            (if not null varList then [VarUP <$> elements varList] else [])
-}
      leaves varList =
        oneof $
            (if not (null varList) then ((VarUP <$> elements varList) :) else id)
            [ StringUP <$> elements (map ((("s") <>) . show) [1..9]) -- chooseAny
            , (IntUP <$> chooseAny)
            , (ChurchUP <$> chooseAny)
            , (pure UnsizedRecursionUP)
            ]
      lambdaTerms = ["w", "x", "y", "z"]
      letTerms = map (("l" <>) . show) [1..255]
      identifierList = frequency
        [ (1, pure . cycle $ letTerms)
        , (3, pure . cycle $ lambdaTerms <> letTerms)
        , (1, cycle <$> shuffle (lambdaTerms <> letTerms))
        ]
      genTree varList i = let half = div i 2
                              third = div i 3
                              recur = genTree varList
                              childList = do
                                -- listSize <- chooseInt (0, i)
                                listSize <- choose (0, i)
                                let childShare = div i listSize
                                vectorOf listSize $ genTree varList childShare
                          in case i of
                                   0 -> leaves varList
                                   x -> oneof
                                     [ LeftUP <$> recur (i - 1)
                                     , RightUP <$> recur (i - 1)
                                     , TraceUP <$> recur (i - 1)
                                     , elements lambdaTerms >>= \var -> LamUP var <$> genTree (var : varList) (i - 1)
                                     , ITEUP <$> recur third <*> recur third <*> recur third
                                     , ListUP <$> childList
                                     , do
                                        -- listSize <- chooseInt (1, max i 1)
                                        listSize <- choose (2, max i 2)
                                        let childShare = div i listSize
                                        let makeList = \case
                                              [] -> pure []
                                              (v:vl) -> do
                                                newTree <- genTree (v:varList) childShare
                                                ((v,newTree) :) <$> makeList vl
                                        vars <- take listSize <$> identifierList
                                        childList <- makeList vars
                                        pure $ LetUP (init childList) (snd . last $ childList)
                                     , PairUP <$> recur half <*> recur half
                                     , AppUP <$> recur half <*> recur half
                                     ]
      {-
      let leaves = State.get >>= \varList -> oneof $
            (pure $ StringUP <$> chooseAny)
            : (pure $ IntUP <$> chooseAny)
            : (pure $ ChurchUP <$> chooseAny)
            : (pure UnsizedRecursionUP)
            (if not null varList then [pure $ VarUP <$> oneof varList] else [])
          genTree i = let half = div i 2
                      in case i of
                           0 -> leaves
                           x -> oneof
                             [
                             ]
-}
