{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE DeriveFunctor              #-}

module Common where

import           Telomare
import           Telomare.Parser
import           Telomare.TypeChecker
import           Test.QuickCheck
import           Test.QuickCheck.Gen

class TestableIExpr a where
  getIExpr :: a -> IExpr

data TestIExpr = TestIExpr IExpr

data ValidTestIExpr = ValidTestIExpr TestIExpr

data ArrowTypedTestIExpr = ArrowTypedTestIExpr TestIExpr

data IExprWrapper a = IExprWrapper a
  deriving (Eq, Show, Functor)

instance Applicative IExprWrapper where
  pure = IExprWrapper
  (<*>) (IExprWrapper f) (IExprWrapper x) = IExprWrapper $ f x

type DataTypedIExpr = IExprWrapper IExpr

-- TODO move these into Telomare.hs and make type checking use them
data BasicType
  = NotFunctionType
  | PairTypeB ExtendedType ExtendedType
  deriving (Eq, Show)

data ArrowType
  = ArrowType ExtendedType BasicType -- Gate as currently designed can't return functions this way... careful
  deriving (Eq, Show)

data ExtendedType
  = BT BasicType
  | AT ArrowType
  deriving (Eq, Show)

instance TestableIExpr DataTypedIExpr where
  getIExpr (IExprWrapper x) = x

instance TestableIExpr TestIExpr where
  getIExpr (TestIExpr x) = x

instance Show TestIExpr where
  show (TestIExpr t) = show t

instance TestableIExpr ValidTestIExpr where
  getIExpr (ValidTestIExpr x) = getIExpr x

instance Show ValidTestIExpr where
  show (ValidTestIExpr v) = show v

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
    (Pair a b) -> TestIExpr a : TestIExpr  b :
      [lift2Texpr pair a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]

instance Arbitrary BasicType where
  arbitrary = sized gen where
    gen i = if i < 1
      then pure NotFunctionType
      else oneof
      [ pure NotFunctionType
      , PairTypeB <$> scale (`div` 2) arbitrary <*> scale (`div` 2) arbitrary
      ]

instance Arbitrary ArrowType where
  arbitrary = ArrowType <$> scale (`div` 2) arbitrary <*> scale (`div` 2) arbitrary

instance Arbitrary ExtendedType where
  arbitrary = sized gen where
    gen i = if i < 1
      then BT <$> arbitrary
      else oneof
      [ BT <$> arbitrary
      , AT <$> arbitrary
      ]

instance Arbitrary DataTypedIExpr where
  arbitrary = IExprWrapper <$> sized (tree Nothing (BT NotFunctionType)) where
    tree :: Maybe ExtendedType -> ExtendedType -> Int -> Gen IExpr
    tree ti t i = let half = div i 2
                      optionEnv = if ti == Just t
                        then (pure var :)
                        else id
                      optionGate ti' to = if ti' == BT NotFunctionType
                        then ((pure Gate <*> tree ti (BT to) half <*> tree ti (BT to) half) :)
                        else id
                      setEnvOption to = arbitrary >>= makeSetEnv where
                        makeSetEnv ti' = SetEnv <$> tree ti (BT $ PairTypeB (AT $ ArrowType ti' to) ti') (i - 1)
                      leftOption to = arbitrary >>= (\ti' -> pleft <$> tree ti (BT $ PairTypeB to ti') (i - 1))
                      rightOption to = arbitrary >>= (\ti' -> pright <$> tree ti (BT $ PairTypeB ti' to) (i - 1))
                  in oneof . optionEnv $ case t of
                       BT NotFunctionType -> if i < 1
                         then [pure zero]
                         else
                         [ tree ti (BT $ PairTypeB (BT NotFunctionType) (BT NotFunctionType)) i
                         , setEnvOption NotFunctionType
                         , leftOption (BT NotFunctionType)
                         , rightOption (BT NotFunctionType)
                         ]
                       BT (PairTypeB ta tb) ->
                         [ pure pair <*> tree ti ta half <*> tree ti tb half
                         , setEnvOption (PairTypeB ta tb)
                         , leftOption (BT (PairTypeB ta tb))
                         , rightOption (BT (PairTypeB ta tb))
                         ]
                       AT (ArrowType ti' to) ->
                         optionGate ti' to
                         [ leftOption (AT (ArrowType ti' to))
                         , rightOption (AT (ArrowType ti' to))
                         , Defer <$> tree (Just ti') (BT to) (i - 1)
                         ]
  {-
  arbitrary = sized (tree Nothing (BT NotFunctionType)) where
    tree ti t i = let half = div i 2
                      pure2 = pure . pure
                      optionEnv = if ti == Just t
                        then (pure2 var :)
                        else id
                      optionGate ti' to = if ti' == BT NotFunctionType
                        then ((pure2 Gate <*> tree ti (BT to) half <*> tree ti (BT to) half) :)
                        else id
                      setEnvOption to = arbitrary >>= makeSetEnv where
                        makeSetEnv ti' = fmap SetEnv <$> tree ti (BT $ PairTypeB (AT $ ArrowType ti' to) ti') (i - 1)
                      leftOption to = arbitrary >>= (\ti' -> fmap pleft <$> tree ti (BT $ PairTypeB to ti') (i - 1))
                      rightOption to = arbitrary >>= (\ti' -> fmap pright <$> tree ti (BT $ PairTypeB ti' to) (i - 1))
                  in oneof . optionEnv $ case t of
                       BT NotFunctionType -> if i < 1
                         then [pure2 zero]
                         else
                         [ tree ti (BT $ PairTypeB (BT NotFunctionType) (BT NotFunctionType)) i
                         , setEnvOption NotFunctionType
                         , leftOption (BT NotFunctionType)
                         , rightOption (BT NotFunctionType)
                         ]
                       BT (PairTypeB ta tb) ->
                         [ pure2 pair <*> tree ti ta half <*> tree ti tb half
                         , setEnvOption (PairTypeB ta tb)
                         , leftOption (BT (PairTypeB ta tb))
                         , rightOption (BT (PairTypeB ta tb))
                         ]
                       AT (ArrowType ti' to) ->
                         optionGate ti' to
                         [ leftOption (AT (ArrowType ti to))
                         , rightOption (AT (ArrowType ti to))
                         , fmap Defer <$> tree (Just ti') to (i - 1)
                         ]
-}

typeable x = case inferType (fromTelomare $ getIExpr x) of
  Left _ -> False
  _      -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = map ValidTestIExpr . filter typeable $ shrink te

{-
zeroTyped x = inferType (fromTelomare $ getIExpr x) == Right ZeroTypeP

instance Arbitrary ZeroTypedTestIExpr where
  arbitrary = ZeroTypedTestIExpr <$> suchThat arbitrary zeroTyped
  shrink (ZeroTypedTestIExpr ztte) = map ZeroTypedTestIExpr . filter zeroTyped $ shrink ztte
  -}

simpleArrowTyped x = inferType (fromTelomare $ getIExpr x) == Right (ArrTypeP ZeroTypeP ZeroTypeP)

instance Arbitrary ArrowTypedTestIExpr where
  arbitrary = ArrowTypedTestIExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestIExpr atte) = map ArrowTypedTestIExpr . filter simpleArrowTyped $ shrink atte

instance Arbitrary UnprocessedParsedTerm where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen UnprocessedParsedTerm
    leaves varList =
      oneof $
          (if not (null varList) then ((VarUP <$> elements varList) :) else id)
          [ StringUP <$> elements (map ((("s") <>) . show) [1..9]) -- chooseAny
          , (IntUP <$> elements [0..9])
          , (ChurchUP <$> elements [0..9])
          , (pure UnsizedRecursionUP)
          , (pure UniqueUP)
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = map (("l" <>) . show) [1..255]
    identifierList = frequency
      [ (1, pure . cycle $ letTerms)
      , (3, pure . cycle $ lambdaTerms <> letTerms)
      , (1, cycle <$> shuffle (lambdaTerms <> letTerms))
      ]
    genTree :: [String] -> Int -> Gen UnprocessedParsedTerm
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
                                   [ leaves varList
                                   , LeftUP <$> recur (i - 1)
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
  shrink = \case
    UniqueUP -> []
    StringUP s -> case s of
      [] -> []
      _  -> pure . StringUP $ tail s
    IntUP i -> case i of
      0 -> []
      x -> pure . IntUP $ x - 1
    ChurchUP i -> case i of
      0 -> []
      x -> pure . ChurchUP $ x - 1
    UnsizedRecursionUP -> []
    VarUP _ -> []
    LeftUP x -> x : map LeftUP (shrink x)
    RightUP x -> x : map RightUP (shrink x)
    TraceUP x -> x : map TraceUP (shrink x)
    LamUP v x -> x : map (LamUP v) (shrink x)
    ITEUP i t e -> i : t : e : [ITEUP ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    ListUP l -> case l of
      [e] -> if null $ shrink e then [e] else e : map (ListUP . pure) (shrink e)
      _ -> head l : ListUP (tail l) : map (ListUP . shrink) l
    LetUP l i -> i : case l of -- TODO make this do proper, full enumeration
      [(v,e)] -> if null $ shrink e then [e] else e : map (flip LetUP i . pure . (v,)) (shrink e) <> (map (LetUP l) (shrink i))
      _ -> snd (head l) : LetUP (tail l) i : map (flip LetUP i. shrink) l
    PairUP a b -> a : b : [PairUP na nb | (na, nb) <- shrink (a,b)]
    AppUP f i -> f : i : [AppUP nf ni | (nf, ni) <- shrink (f,i)]

instance Arbitrary Term1 where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen Term1
    leaves varList =
      oneof $
          (if not (null varList) then ((TVar <$> elements varList) :) else id)
          [ pure TZero
          , pure TLimitedRecursion
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = map (("l" <>) . show) [1..255]
    identifierList = frequency
      [ (1, pure . cycle $ letTerms)
      , (3, pure . cycle $ lambdaTerms <> letTerms)
      , (1, cycle <$> shuffle (lambdaTerms <> letTerms))
      ]
    genTree :: [String] -> Int -> Gen Term1
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
                                   [ leaves varList
                                   , TLeft <$> recur (i - 1)
                                   , TRight <$> recur (i - 1)
                                   , TTrace <$> recur (i - 1)
                                   , elements lambdaTerms >>= \var -> TLam (Open var) <$> genTree (var : varList) (i - 1)
                                   , TITE <$> recur third <*> recur third <*> recur third
                                   , TPair <$> recur half <*> recur half
                                   , TApp <$> recur half <*> recur half
                                   ]
  shrink = \case
    TZero -> []
    TLimitedRecursion -> []
    TVar _ -> []
    TLeft x -> x : map TLeft (shrink x)
    TRight x -> x : map TRight (shrink x)
    TTrace x -> x : map TTrace (shrink x)
    TLam v x -> x : map (TLam v) (shrink x)
    TITE i t e -> i : t : e : [TITE ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    TPair a b -> a : b : [TPair na nb | (na, nb) <- shrink (a,b)]
    TApp f i -> f : i : [TApp nf ni | (nf, ni) <- shrink (f,i)]
