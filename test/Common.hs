{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Common where

import           Data.Bifunctor

import           Test.QuickCheck
import           Test.QuickCheck.Gen

import           Telomare
import           Telomare.Parser
import           Telomare.TypeChecker

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

instance Arbitrary DataType where
  arbitrary = sized gen where
    gen i = let half = div i 2 in oneof $ pure ZeroType :
      if i < 1
      then []
      else [ ArrType <$> gen half <*> gen half
           , PairType <$> gen half <*> gen half
           ]

zeroTyped = null . typeCheck ZeroTypeP . fromTelomare . getIExpr

instance Arbitrary DataTypedIExpr where
  arbitrary = IExprWrapper <$> sized (tree Nothing ZeroType) where
    tree :: Maybe DataType -> DataType -> Int -> Gen IExpr
    tree ti t i = let half = div i 2
                      optionEnv = if ti == Just t
                        then (pure var :)
                        else id
                      optionGate ti' to = if ti' == ZeroType
                        then ((pure Gate <*> tree ti to half <*> tree ti to half) :)
                        else id
                      setEnvOption to = arbitrary >>= makeSetEnv where
                        makeSetEnv ti' = SetEnv <$> tree ti (PairType (ArrType ti' to) ti') (i - 1)
                      leftOption to = arbitrary >>= (\ti' -> pleft <$> tree ti (PairType to ti') (i - 1))
                      rightOption to = arbitrary >>= (\ti' -> pright <$> tree ti (PairType ti' to) (i - 1))
                  in oneof . optionEnv $ case t of
                       ZeroType ->
                         pure zero : if i < 1
                         then []
                         else [ tree ti (PairType ZeroType ZeroType) i
                              , setEnvOption ZeroType
                              , leftOption ZeroType
                              , rightOption ZeroType
                              ]
                       PairType ta tb ->
                         (pure pair <*> tree ti ta half <*> tree ti tb half) :
                         if i < 1
                         then []
                         else [ setEnvOption (PairType ta tb)
                              , leftOption (PairType ta tb)
                              , rightOption (PairType ta tb)
                              ]
                       ArrType ti' to ->
                         (Defer <$> tree (Just ti') to (i - 1)) :
                         if i < 1
                         then []
                         else optionGate ti' to
                         [ leftOption (ArrType ti' to)
                         , rightOption (ArrType ti' to)
                         ]
  shrink (IExprWrapper x) = map (IExprWrapper . getIExpr) . filter zeroTyped . shrink $ TestIExpr x

typeable x = case inferType (fromTelomare $ getIExpr x) of
  Left _ -> False
  _      -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = map ValidTestIExpr . filter typeable $ shrink te

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
                                   , HashUP <$> recur (i - 1)
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
    HashUP x -> x : map HashUP (shrink x)
    LeftUP x -> x : map LeftUP (shrink x)
    RightUP x -> x : map RightUP (shrink x)
    TraceUP x -> x : map TraceUP (shrink x)
    LamUP v x -> x : map (LamUP v) (shrink x)
    ITEUP i t e -> i : t : e : [ITEUP ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    ListUP l -> case l of
      [e] -> if null $ shrink e then [e] else e : map (ListUP . pure) (shrink e)
      _   -> head l : ListUP (tail l) : map (ListUP . shrink) l
  {-
    LetUP l i -> i : case l of -- TODO make this do proper, full enumeration
      [(v,e)] -> if null $ shrink e then [e] else e : map (flip LetUP i . pure . (v,)) (shrink e) <> (map (LetUP l) (shrink i))
      _ -> let shrinkBinding (n, v) = map (n,) $ shrink v
           in snd (head l) : LetUP (tail l) i : map (flip LetUP i . second shrink) l
-}
    LetUP l i -> let shrinkBinding (n, v) = map (n,) $ shrink v
                     removeAt n x = let (f,s) = splitAt n x in f ++ tail s
                     makeOptions f n [] = error "debugging split here"
                     makeOptions f n x = let (pa,c:pz) = splitAt n x in map ((pa ++) . (:pz)) $ f c
                     lessBindings = if length l > 1
                       then [LetUP (removeAt n l) i | n <- [0..length l - 1]]
                       else []
                 in i : lessBindings
                    ++ concat [map (flip LetUP i) $ makeOptions shrinkBinding n l | n <- [0..length l - 1]]
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
