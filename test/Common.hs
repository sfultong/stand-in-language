{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ScopedTypeVariables     #-}
module Common where

import Control.Applicative
import Data.Bifunctor
import qualified Data.Map as Map
import System.IO
import qualified System.IO.Strict as Strict
import System.Posix.IO
import System.Posix.Process
import System.Posix.Types (ProcessID)
import Telomare
import Telomare.Eval (runMain)
import Telomare.Parser
import Telomare.Resolver
import Telomare.TypeChecker
import Test.QuickCheck
import Test.QuickCheck.Gen
import Control.Comonad.Cofree (Cofree ((:<)))

class TestableIExpr a where
  getIExpr :: a -> IExpr

newtype TestIExpr = TestIExpr IExpr

newtype ValidTestIExpr = ValidTestIExpr TestIExpr

newtype ArrowTypedTestIExpr = ArrowTypedTestIExpr TestIExpr

newtype URTestExpr = URTestExpr {unURTest :: Term3} deriving Show

newtype IExprWrapper a = IExprWrapper a
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
                  0 -> oneof $ fmap pure2 [zero, var]
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
    (PLeft x) -> TestIExpr x : (fmap (lift1Texpr pleft) . shrink $ TestIExpr x)
    (PRight x) -> TestIExpr x : (fmap (lift1Texpr pright) . shrink $ TestIExpr x)
    Trace -> []
    (SetEnv x) -> TestIExpr x : (fmap (lift1Texpr SetEnv) . shrink $ TestIExpr x)
    (Defer x) -> TestIExpr x : (fmap (lift1Texpr Defer) . shrink $ TestIExpr x)
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

genTypedTree :: Maybe DataType -> DataType -> Int -> Gen IExpr
genTypedTree ti t i =
  let half = div i 2
      optionEnv = if ti == Just t
                  then (pure var :)
                  else id
      optionGate ti' to = if ti' == ZeroType
                          then ((Gate <$> genTypedTree ti to half <*> genTypedTree ti to half) :)
                          else id
      setEnvOption to = arbitrary >>= makeSetEnv where
        makeSetEnv ti' = SetEnv <$> genTypedTree ti (PairType (ArrType ti' to) ti') (i - 1)
      leftOption to = arbitrary >>= (\ti' -> pleft <$> genTypedTree ti (PairType to ti') (i - 1))
      rightOption to = arbitrary >>= (\ti' -> pright <$> genTypedTree ti (PairType ti' to) (i - 1))
  in oneof . optionEnv $ case t of
                    ZeroType ->
                      pure zero : if i < 1
                      then []
                      else [ genTypedTree ti (PairType ZeroType ZeroType) i
                          , setEnvOption ZeroType
                          , leftOption ZeroType
                          , rightOption ZeroType
                          ]
                    PairType ta tb ->
                      (pair <$> genTypedTree ti ta half <*> genTypedTree ti tb half) :
                      if i < 1
                      then []
                      else [ setEnvOption (PairType ta tb)
                          , leftOption (PairType ta tb)
                          , rightOption (PairType ta tb)
                          ]
                    ArrType ti' to ->
                      (Defer <$> genTypedTree (Just ti') to (i - 1)) :
                      if i < 1
                      then []
                      else optionGate ti' to
                      [ leftOption (ArrType ti' to)
                      , rightOption (ArrType ti' to)
                      ]

genTypedTree' :: Maybe DataType -> DataType -> Int -> Gen (BreakState' RecursionPieceFrag UnsizedRecursionToken)
genTypedTree' ti t i =
  let half = div i 2
      optionEnv = if ti == Just t
                  then (pure (pure $ (0,0) :< EnvFragF) :)
                  else id
      optionGate ti' to = if ti' == ZeroType
                          then ((liftA2 (\x y -> (0,0) :< GateFragF x y) <$> genTypedTree' ti to half <*> genTypedTree' ti to half) :)
                          else id
      setEnvOption to = arbitrary >>= makeSetEnv where
        makeSetEnv ti' = fmap (((0,0) :<) . SetEnvFragF) <$> genTypedTree' ti (PairType (ArrType ti' to) ti') (i - 1)
      leftOption to = arbitrary >>= (\ti' -> fmap (((0,0) :<) . LeftFragF) <$> genTypedTree' ti (PairType to ti') (i - 1))
      rightOption to = arbitrary >>= (\ti' -> fmap (((0,0) :<) . RightFragF) <$> genTypedTree' ti (PairType ti' to) (i - 1))
  in oneof . optionEnv $ case t of
    ZeroType -> pure (pure $ (0,0) :< ZeroFragF) :
     if i < 1
     then []
     else [ genTypedTree' ti (PairType ZeroType ZeroType) i
          , setEnvOption ZeroType
          , leftOption ZeroType
          , rightOption ZeroType
          ]
    PairType ta tb ->
      (liftA2 (\x y -> (0,0) :< PairFragF x y) <$> genTypedTree' ti ta half <*> genTypedTree' ti tb half) :
      if i < 1
      then []
      else [ setEnvOption (PairType ta tb)
           , leftOption (PairType ta tb)
           , rightOption (PairType ta tb)
           ]
    ArrType ti' to ->
      (deferF <$> genTypedTree' (Just ti') to (i - 1)) :
      if i < 1
      then []
      else optionGate ti' to
             [ leftOption (ArrType ti' to)
             , rightOption (ArrType ti' to)
             ]

instance Arbitrary DataTypedIExpr where
  arbitrary = IExprWrapper <$> sized (genTypedTree Nothing ZeroType)
  shrink (IExprWrapper x) = fmap (IExprWrapper . getIExpr) . filter zeroTyped . shrink $ TestIExpr x

instance Arbitrary URTestExpr where -- TODO needs to be tested since refactor
  -- arbitrary = URTestExpr . Term3 . fmap FragExprUR  . buildFragMap  . wrapWithUR <$>  mapM sized undefined
  arbitrary = URTestExpr . Term3 . fmap FragExprUR . buildFragMap . wrapWithUR <$> mapM sized
      [ genTypedTree' Nothing (PairType (ArrType ZeroType ZeroType) ZeroType)
      , genTypedTree' Nothing (PairType (ArrType (PairType (ArrType ZeroType ZeroType) ZeroType)
                                                 (PairType (ArrType ZeroType ZeroType) ZeroType))
                                         ZeroType)
      , genTypedTree' Nothing (PairType (ArrType ZeroType ZeroType) ZeroType)
      , genTypedTree' Nothing ZeroType
      ]
      where wrapWithUR [t, r, b, i] =
              appF (unsizedRecursionWrapper (toEnum 0) t r b) i


typeable x = case inferType (fromTelomare $ getIExpr x) of
  Left _ -> False
  _      -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = fmap ValidTestIExpr . filter typeable $ shrink te

simpleArrowTyped x = inferType (fromTelomare $ getIExpr x) == Right (ArrTypeP ZeroTypeP ZeroTypeP)

instance Arbitrary ArrowTypedTestIExpr where
  arbitrary = ArrowTypedTestIExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestIExpr atte) = fmap ArrowTypedTestIExpr . filter simpleArrowTyped $ shrink atte

instance Arbitrary UnprocessedParsedTerm where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen UnprocessedParsedTerm
    leaves varList =
      oneof $
          (if not (null varList) then ((VarUP <$> elements varList) :) else id)
          [ StringUP <$> elements (fmap (("s" <>) . show) [1..9]) -- chooseAny
          , IntUP <$> elements [0..9]
          , ChurchUP <$> elements [0..9]
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = fmap (("l" <>) . show) [1..255]
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
                                   , UnsizedRecursionUP <$> recur third <*> recur third <*> recur third
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
    UnsizedRecursionUP t r b -> t : r : b : [UnsizedRecursionUP nt nr nb | (nt, nr, nb) <- shrink (t,r,b)]
    VarUP _ -> []
    HashUP x -> x : fmap HashUP (shrink x)
    LeftUP x -> x : fmap LeftUP (shrink x)
    RightUP x -> x : fmap RightUP (shrink x)
    TraceUP x -> x : fmap TraceUP (shrink x)
    LamUP v x -> x : fmap (LamUP v) (shrink x)
    ITEUP i t e -> i : t : e : [ITEUP ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    ListUP l -> case l of
      [e] -> if null $ shrink e then [e] else e : fmap (ListUP . pure) (shrink e)
      _   -> head l : ListUP (tail l) : fmap (ListUP . shrink) l
  {-
    LetUP l i -> i : case l of -- TODO make this do proper, full enumeration
      [(v,e)] -> if null $ shrink e then [e] else e : map (flip LetUP i . pure . (v,)) (shrink e) <> (map (LetUP l) (shrink i))
      _ -> let shrinkBinding (n, v) = map (n,) $ shrink v
           in snd (head l) : LetUP (tail l) i : map (flip LetUP i . second shrink) l
-}
    LetUP l i -> let shrinkBinding (n, v) = ((n,) <$> shrink v)
                     removeAt n x = let (f,s) = splitAt n x in (f <> tail s)
                     makeOptions f n [] = error "debugging split here"
                     makeOptions f n x = let (pa,c:pz) = splitAt n x in ((pa ++) . (:pz) <$> f c)
                     lessBindings = if length l > 1
                       then [LetUP (removeAt n l) i | n <- [0..length l - 1]]
                       else []
                 in i : (lessBindings <> concat [(`LetUP` i) <$> makeOptions shrinkBinding n l | n <- [0..length l - 1]])
    PairUP a b -> a : b : [PairUP na nb | (na, nb) <- shrink (a,b)]
    AppUP f i -> f : i : [AppUP nf ni | (nf, ni) <- shrink (f,i)]

instance Arbitrary Term1 where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen Term1
    leaves varList =
      oneof $
          (if not (null varList) then ((((0,0) :<) . TVarF <$> elements varList) :) else id)
          [ pure $ (0,0) :< TZeroF
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = fmap (("l" <>) . show) [1..255]
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
                                   , ((0,0) :<) . THashF <$> recur (i - 1)
                                   , ((0,0) :<) . TLeftF <$> recur (i - 1)
                                   , ((0,0) :<) . TRightF <$> recur (i - 1)
                                   , ((0,0) :<) . TTraceF <$> recur (i - 1)
                                   , elements lambdaTerms >>= \var -> ((0,0) :<) . TLamF (Open var) <$> genTree (var : varList) (i - 1)
                                   , (\a b c -> (0,0) :< TITEF a b c) <$> recur third <*> recur third <*> recur third
                                   , (\a b c -> (0,0) :< TLimitedRecursionF a b c) <$> recur third <*> recur third <*> recur third
                                   , (\a b -> (0,0) :< TPairF a b) <$> recur half <*> recur half
                                   , (\a b -> (0,0) :< TAppF a b) <$> recur half <*> recur half
                                   ]
  shrink = \case
    _ :< TZeroF -> []
    anno :< TLimitedRecursionF t r b -> t : r : b : [anno :< TLimitedRecursionF nt nr nb | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< TVarF _ -> []
    anno :< THashF x -> x : fmap ((anno :<) . THashF) (shrink x)
    anno :< TLeftF x -> x : fmap ((anno :<) . TLeftF) (shrink x)
    anno :< TRightF x -> x : fmap ((anno :<) . TRightF) (shrink x)
    anno :< TTraceF x -> x : fmap ((anno :<) . TTraceF) (shrink x)
    anno :< TLamF v x -> x : fmap ((anno :<) . TLamF v) (shrink x)
    anno :< TITEF i t e -> i : t : e : [anno :< TITEF ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< TPairF a b -> a : b : [anno :< TPairF na nb | (na, nb) <- shrink (a,b)]
    anno :< TAppF f i -> f : i : [anno :< TAppF nf ni | (nf, ni) <- shrink (f,i)]

instance Arbitrary Term2 where
  arbitrary = do
    term1 <- arbitrary :: Gen Term1
    let term2 = case debruijinize [] term1 of
                  Left str -> error $ "Non valid `Term1` generated from `arbitrarry :: Gen Term1`: "
                                        <> show term1
                                        <> " With error message: "
                                        <> str
                  Right t2 -> t2
    pure term2
  shrink = \case
    _ :< TZeroF -> []
    anno :< TLimitedRecursionF t r b -> t : r : b : [anno :< TLimitedRecursionF nt nr nb | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< TVarF _ -> []
    anno :< THashF x -> x : fmap ((anno :<) . THashF) (shrink x)
    anno :< TLeftF x -> x : fmap ((anno :<) . TLeftF) (shrink x)
    anno :< TRightF x -> x : fmap ((anno :<) . TRightF) (shrink x)
    anno :< TTraceF x -> x : fmap ((anno :<) . TTraceF) (shrink x)
    anno :< TLamF v x -> x : fmap ((anno :<) . TLamF v) (shrink x)
    anno :< TITEF i t e -> i : t : e : [anno :< TITEF ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< TPairF a b -> a : b : [anno :< TPairF na nb | (na, nb) <- shrink (a,b)]
    anno :< TAppF f i -> f : i : [anno :< TAppF nf ni | (nf, ni) <- shrink (f,i)]

runTelomare :: String
            -> ((ProcessID, Handle, Handle, Handle) -> IO a)
            -> IO String
runTelomare str action = do
  preludeString <- Strict.readFile "Prelude.tel"
  (pid, hIn, hOut, hErr) <- forkWithStandardFds $ runMain preludeString str
  a <- action (pid, hIn, hOut, hErr)
  hGetContents hOut

forkWithStandardFds :: IO () -> IO (ProcessID, Handle, Handle, Handle)
forkWithStandardFds act = do
    (r0, w0) <- createPipe
    (r1, w1) <- createPipe
    (r2, w2) <- createPipe
    pid <- forkProcess $ do
      -- the six closeFd's aren't strictly speaking necessary,
      -- but they're good hygiene
      closeFd w0 >> dupTo r0 stdInput
      closeFd r1 >> dupTo w1 stdOutput
      closeFd r2 >> dupTo w2 stdError
      act
    hIn  <- closeFd r0 >> fdToHandle w0
    hOut <- closeFd w1 >> fdToHandle r1
    hErr <- closeFd w2 >> fdToHandle r2
    pure (pid, hIn, hOut, hErr)
