{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module Common where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor
import Data.Fix (Fix (..))
import Data.Functor.Foldable (Corecursive (..))
import qualified Data.Map as Map
import System.IO
import System.Posix.IO
import System.Posix.Process
import System.Posix.Types (ProcessID)
import Telomare
import Telomare.Parser
import Telomare.Resolver
import Telomare.TypeChecker
import Test.QuickCheck
import Test.QuickCheck.Gen

class TestableIExpr a where
  getIExpr :: a -> StuckExpr -- maybe this should be StuckExpr

newtype TestIExpr = TestIExpr StuckExpr

newtype ValidTestIExpr = ValidTestIExpr TestIExpr

newtype ArrowTypedTestIExpr = ArrowTypedTestIExpr TestIExpr

newtype URTestExpr = URTestExpr {unURTest :: Term3} deriving Show

newtype IExprWrapper a = IExprWrapper a
  deriving (Eq, Show, Functor)

instance Applicative IExprWrapper where
  pure = IExprWrapper
  (<*>) (IExprWrapper f) (IExprWrapper x) = IExprWrapper $ f x

type DataTypedIExpr = IExprWrapper StuckExpr

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

lift1Texpr :: (StuckExpr -> StuckExpr) -> TestIExpr -> TestIExpr
lift1Texpr f (TestIExpr x) = TestIExpr $ f x

lift2Texpr :: (StuckExpr -> StuckExpr -> StuckExpr) -> TestIExpr -> TestIExpr -> TestIExpr
lift2Texpr f (TestIExpr a) (TestIExpr b) = TestIExpr $ f a b

instance Arbitrary TestIExpr where
  arbitrary = sized tree where
    tree i = let half = div i 2
                 pure2 = pure . TestIExpr
             in case i of
                  0 -> oneof $ fmap pure2 [ZeroB, EnvB, GateB]
                  x -> oneof
                    [ pure2 ZeroB
                    , pure2 EnvB
                    , pure2 GateB
                    , lift2Texpr PairB <$> tree half <*> tree half
                    , lift1Texpr SetEnvB <$> tree (i - 1)
                    , lift1Texpr (StuckEE  . DeferSF (toEnum (-1))) <$> tree (i - 1)
                    , lift1Texpr LeftB <$> tree (i - 1)
                    , lift1Texpr RightB <$> tree (i - 1)
                    ]
  shrink (TestIExpr x) = case x of
    ZeroB -> []
    StuckEE EnvSF -> []
    StuckEE GateSF -> []
    StuckEE (LeftSF x) -> TestIExpr x : (fmap (lift1Texpr LeftB) . shrink $ TestIExpr x)
    StuckEE (RightSF x) -> TestIExpr x : (fmap (lift1Texpr RightB) . shrink $ TestIExpr x)
    StuckEE (SetEnvSF x) -> TestIExpr x : (fmap (lift1Texpr SetEnvB) . shrink $ TestIExpr x)
    StuckEE (DeferSF fi x) -> TestIExpr x : (fmap (lift1Texpr (StuckEE . DeferSF fi)) . shrink $ TestIExpr x)
    PairB a b -> TestIExpr a : TestIExpr  b :
      [lift2Texpr PairB a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]

instance Arbitrary DataType where
  arbitrary = sized gen where
    gen i = let half = div i 2 in oneof $ pure ZeroType :
      if i < 1
      then []
      else [ ArrType <$> gen half <*> gen half
           , PairType <$> gen half <*> gen half
           ]

zeroTyped = null . typeCheck (embed ZeroTypeP) . fromTelomare . getIExpr

genTypedTree :: Maybe DataType -> DataType -> Int -> Gen StuckExpr
genTypedTree ti t i =
  let half = div i 2
      optionEnv = if ti == Just t
                  then (pure EnvB :)
                  else id
      gateMatch = \case
        ArrType (PairType a b) c | a == b && b == c -> True
        _ -> False
      optionGate :: DataType -> DataType -> [Gen StuckExpr] -> [Gen StuckExpr]
      optionGate ti' to = if ti' == ZeroType && gateMatch to
                          then (pure GateB :)
                          else id
      setEnvOption to = arbitrary >>= makeSetEnv where
        makeSetEnv ti' = SetEnvB <$> genTypedTree ti (PairType (ArrType ti' to) ti') (i - 1)
      leftOption to = arbitrary >>= (\ti' -> LeftB <$> genTypedTree ti (PairType to ti') (i - 1))
      rightOption to = arbitrary >>= (\ti' -> RightB <$> genTypedTree ti (PairType ti' to) (i - 1))
  in oneof . optionEnv $ case t of
                    ZeroType ->
                      pure ZeroB : if i < 1
                      then []
                      else [ genTypedTree ti (PairType ZeroType ZeroType) i
                          , setEnvOption ZeroType
                          , leftOption ZeroType
                          , rightOption ZeroType
                          ]
                    PairType ta tb ->
                      (PairB <$> genTypedTree ti ta half <*> genTypedTree ti tb half) :
                      if i < 1
                      then []
                      else [ setEnvOption (PairType ta tb)
                          , leftOption (PairType ta tb)
                          , rightOption (PairType ta tb)
                          ]
                    ArrType ti' to ->
                      (StuckEE . DeferSF (toEnum (-1)) <$> genTypedTree (Just ti') to (i - 1)) :
                      if i < 1
                      then []
                      else optionGate ti' to
                      [ leftOption (ArrType ti' to)
                      , rightOption (ArrType ti' to)
                      ]

instance Arbitrary DataTypedIExpr where
  arbitrary = IExprWrapper <$> sized (genTypedTree Nothing ZeroType)
  shrink (IExprWrapper x) = fmap (IExprWrapper . getIExpr) . filter zeroTyped . shrink $ TestIExpr x

typeable x = case inferType (fromTelomare $ getIExpr x) of
  Left _ -> False
  _      -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = fmap ValidTestIExpr . filter typeable $ shrink te

simpleArrowTyped x = inferType (fromTelomare $ getIExpr x) == Right (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP))

instance Arbitrary ArrowTypedTestIExpr where
  arbitrary = ArrowTypedTestIExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestIExpr atte) = fmap ArrowTypedTestIExpr . filter simpleArrowTyped $ shrink atte

instance Arbitrary UnprocessedParsedTerm where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen UnprocessedParsedTerm
    leaves varList =
      oneof $
          (if not (null varList) then ((UnprocessedParsedTerm . Fix . UnprocessedParsedTermL . VarF <$> elements varList) :) else id)
          [ UnprocessedParsedTerm . Fix . StringUPF <$> elements (fmap (("s" <>) . show) [1..9]) -- chooseAny
          , UnprocessedParsedTerm . Fix . IntUPF <$> elements [0..9]
          , UnprocessedParsedTerm . Fix . UnprocessedParsedTermH . ChurchF <$> elements [0..9]
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = fmap (("l" <>) . show) [1..255]
    identifierList :: Gen [String]
    identifierList = frequency
      [ (1, pure . cycle $ letTerms)
      , (3, pure . cycle $ lambdaTerms <> letTerms)
      , (1, cycle <$> shuffle (lambdaTerms <> letTerms))
      ]
    genImportName :: Gen String
    genImportName = do
      firstChar <- elements $ ['a'..'z'] <> ['A'..'Z']
      len <- choose (3, 15)
      rest <- vectorOf (len - 1)
                       (frequency [ (10, elements (['a'..'z'] <> ['A'..'Z'] <> ['0'..'9']))
                                  , (1, pure '_')
                                  , (1, pure '.')
                                  ])
      return (firstChar : rest)
    mkUPT :: UnprocessedParsedTermF Pattern UPT -> UnprocessedParsedTerm
    mkUPT = UnprocessedParsedTerm . Fix
    wrap :: UnprocessedParsedTerm -> UPT
    wrap = unUnprocessedParsedTerm
    genTree :: [String] -> Int -> Gen UnprocessedParsedTerm
    genTree varList i = let half = div i 2
                            third = div i 3
                            recur = genTree varList
                            childList = do
                              listSize <- choose (0, i)
                              let childShare = div i listSize
                              vectorOf listSize $ genTree varList childShare
                        in case i of
                                 0 -> leaves varList
                                 x -> oneof
                                   [ leaves varList
                                   , mkUPT . ImportUPF <$> genImportName
                                   , (\m a -> mkUPT (ImportQualifiedUPF m a)) <$> genImportName <*> genImportName
                                   , mkUPT . UnprocessedParsedTermH . HashF . wrap <$> recur (i - 1)
                                   , mkUPT . UnprocessedParsedTermH . HLeftF . wrap <$> recur (i - 1)
                                   , mkUPT . UnprocessedParsedTermH . HRightF . wrap <$> recur (i - 1)
                                   , mkUPT . UnprocessedParsedTermH . HTraceF . wrap <$> recur (i - 1)
                                   , elements lambdaTerms >>= \var -> mkUPT . UnprocessedParsedTermL . LamF (locatedName UnknownLoc var) . wrap <$> genTree (var : varList) (i - 1)
                                   , (\a b c -> mkUPT (UnprocessedParsedTermH (ITEF (wrap a) (wrap b) (wrap c)))) <$> recur third <*> recur third <*> recur third
                                   , (\a b c -> mkUPT (UnprocessedParsedTermH (RecursionF (wrap a) (wrap b) (wrap c)))) <$> recur third <*> recur third <*> recur third
                                   , mkUPT . ListUPF . fmap wrap <$> childList
                                   , do { listSize <- choose (2, max i 2)
                                        ; let childShare = div i listSize
                                              makeList [] = pure []
                                              makeList (v:vl) = do
                                                 newTree <- genTree (v:varList) childShare
                                                 ((locatedName UnknownLoc v, wrap newTree) :) <$> makeList vl
                                        ; vars <- take listSize <$> identifierList
                                        ; childList' <- makeList vars
                                        ; let (binds, lastBind) = (init childList', last childList')
                                        ; pure $ mkUPT (LetUPF binds (snd lastBind))
                                        }
                                   , (\a b -> mkUPT (UnprocessedParsedTermB (PairSF (wrap a) (wrap b)))) <$> recur half <*> recur half
                                   , (\a b -> mkUPT (UnprocessedParsedTermL (AppF (wrap a) (wrap b)))) <$> recur half <*> recur half
                                   ]
  shrink x = case unUnprocessedParsedTerm x of
      Fix (StringUPF s) -> case s of
        [] -> []
        _  -> [UnprocessedParsedTerm . Fix . StringUPF $ tail s]
      Fix (IntUPF i) -> case i of
        0 -> []
        n -> [UnprocessedParsedTerm . Fix . IntUPF $ n - 1]
      Fix (UnprocessedParsedTermH (ChurchF i)) -> case i of
        0 -> []
        n -> [UnprocessedParsedTerm . Fix . UnprocessedParsedTermH . ChurchF $ n - 1]
      Fix (UnprocessedParsedTermH (RecursionF t r b)) ->
        let w = UnprocessedParsedTerm
            t' = w t; r' = w r; b' = w b
            mk nt nr nb = UnprocessedParsedTerm . Fix $ UnprocessedParsedTermH (RecursionF (unUnprocessedParsedTerm nt) (unUnprocessedParsedTerm nr) (unUnprocessedParsedTerm nb))
        in t' : r' : b' : [mk nt nr nb | (nt, nr, nb) <- shrink (t', r', b')]
      Fix (UnprocessedParsedTermL (VarF _)) -> []
      Fix (UnprocessedParsedTermH (HashF x')) ->
        let x'' = UnprocessedParsedTerm x'
            mk y = UnprocessedParsedTerm . Fix . UnprocessedParsedTermH . HashF $ unUnprocessedParsedTerm y
        in x'' : fmap mk (shrink x'')
      Fix (UnprocessedParsedTermH (HLeftF x')) ->
        let x'' = UnprocessedParsedTerm x'
            mk y = UnprocessedParsedTerm . Fix . UnprocessedParsedTermH . HLeftF $ unUnprocessedParsedTerm y
        in x'' : fmap mk (shrink x'')
      Fix (UnprocessedParsedTermH (HRightF x')) ->
        let x'' = UnprocessedParsedTerm x'
            mk y = UnprocessedParsedTerm . Fix . UnprocessedParsedTermH . HRightF $ unUnprocessedParsedTerm y
        in x'' : fmap mk (shrink x'')
      Fix (UnprocessedParsedTermH (HTraceF x')) ->
        let x'' = UnprocessedParsedTerm x'
            mk y = UnprocessedParsedTerm . Fix . UnprocessedParsedTermH . HTraceF $ unUnprocessedParsedTerm y
        in x'' : fmap mk (shrink x'')
      Fix (UnprocessedParsedTermL (LamF v x')) ->
        let x'' = UnprocessedParsedTerm x'
            mk y = UnprocessedParsedTerm . Fix . UnprocessedParsedTermL . LamF v $ unUnprocessedParsedTerm y
        in x'' : fmap mk (shrink x'')
      Fix (UnprocessedParsedTermH (ITEF i' t' e')) ->
        let [i'', t'', e''] = fmap UnprocessedParsedTerm [i', t', e']
            mk ni nt ne = UnprocessedParsedTerm . Fix . UnprocessedParsedTermH $ ITEF (unUnprocessedParsedTerm ni) (unUnprocessedParsedTerm nt) (unUnprocessedParsedTerm ne)
        in i'' : t'' : e'' : [mk ni nt ne | (ni, nt, ne) <- shrink (i'', t'', e'')]
      Fix (ListUPF l) ->
        let l' = fmap UnprocessedParsedTerm l
            mkList items = UnprocessedParsedTerm . Fix . ListUPF $ fmap unUnprocessedParsedTerm items
        in case l' of
          []  -> []
          [e] -> if null $ shrink e then [e] else e : fmap (mkList . pure) (shrink e)
          _   -> head l' : mkList (tail l') : fmap (mkList . shrink) l'
    {-
      LetUP l i -> i : case l of -- TODO make this do proper, full enumeration
        [(v,e)] -> if null $ shrink e then [e] else e : map (flip LetUP i . pure . (v,)) (shrink e) <> (map (LetUP l) (shrink i))
        _ -> let shrinkBinding (n, v) = map (n,) $ shrink v
            in snd (head l) : LetUP (tail l) i : map (flip LetUP i . second shrink) l
  -}
      Fix (LetUPF l body) ->
        let body' = UnprocessedParsedTerm body
            l' = fmap (second UnprocessedParsedTerm) l
            shrinkBinding (n, v) = (n,) <$> shrink v
            removeAt n xs = let (f,s) = splitAt n xs in (f <> tail s)
            makeOptions f n xs = let (pa,c:pz) = splitAt n xs in ((pa ++) . (:pz) <$> f c)
            mkLet binds b = UnprocessedParsedTerm . Fix $ LetUPF (fmap (second unUnprocessedParsedTerm) binds) (unUnprocessedParsedTerm b)
            lessBindings = if length l' > 1
              then [mkLet (removeAt n l') body' | n <- [0..length l' - 1]]
              else []
        in body' : (lessBindings <> concat [(`mkLet` body') <$> makeOptions shrinkBinding n l' | n <- [0..length l' - 1]])
      Fix (UnprocessedParsedTermB (PairSF a b)) ->
        let a' = UnprocessedParsedTerm a; b' = UnprocessedParsedTerm b
            mk na nb = UnprocessedParsedTerm . Fix . UnprocessedParsedTermB $ PairSF (unUnprocessedParsedTerm na) (unUnprocessedParsedTerm nb)
        in a' : b' : [mk na nb | (na, nb) <- shrink (a', b')]
      Fix (UnprocessedParsedTermL (AppF f i)) ->
        let f' = UnprocessedParsedTerm f; i' = UnprocessedParsedTerm i
            mk nf ni = UnprocessedParsedTerm . Fix . UnprocessedParsedTermL $ AppF (unUnprocessedParsedTerm nf) (unUnprocessedParsedTerm ni)
        in f' : i' : [mk nf ni | (nf, ni) <- shrink (f', i')]
      _ -> []

instance Arbitrary Term1 where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen Term1
    leaves varList =
      oneof $
          (if not (null varList) then (((UnknownLoc :<) . ParserTermL . VarF <$> elements varList) :) else id)
          [ pure $ UnknownLoc :< ParserTermB ZeroSF
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
                                   , (UnknownLoc :<) . ParserTermH . HashF <$> recur (i - 1)
                                   , (UnknownLoc :<) . ParserTermH . HLeftF <$> recur (i - 1)
                                   , (UnknownLoc :<) . ParserTermH . HRightF <$> recur (i - 1)
                                   , (UnknownLoc :<) . ParserTermH . HTraceF <$> recur (i - 1)
                                   , elements lambdaTerms >>= \var -> (UnknownLoc :<) . ParserTermL . LamF (Open var) <$> genTree (var : varList) (i - 1)
                                   , (\a b c -> UnknownLoc :< ParserTermH (ITEF a b c)) <$> recur third <*> recur third <*> recur third
                                   , (\a b c -> UnknownLoc :< ParserTermH (RecursionF a b c)) <$> recur third <*> recur third <*> recur third
                                   , (\a b -> UnknownLoc :< ParserTermB (PairSF a b)) <$> recur half <*> recur half
                                   , (\a b -> UnknownLoc :< ParserTermL (AppF a b)) <$> recur half <*> recur half
                                   ]
  shrink = \case
    _ :< ParserTermB ZeroSF -> []
    anno :< ParserTermH (RecursionF t r b) -> t : r : b : [anno :< ParserTermH (RecursionF nt nr nb) | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< ParserTermL (VarF _) -> []
    anno :< ParserTermH (HashF x) -> x : fmap ((anno :<) . ParserTermH . HashF) (shrink x)
    anno :< ParserTermH (HLeftF x) -> x : fmap ((anno :<) . ParserTermH . HLeftF) (shrink x)
    anno :< ParserTermH (HRightF x) -> x : fmap ((anno :<) . ParserTermH . HRightF) (shrink x)
    anno :< ParserTermH (HTraceF x) -> x : fmap ((anno :<) . ParserTermH . HTraceF) (shrink x)
    anno :< ParserTermL (LamF v x) -> x : fmap ((anno :<) . ParserTermL . LamF v) (shrink x)
    anno :< ParserTermH (ITEF i t e) -> i : t : e : [anno :< ParserTermH (ITEF ni nt ne) | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< ParserTermB (PairSF a b) -> a : b : [anno :< ParserTermB (PairSF na nb) | (na, nb) <- shrink (a,b)]
    anno :< ParserTermL (AppF f i) -> f : i : [anno :< ParserTermL (AppF nf ni) | (nf, ni) <- shrink (f,i)]

instance Arbitrary Term2 where
  arbitrary = do
    term1 <- arbitrary :: Gen Term1
    let term2 = case debruijinize term1 of
                  Left str -> error $ "Non valid `Term1` generated from `arbitrarry :: Gen Term1`: "
                                        <> show term1
                                        <> " With error message: "
                                        <> shre str
                  Right t2 -> t2
        shre :: ResolverError -> String
        shre = show
    pure term2
  shrink = \case
    _ :< ParserTermB ZeroSF -> []
    anno :< ParserTermH (RecursionF t r b) -> t : r : b : [anno :< ParserTermH (RecursionF nt nr nb) | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< ParserTermL (VarF _) -> []
    anno :< ParserTermH (HashF x) -> x : fmap ((anno :<) . ParserTermH . HashF) (shrink x)
    anno :< ParserTermH (HLeftF x) -> x : fmap ((anno :<) . ParserTermH . HLeftF) (shrink x)
    anno :< ParserTermH (HRightF x) -> x : fmap ((anno :<) . ParserTermH . HRightF) (shrink x)
    anno :< ParserTermH (HTraceF x) -> x : fmap ((anno :<) . ParserTermH . HTraceF) (shrink x)
    anno :< ParserTermL (LamF v x) -> x : fmap ((anno :<) . ParserTermL . LamF v) (shrink x)
    anno :< ParserTermH (ITEF i t e) -> i : t : e : [anno :< ParserTermH (ITEF ni nt ne) | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< ParserTermB (PairSF a b) -> a : b : [anno :< ParserTermB (PairSF na nb) | (na, nb) <- shrink (a,b)]
    anno :< ParserTermL (AppF f i) -> f : i : [anno :< ParserTermL (AppF nf ni) | (nf, ni) <- shrink (f,i)]
