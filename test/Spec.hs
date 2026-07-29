{-# LANGUAGE CApiFFI #-}
module Main where

import Control.Applicative (liftA2)
import Control.Monad.IO.Class
import Control.Monad.Reader (Reader, runReader)
import qualified Control.Monad.State as State
import Data.Bifunctor
import Data.Char
import qualified Data.DList as DList
import Data.List (partition)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import PrettyPrint
import System.Exit
import System.IO
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Decompiler
import Telomare.Eval
import Telomare.Parser
import Telomare.Possible (SizingSettings (SizingSettings), appB, deferB)
import Telomare.Resolver
import Telomare.RunTime
import Telomare.TypeChecker
import Test.Hspec
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck

-- Common datatypes for generating Telomare AST.
import Common
import Data.Functor.Foldable (Corecursive (..))

toChurch :: Int -> Term3
toChurch x =
  let inner :: Int -> Term3Builder Term3
      inner 0 = pure (LeftB EnvB)
      inner a = appS (pure (LeftB $ RightB EnvB)) (inner (a - 1))
  in buildTerm $ fmap (`PairB` ZeroB) (lamS (inner x) >>= deferS)

-- recursively finds shrink matching invariant, ordered simplest to most complex
shrinkComplexCase :: Arbitrary a => (a -> Bool) -> [a] -> [a]
shrinkComplexCase test a =
  let shrinksWithNextLevel = fmap (\x -> (x, filter test $ shrink x)) a
      (recurseable, nonRecursable) = partition (not . null . snd) shrinksWithNextLevel
  in (shrinkComplexCase test (concatMap snd recurseable) <> fmap fst nonRecursable)

three_succ = buildTerm $ lamS (pure (PairB (varB 0) ZeroB)) >>= \il -> appS (appS (pure (toChurch 3)) (pure il)) (pure ZeroB)

one_succ = buildTerm $ lamS (pure (PairB (varB 0) ZeroB)) >>= \il -> appS (appS (pure (toChurch 1)) (pure il)) (pure ZeroB)

two_succ = buildTerm $ lamS (pure (PairB (varB 0) ZeroB)) >>= \il -> appS (appS (pure (toChurch 2)) (pure il)) (pure ZeroB)

church_type :: StuckExpr
church_type = PairB (PairB ZeroB ZeroB) (PairB ZeroB ZeroB)

c2d = buildTerm . lamS $ lamS (pure (PairB (varB 0) ZeroB)) >>= \il -> appS (appS (pure (varB 0)) (pure il)) (pure ZeroB)

test_toChurch = buildTerm $ lamS (pure (PairB (varB 0) ZeroB)) >>= \il -> appS (appS (pure (toChurch 2)) (pure il)) (pure ZeroB)

map_ =
  let layer = (buildTerm . lamS . lamS . lamS $ (do
                a <- appS (pure (varB 1)) (pure (LeftB $ varB 0))
                b <- appS (appS (pure (varB 2)) (pure (varB 1))) (pure (RightB $ varB 0))
                pure $ iteB_ (varB 0) (PairB a b) ZeroB))
      base = (buildTerm . lamS . lamS . pure $ LeftB (PairB ZeroB EnvB))
  in buildTerm $ appS (appS (pure (toChurch 255)) (pure layer)) (pure base)

foldr_ =
  let layer = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (pure (varB 2)) (pure (LeftB $ varB 0))) (pure (varB 1))
                b <- appS (appS (appS (pure (varB 3)) (pure (varB 2))) (pure a)) (pure (RightB $ varB 0))
                pure $ iteB_ (varB 0) b (varB 1)))
      base = (buildTerm . lamS . lamS . lamS . pure $ ZeroB)
  in buildTerm $ appS (appS (pure (toChurch 255)) (pure layer)) (pure base)

zipWith_ =
  let layer = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (pure (varB 2)) (pure (LeftB $ varB 1))) (pure (LeftB $ varB 0))
                b <- appS (appS (appS (pure (varB 3)) (pure (varB 2))) (pure (RightB $ varB 1))) (pure (RightB $ varB 0))
                pure $ iteB_ (varB 1) (iteB_ (varB 0) (PairB a b) ZeroB) ZeroB))
      base = (buildTerm . lamS . lamS . lamS . pure $ ZeroB)
  in buildTerm $ appS (appS (pure (toChurch 255)) (pure layer)) (pure base)

d2c recur =
  let layer = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (appS (pure (varB 3)) (pure (LeftB $ varB 2))) (pure (varB 1))) (pure (varB 0))
                b <- appS (pure (varB 1)) (pure a)
                pure $ iteB_ (varB 2) b (varB 0)))
      base = (buildTerm . lamS . lamS . lamS . pure $ varB 0)
  in buildTerm $ do
       wrapLam <- lamS $ appS (appS (pure (varB 0)) (pure layer)) (pure base)
       appS (pure wrapLam) (pure (toChurch recur))

d_equals_one = buildTerm . lamS . pure $ iteB_ (varB 0) (iteB_ (LeftB (varB 0)) ZeroB (i2B 1)) ZeroB

d_to_equality = buildTerm . lamS . lamS $ (do
  innerLam <- lamS . pure $ LeftB (varB 0)
  a <- appS (appS (appS (pure (d2c 255)) (pure (LeftB $ varB 1))) (pure innerLam)) (pure (varB 0))
  b <- appS (pure d_equals_one) (pure a)
  pure $ iteB_ (varB 1) b (iteB_ (varB 0) ZeroB (i2B 1)))

list_equality = buildTerm $ do
  and_ <- lamS . lamS . pure $ iteB_ (varB 1) (varB 0) ZeroB
  pairs_equal <- appS (appS (appS (pure zipWith_) (pure d_to_equality)) (pure (varB 0))) (pure (varB 1))
  ll1 <- appS (pure list_length) (pure (varB 1))
  ll0 <- appS (pure list_length) (pure (varB 0))
  length_equal <- appS (appS (pure d_to_equality) (pure ll1)) (pure ll0)
  folded <- appS (appS (appS (pure foldr_) (pure and_)) (pure (i2B 1))) (pure (PairB length_equal pairs_equal))
  lamS . lamS . pure $ folded

list_length = buildTerm $ do
  innerLam <- lamS . lamS . pure $ PairB (varB 0) ZeroB
  lamS $ appS (appS (appS (pure foldr_) (pure innerLam)) (pure ZeroB)) (pure (varB 0))

plus_ :: Term3 -> Term3 -> Term3
plus_ x y =
  let plus = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (pure (varB 2)) (pure (varB 1))) (pure (varB 0))
                appS (appS (pure (varB 3)) (pure (varB 1))) (pure a)))
  in buildTerm $ appS (appS (pure plus) (pure x)) (pure y)

d_plus = buildTerm . lamS . lamS $ (do
  a <- appS (pure (d2c 255)) (pure (varB 1))
  b <- appS (pure (d2c 255)) (pure (varB 0))
  appS (pure c2d) (pure (plus_ a b)))

d_plus2 = buildTerm . lamS . lamS $ (do
  a <- appS (pure (d2c 6)) (pure (varB 1))
  b <- appS (pure (d2c 6)) (pure (varB 0))
  appS (pure c2d) (pure (plus_ a b)))

d_plus3 = buildTerm . lamS $ (do
  a <- appS (pure (d2c 6)) (pure (varB 0))
  appS (pure c2d) (pure (plus_ (toChurch 2) a)))

d2c_test =
  let layer = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (appS (pure (varB 3)) (pure (LeftB $ varB 2))) (pure (varB 1))) (pure (varB 0))
                b <- appS (pure (varB 1)) (pure a)
                pure $ iteB_ (varB 2) b (varB 0)))
      base = (buildTerm . lamS . lamS . lamS . pure $ varB 0)
  in buildTerm $ do
       s_d2c <- appS (appS (pure (toChurch 3)) (pure layer)) (pure base)
       succLam <- lamS . pure $ PairB (varB 0) ZeroB
       appS (appS (appS (pure s_d2c) (pure (i2B 2))) (pure succLam)) (pure ZeroB)

d2c2_test :: Term3
d2c2_test = iteB_ ZeroB (LeftB (i2B 1)) (LeftB (i2B 2))

c2d_test = buildTerm $ appS (pure c2d) (pure (toChurch 2))
c2d_test2 = buildTerm $ do
  innerLam <- lamS . pure $ PairB (varB 0) ZeroB
  outerLam <- lamS $ appS (appS (pure (varB 0)) (pure innerLam)) (pure ZeroB)
  appS (pure outerLam) (pure (toChurch 2))
c2d_test3 = buildTerm $ do
  bodyLam <- lamS . pure $ PairB (varB 0) ZeroB
  outerLam <- lamS $ appS (pure (varB 0)) (pure ZeroB)
  appS (pure outerLam) (pure bodyLam)

double_app :: Term3
double_app = buildTerm $ do
  inner <- lamS . lamS . pure $ PairB (varB 0) (varB 1)
  appS (appS (pure inner) (pure ZeroB)) (pure ZeroB)

test_plus0 = buildTerm $ do { a <- appS (pure (d2c 255)) (pure ZeroB); appS (pure c2d) (pure (plus_ (toChurch 3) a)) }
test_plus1 = buildTerm $ do { a <- appS (pure (d2c 255)) (pure (i2B 1)); appS (pure c2d) (pure (plus_ (toChurch 3) a)) }
test_plus254 = buildTerm $ do { a <- appS (pure (d2c 255)) (pure (i2B 254)); appS (pure c2d) (pure (plus_ (toChurch 3) a)) }
test_plus255 = buildTerm $ do { a <- appS (pure (d2c 255)) (pure (i2B 255)); appS (pure c2d) (pure (plus_ (toChurch 3) a)) }
test_plus256 = buildTerm $ do { a <- appS (pure (d2c 255)) (pure (i2B 256)); appS (pure c2d) (pure (plus_ (toChurch 3) a)) }

one_plus_one =
  let plus = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (pure (varB 2)) (pure (varB 1))) (pure (varB 0))
                appS (appS (pure (varB 3)) (pure (varB 1))) (pure a)))
  in buildTerm $ do
       a <- appS (appS (pure plus) (pure (toChurch 1))) (pure (toChurch 1))
       appS (pure c2d) (pure a)

times_two =
  let times_app = (buildTerm . lamS . lamS $ (do
                    a <- appS (pure (varB 1)) (pure (varB 0))
                    appS (pure (toChurch 2)) (pure a)))
  in buildTerm $ do
       a <- appS (pure times_app) (pure (toChurch 3))
       appS (pure c2d) (pure a)

times_three =
  let times_app = (buildTerm . lamS . lamS $ (do
                    a <- appS (pure (toChurch 3)) (pure (varB 0))
                    appS (pure (varB 1)) (pure a)))
  in buildTerm $ do
       a <- appS (pure times_app) (pure (toChurch 2))
       appS (pure c2d) (pure a)

times_wip =
  let times_app = (buildTerm . lamS . lamS $ (do
                    a <- appS (pure (toChurch 3)) (pure (varB 0))
                    appS (pure (varB 1)) (pure a)))
  in buildTerm $ appS (pure c2d) (pure (toChurch 6))

function_argument :: Term3
function_argument = buildTerm $ do
  bodyLam <- lamS . pure $ PairB ZeroB (varB 0)
  outerLam <- lamS $ appS (pure (varB 0)) (pure ZeroB)
  appS (pure outerLam) (pure bodyLam)

-- m f (n f x)
-- app (app m f) (app (app n f) x)
three_plus_two =
  let plus = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (appS (pure (varB 2)) (pure (varB 1))) (pure (varB 0))
                appS (appS (pure (varB 3)) (pure (varB 1))) (pure a)))
  in buildTerm $ do
       a <- appS (appS (pure plus) (pure (toChurch 3))) (pure (toChurch 2))
       appS (pure c2d) (pure a)

-- (m (n f)) x
-- app (app m (app n f)) x
three_times_two =
  let succ = (buildTerm . lamS . pure $ PairB (varB 0) ZeroB)
      times = (buildTerm . lamS . lamS . lamS . lamS $ (do
                a <- appS (pure (varB 2)) (pure (varB 1))
                appS (appS (pure (varB 3)) (pure a)) (pure (varB 0))))
  in buildTerm $ appS (appS (appS (appS (pure times) (pure (toChurch 3))) (pure (toChurch 2))) (pure succ)) (pure ZeroB)

-- m n
-- app (app (app (m n)) f) x
three_pow_two =
  let succ = (buildTerm . lamS . pure $ PairB (varB 0) ZeroB)
      pow = (buildTerm . lamS . lamS . lamS . lamS $ (do
              a <- appS (appS (pure (varB 3)) (pure (varB 2))) (pure (varB 1))
              appS (pure a) (pure (varB 0))))
  in buildTerm $ appS (appS (appS (appS (pure pow) (pure (toChurch 2))) (pure (toChurch 3))) (pure succ)) (pure ZeroB)

-- validate termination checking
inf_pairs = buildTerm $ do
  let firstArg = LeftB EnvB
  recur <- deferS (PairB ZeroB (SetEnvB (PairB firstArg EnvB)))
  pure $ SetEnvB (PairB recur (PairB recur ZeroB))

-- unbound type errors should be allowed for purposes of testing runtime
allowedTypeCheck :: Maybe TypeCheckError -> Bool
allowedTypeCheck Nothing                = True
allowedTypeCheck (Just (UnboundType _)) = True
allowedTypeCheck _                      = False

testEval :: CompiledExpr -> IO StuckExpr
testEval expr = case eval (SetEnvB (PairB (deferB (toEnum 0) expr) ZeroB)) of
  Right x -> case toTelomare x of
    Just x' -> pure x'
    _       -> error $ "testEval failed to convert:\n" <> prettyPrint x
  Left z -> error $ "testEval unexpected: " <> show z

unitTest :: String -> String -> Term3 -> Spec
unitTest name expected iexpr = it name $ if allowedTypeCheck (typeCheck (embed ZeroTypeP) iexpr)
  then case compileUnitTest iexpr of
    Left e  -> expectationFailure (concat [name, " failed to compile: ", show e])
    Right compiled -> do
      result <- show . PrettyStuckExpr <$> testEval compiled
      result `shouldBe` expected
  else expectationFailure ( concat [name, " failed typecheck: ", show (typeCheck (embed ZeroTypeP) iexpr)])

unitTestRefinement :: String -> Bool -> BasicExpr -> Spec
unitTestRefinement name shouldSucceed iexpr = it name $
  expectationFailure (name <> ": unitTestRefinement not yet updated after refactor")

unitTestQC :: Testable p => String -> Int -> p -> Spec
unitTestQC name times = modifyMaxSuccess (const times) . it name . property

churchType = ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType)

quickcheckDataTypedCorrectlyTypeChecks :: DataTypedIExpr -> Bool
quickcheckDataTypedCorrectlyTypeChecks (IExprWrapper x) = not . null $ inferType (fromTelomare x)


testRecur = concat
  [ "main = let layer = \\recur x -> recur (x, 0)"
  , "\n"
  , "       in $3 layer (\\x -> x) 0"
  ]

-- testSBV'' = do
--   r <- runIO testSBV'
--   runIO $ if r == 4
--     then pure ()
--     else expectationFailure $ "testSBV failed, got result " <> show r
--   -- assertEqual "testing SBV" r 3

unitTests_ parse = do
  let unitTestType = unitTestType' (parse False)
      unitTest2 = unitTest2' (parse True)
      unitTestStaticChecks = unitTestStaticChecks' (parse True)
      buildMainTest s = case fmap (compileMain' (SizingSettings 255 True)) (parse True s) of
        Right (Right g) -> let eval = funWrap g appB
                           in pure $ \s i e -> it ("main input " <> i) $ eval (Just (i, s)) `shouldBe` e
        z -> pure $ \s i e -> runIO . expectationFailure $ "failed to compile main:\n" <> show s <> "\nbecause:\n" <> show z
      -- normalMainType = embed $ PairTypeP (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) (embed ZeroTypeP)
      -- decompileExample = IExprWrapper (SetEnv (SetEnv (SetEnv (Pair (Defer (Pair (Defer (Pair (Defer Zero) Env)) Env)) Zero))))
  -- describe "unitTest2" $ unitTestType "main = succ 0" (ArrTypeP ZeroTypeP ZeroTypeP) isInconsistentType
  describe "type checker" $ do
    {-
    unitTestType "main = \\x -> (x,0)" normalMainType (== Nothing)
    unitTestType "main = \\x -> (x,0)" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = succ 0" (embed ZeroTypeP) (== Nothing)
-}
    unitTestType "main = succ 0" (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) isInconsistentType
  {-
    unitTestType "main = or 0" normalMainType (== Nothing)
    unitTestType "main = or 0" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = or succ" (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) isInconsistentType
    unitTestType "main = 0 succ" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = 0 0" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = (if 0 then (\\x -> (x,0)) else (\\x -> (x,1))) 0" (embed ZeroTypeP) isRecursiveType
    unitTestType "main = (\\x y -> x y x) (\\y x -> y (x y x))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> y (x x y)) (\\x y -> y ( x x y))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> y (\\z -> x x y z)) (\\x y -> y (\\z -> x x y z))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f x -> f (\\v -> x x v) (\\x -> f (\\v -> x x v)))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> f 0) (\\g -> (g,0))" (embed ZeroTypeP) (== Nothing)
    unitTestType "main : (\\x -> if x then \"fail\" else 0) = 0" (embed ZeroTypeP) (== Nothing)
    -- unitTestType "main = ? (\\r l -> if l then r (left l) else 0) (\\l -> 0) 2" ZeroTypeP (== Nothing)
    unitTestType "main = {id,\\r l -> r (left l),id} 2" (embed ZeroTypeP) (== Nothing)
    unitTestType2
      (buildTerm $ do
        d1 <- deferS (SetEnvB (PairB EnvB EnvB))
        d2 <- deferS EnvB
        pure $ SetEnvB (PairB (SetEnvB (PairB d1 d2)) ZeroB)
      )
      (embed ZeroTypeP) isRecursiveType
    unitTestType2 inf_pairs (embed ZeroTypeP) isRecursiveType
-}
  {- TODO uncomment when type checker is fixed
    unitTestType "main = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> (\\x -> x x) (\\x -> f (x x)))"
      normalMainType (/= Nothing) -- isRecursiveType
-}

c2dApp = "main = (c2dG $4 3) $2 succ 0"

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _                              = False

isRecursiveType (Just (RecursiveType _)) = True
isRecursiveType _                        = False

unitTestTypeP :: StuckExpr -> Either TypeCheckError PartialType -> IO Bool
unitTestTypeP iexpr expected = if inferType (fromTelomare iexpr) == expected
  then pure True
  else do
  putStrLn $ concat ["type inference error ", show iexpr, " expected ", show expected
                    , " result ", show (inferType $ fromTelomare iexpr)
                    ]
  pure False

debugMark s = hPutStrLn stderr s >> pure True

--unitTests :: (String -> String -> Spec) -> (String -> PartialType -> (Maybe TypeCheckError -> Bool) -> Spec) -> Spec
unitTests parse = do
  let unitTestType = unitTestType' (parse False)
      unitTest2 = unitTest2' (parse True)
      unitTestStaticChecks = unitTestStaticChecks' (parse True)
      buildMainTest s = case fmap (compileMain' (SizingSettings 255 True)) (parse True s) of
        Right (Right g) -> let eval = funWrap g appB
                           in pure $ \s i e -> it ("main input " <> i) $ eval (Just (i, s)) `shouldBe` e
        z -> pure $ \s i e -> runIO . expectationFailure $ "failed to compile main:\n" <> show s <> "\nbecause:\n" <> show z
      normalMainType = embed $ PairTypeP (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) (embed ZeroTypeP)
  describe "type checker" $ do
    unitTestType "main = \\x -> (x,0)" normalMainType (== Nothing)
    unitTestType "main = \\x -> (x,0)" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = succ 0" (embed ZeroTypeP) (== Nothing)
    unitTestType "main = succ 0" (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) isInconsistentType
    unitTestType "main = or 0" normalMainType (== Nothing)
    unitTestType "main = or 0" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = or succ" (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) isInconsistentType
    unitTestType "main = 0 succ" (embed ZeroTypeP) isInconsistentType
    unitTestType "main = 0 0" (embed ZeroTypeP) isInconsistentType
  {- TODO uncomment when type checker is fixed
    unitTestType "main = (if 0 then (\\x -> (x,0)) else (\\x -> (x,1))) 0" (embed ZeroTypeP) isRecursiveType
    unitTestType "main = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> (\\x -> x x) (\\x -> f (x x)))"
      normalMainType (/= Nothing) -- isRecursiveType
-}
    unitTestType "main = (\\x y -> x y x) (\\y x -> y (x y x))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> y (x x y)) (\\x y -> y ( x x y))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> y (\\z -> x x y z)) (\\x y -> y (\\z -> x x y z))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f x -> f (\\v -> x x v) (\\x -> f (\\v -> x x v)))"
      normalMainType (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> f 0) (\\g -> (g,0))" (embed ZeroTypeP) (== Nothing)
    unitTestType "main : (\\x -> if x then \"fail\" else 0) = 0" (embed ZeroTypeP) (== Nothing)
    -- unitTestType "main = ? (\\r l -> if l then r (left l) else 0) (\\l -> 0) 2" ZeroTypeP (== Nothing)
    unitTestType "main = {id,\\r l -> r (left l),id} 2" (embed ZeroTypeP) (== Nothing)
    unitTestType2
      (buildTerm $ do
        d1 <- deferS (SetEnvB (PairB EnvB EnvB))
        d2 <- deferS EnvB
        pure $ SetEnvB (PairB (SetEnvB (PairB d1 d2)) ZeroB)
      )
      (embed ZeroTypeP) isRecursiveType
    unitTestType2 inf_pairs (embed ZeroTypeP) isRecursiveType
  describe "unitTest" $ do
    unitTest "ite" "2" (iteB_ (i2B 1) (i2B 2) (i2B 3))
    unitTest "c2d" "2" c2d_test
    unitTest "c2d2" "2" c2d_test2
    unitTest "c2d3" "1" c2d_test3
    unitTest "oneplusone" "2" one_plus_one
    unitTest "church 3+2" "5" three_plus_two
    unitTest "3*2" "6" three_times_two
    unitTest "3^2" "9" three_pow_two
    unitTest "test_tochurch" "2" test_toChurch
    unitTest "three" "3" three_succ
    unitTest "data 3+5" "8" . buildTerm $ appS (appS (pure d_plus) (pure (i2B 3))) (pure (i2B 5))
    unitTest "foldr" "13" . buildTerm $ appS (appS (appS (pure foldr_) (pure d_plus)) (pure (i2B 1))) (pure (foldr (PairB . i2B) ZeroB [2,4,6]))
    unitTest "listlength0" "0" . buildTerm $ appS (pure list_length) (pure ZeroB)
    unitTest "listlength3" "3" . buildTerm $ appS (pure list_length) (pure (foldr (PairB . i2B) ZeroB [1,2,3]))
    unitTest "zipwith" "((4,1),((5,1),((6,2),0)))" . buildTerm $ appS (appS (appS (pure zipWith_) (pure (buildTerm . lamS . lamS . pure $ PairB (varB 1) (varB 0))))
                               (pure (foldr (PairB . i2B) ZeroB [4,5,6])))
                         (pure (foldr (PairB . i2B) ZeroB [1,1,2,3]))
    unitTest "listequal1" "1" . buildTerm $ appS (appS (pure list_equality) (pure (s2b "hey"))) (pure (s2b "hey"))
    unitTest "listequal0" "0" . buildTerm $ appS (appS (pure list_equality) (pure (s2b "hey"))) (pure (s2b "he"))
    unitTest "listequal00" "0" . buildTerm $ appS (appS (pure list_equality) (pure (s2b "hey"))) (pure (s2b "hel"))
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
    unitTest "map" "(2,(3,5))" . buildTerm $ appS (appS (pure map_) (pure (buildTerm . lamS . pure $ PairB (varB 0) ZeroB)))
                                                  (pure (foldr (PairB . i2B) ZeroB [1,2,3]))

  describe "refinement" $ do
    unitTestStaticChecks "main : (\\x -> assert (not x) \"fail\") = 1" (== Left (StaticCheckError "user abort: fail"))
    unitTestStaticChecks "main : (\\x -> assert (not (left x)) \"fail\") = 1" (not . null)
    unitTestStaticChecks "main : (\\x -> assert 1 \"fail\") = 1" (not . null)
    unitTestStaticChecks "main : (\\f -> assert (not (f 2)) \"boop\") = \\x -> left x" (== Left (StaticCheckError "user abort: boop"))
    unitTestStaticChecks "main : (\\f -> assert (not (f 2)) \"boop\") = \\x -> left (left x)" (not . null)

  describe "unitTest2" $ do
    unitTest2 "main = 0" "0"
    unitTest2 fiveApp "5"
    unitTest2 "main = plus $3 $2 succ 0" "5"
    unitTest2 "main = times $3 $2 succ 0" "6"
    unitTest2 "main = pow $3 $2 succ 0" "9"
    unitTest2 "main = d2c 3 succ 0" "3"
    -- unitTest2 "main = (d2cG $4 3) succ 0" "3"
    unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
    unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
    unitTest2 "main = dEqual 0 0" "1"
    unitTest2 "main = dEqual 1 0" "0"
    unitTest2 "main = dEqual 0 1" "0"
    unitTest2 "main = dEqual 1 1" "1"
    unitTest2 "main = dEqual 2 1" "0"
    unitTest2 "main = dEqual 1 2" "0"
    unitTest2 "main = dEqual 2 2" "1"
    unitTest2 "main = listLength []" "0"
    unitTest2 "main = listLength [1,2,3]" "3"
    unitTest2 "main = listEqual \"hey\" \"hey\"" "1"
    unitTest2 "main = listEqual \"hey\" \"he\"" "0"
    unitTest2 "main = listEqual \"hey\" \"hel\"" "0"
    unitTest2 "main = listPlus [1,2] [3,4]" "(1,(2,(3,5)))"
    unitTest2 "main = listPlus 0 [1]" "2"
    unitTest2 "main = listPlus [1] 0" "2"
    unitTest2 "main = map left [1,2]" "(0,2)" -- test "left" as a function rather than builtin requiring argument
    unitTest2 "main = concat [\"a\",\"b\",\"c\"]" "(97,(98,100))"
    unitTest2 nestedNamedFunctionsIssue "2"
    unitTest2 "main = take $0 [1,2,3]" "0"
    unitTest2 "main = take $1 [1,2,3]" "2"
    unitTest2 "main = take $5 [1,2,3]" "(1,(2,4))"
    unitTest2 "main = c2d (minus $4 $3)" "1"
    unitTest2 "main = c2d (minus $4 $4)" "0"
    unitTest2 "main = dMinus 4 3" "1"
    unitTest2 "main = dMinus 4 4" "0"
    unitTest2 "main = (if 0 then (\\x -> (x,0)) else (\\x -> ((x,0),0))) 1" "3"
    unitTest2 "main = range 2 5" "(2,(3,5))"
    unitTest2 "main = range 6 6" "0"
    unitTest2 "main = filter (\\x -> dMinus x 3) (range 1 8)"
      "(4,(5,(6,8)))"
    unitTest2 "main = (\\a b -> if 0 then a b else b) (\\b -> times $2 b) $1 succ 0" "1"
    unitTest2 "main = c2d (factorial 0)" "1"
    unitTest2 "main = c2d (factorial 4)" "24"

  describe "main function tests" $ do
    testMain <- runIO $ Strict.readFile "testchar.tel"
    unitTestMain <- buildMainTest testMain
    unitTestMain ZeroB "A" ("ascii value of first char is odd", Right ZeroB)
    unitTestMain ZeroB "B" ("ascii value of first char is even", Right ZeroB)
    testMain <- runIO $ Strict.readFile "simpleplus.tel"
    unitTestMain <- buildMainTest testMain
    unitTestMain ZeroB "0 0" ("0 plus 0 is 0", Right ZeroB)
    unitTestMain ZeroB "9 9" ("9 plus 9 is 18", Right ZeroB)
    unitTestMain ZeroB "9 a" ("runtime error:\nAborted, user abort: invalid input", Left (AbortRunTime (AbortUser $ s2b "invalid input")))


  {- TODO -- figure out why this broke
    unitTest2 "main = quicksort [4,3,7,1,2,4,6,9,8,5,7]"
      "(1,(2,(3,(4,(4,(5,(6,(7,(7,(8,10))))))))))"
-}

testExpr = concat
  [ "main = let a = 0\n"
  , "           b = 1\n"
  , "       in (a,1)\n"
  ]

fiveApp = "main = let fiveApp = $5\n" <> "       in fiveApp (\\x -> (x,0)) 0"

nestedNamedFunctionsIssue = concat
  [ "main = let bindTest = \\tlb -> let f1 = \\f -> f tlb\n"
  , "                                  f2 = \\f -> succ (f1 f)\n"
  , "                               in f2 succ\n"
  , "       in bindTest 0"
  ]


unitTest2' parse s r = it s $ case fmap compileUnitTest (parse s) of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right (Right g) -> testEval g >>= (\r2 -> if r2 == r
    then pure ()
    else expectationFailure $ concat [s, " result ", r2])
    . show . PrettyStuckExpr
  Right (Left e) -> expectationFailure $ "failed to compile: " <> show e

unitTestType' parse s t tef = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> let apt = typeCheck t g
             in if tef apt
                then pure ()
                else expectationFailure $
                      concat [s, " failed typecheck, result ", show apt]

unitTestStaticChecks' parse s c = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> let rr = findChurchSizeD UnitTestSizing g >>= runStaticChecks
              in if c rr
                then pure ()
                else do
    --putStrLn $ "grammar is " <> show g
    expectationFailure $ "static check failed with " <> show rr

unitTestType2 i t tef = it ("type check " <> show i) $
  let apt = typeCheck t i
  in if tef apt
     then pure ()
     else expectationFailure $ concat [show i, " failed typecheck, result ", show apt]

main = do
  preludeFile <- Strict.readFile "Prelude.tel"

  let
    prelude' = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    prelude :: [(String, [Either AUPT (String, AUPT)])]
    prelude = [("Prelude", Right . second unAnnotatedUPT <$> prelude')]
    parseAuxModule :: String -> (String, [Either AUPT (String, AUPT)])
    parseAuxModule str =
      case sequence ("AuxModule", parseModule ("import Prelude\n" <> str)) of
      -- case sequence ("AuxModule", parseModule str) of
        Left e    -> error $ show e
        Right pam -> second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) pam
    parse :: Bool -> String -> Either String Term3
    parse appLet str = if appLet
      then first show $ main2Term3let (parseAuxModule str:prelude) "AuxModule"
      else first show $ main2Term3 (parseAuxModule str:prelude) "AuxModule"

  hspec $ unitTests parse
