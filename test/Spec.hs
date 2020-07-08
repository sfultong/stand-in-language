{-# LANGUAGE CApiFFI #-}
module Main where

import Control.Applicative (liftA2)
import Control.Monad.IO.Class
import Debug.Trace
import Data.Bifunctor
import Data.Char
import Data.List (partition)
import Data.Monoid
import Telomare
import Telomare.Eval
import Telomare.Llvm (RunResult(..))
import Naturals
import Telomare.Parser
import Telomare.RunTime
import Telomare.TypeChecker
import Telomare.Optimizer
import Telomare.Serializer
import System.Exit
import System.IO
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import qualified System.IO.Strict as Strict

-- Common datatypes for generating Telomare AST.
import Common

-- recursively finds shrink matching invariant, ordered simplest to most complex
shrinkComplexCase :: Arbitrary a => (a -> Bool) -> [a] -> [a]
shrinkComplexCase test a =
  let shrinksWithNextLevel = map (\x -> (x, filter test $ shrink x)) a
      (recurseable, nonRecursable) = partition (not . null . snd) shrinksWithNextLevel
  in shrinkComplexCase test (concat $ map snd recurseable) ++ map fst nonRecursable

three_succ = app (app (toChurch 3) (lam (pair (varN 0) zero))) zero

one_succ = app (app (toChurch 1) (lam (pair (varN 0) zero))) zero

two_succ = app (app (toChurch 2) (lam (pair (varN 0) zero))) zero

church_type = pair (pair zero zero) (pair zero zero)

c2d = lam (app (app (varN 0) (lam (pair (varN 0) zero))) zero)

h2c i =
  let layer recurf i churchf churchbase =
        if i > 0
        then churchf $ recurf (i - 1) churchf churchbase
        -- app v1 (app (app (app v3 (pleft v2)) v1) v0)
        else churchbase
      stopf i churchf churchbase = churchbase
  in \cf cb -> layer (layer (layer (layer stopf))) i cf cb


{-
h_zipWith a b f =
  let layer recurf zipf a b =
        if a > 0
        then if b > 0
             then pair (zipf (pleft a) (pleft b)) (recurf zipf (pright a) (pright b))
             else zero
        else zero
      stopf _ _ _ = zero
  in layer (layer (layer (layer stopf))) a b f

foldr_h =
  let layer recurf f accum l =
        if not $ nil l
        then recurf f (f (pleft l) accum) (pright l)
        else accum
-}

test_toChurch = app (app (toChurch 2) (lam (pair (varN 0) zero))) zero

map_ =
  -- layer recurf f l = pair (f (pleft l)) (recurf f (pright l))
  let layer = lam (lam (lam
                            (ite (varN 0)
                            (pair
                             (app (varN 1) (pleft $ varN 0))
                             (app (app (varN 2) (varN 1))
                              (pright $ varN 0)))
                            zero
                            )))
      base = lam (lam (pleft (pair zero var)))
  in app (app (toChurch 255) layer) base

foldr_ =
  let layer = lam (lam (lam (lam
                                 (ite (varN 0)
                                 (app (app (app (varN 3) (varN 2))

                                       (app (app (varN 2) (pleft $ varN 0))
                                            (varN 1)))
                                  (pright $ varN 0))
                                 (varN 1)
                                 )
                                 )))
      base = lam (lam (lam zero)) -- var 0?
  in app (app (toChurch 255) layer) base

zipWith_ =
  let layer = lam (lam (lam (lam
                                  (ite (varN 1)
                                   (ite (varN 0)
                                    (pair
                                     (app (app (varN 2) (pleft $ varN 1))
                                      (pleft $ varN 0))
                                     (app (app (app (varN 3) (varN 2))
                                           (pright $ varN 1))
                                      (pright $ varN 0))
                                    )
                                    zero)
                                   zero)
                                 )))
      base = lam (lam (lam zero))
  in app (app (toChurch 255) layer) base

-- layer recurf i churchf churchbase
-- layer :: (zero -> baseType) -> zero -> (baseType -> baseType) -> baseType
--           -> baseType
-- converts plain data type number (0-255) to church numeral
{-
d2c recur =
  let layer = lam (lam (lam (lam (ite
                             (varN 2)
                             (app (varN 1)
                              (app (app (app (varN 3)
                                   (pleft $ varN 2))
                                   (varN 1))
                                   (varN 0)
                                  ))
                             (varN 0)
                            ))))
      base = lam (lam (lam (varN 0)))
  in app (app (toChurch recur) layer) base
-}
d2c recur =
  let layer = lam (lam (lam (lam (ite
                             (varN 2)
                             (app (varN 1)
                              (app (app (app (varN 3)
                                   (pleft $ varN 2))
                                   (varN 1))
                                   (varN 0)
                                  ))
                             (varN 0)
                            ))))
      base = lam (lam (lam (varN 0)))
  in app (lam (app (app (varN 0) layer) base)) (toChurch recur)

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = lam (ite (varN 0) (ite (pleft (varN 0)) zero (i2g 1)) zero)

d_to_equality = lam (lam (ite (varN 1)
                                          (app d_equals_one (app (app (app (d2c 255) (pleft $ varN 1)) (lam . pleft $ varN 0)) (varN 0)))
                                          (ite (varN 0) zero (i2g 1))
                                         ))

list_equality =
  let pairs_equal = app (app (app zipWith_ d_to_equality) (varN 0)) (varN 1)
      length_equal = app (app d_to_equality (app list_length (varN 1)))
                     (app list_length (varN 0))
      and_ = lam (lam (ite (varN 1) (varN 0) zero))
      folded = app (app (app foldr_ and_) (i2g 1)) (pair length_equal pairs_equal)
  in lam (lam folded)

list_length = lam (app (app (app foldr_ (lam (lam (pair (varN 0) zero))))
                                  zero)
  (varN 0))

plus_ x y =
  let succ = lam (pair (varN 0) zero)
      plus_app = app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
      plus = lam (lam (lam (lam plus_app)))
  in app (app plus x) y

d_plus = lam (lam (app c2d (plus_
                                   (app (d2c 255) (varN 1))
                                   (app (d2c 255) (varN 0))
                                   )))

d_plus2 = lam (lam (app c2d (plus_
                                   (app (d2c 6) (varN 1))
                                   (app (d2c 6) (varN 0))
                                   )))

d_plus3 = lam (app c2d (plus_
                                   (toChurch 2)
                                   (app (d2c 6) (varN 0))
                                   ))

d2c_test =
  let s_d2c = app (app (toChurch 3) layer) base
      layer = lam (lam (lam (lam (ite
                             (varN 2)
                             (app (varN 1)
                              (app (app (app (varN 3)
                                   (pleft $ varN 2))
                                   (varN 1))
                                   (varN 0)
                                  ))
                             (varN 0)
                            ))))
      base = lam (lam (lam (varN 0)))
  in app (app (app s_d2c (i2g 2)) (lam (pair (varN 0) zero))) zero

d2c2_test = ite zero (pleft (i2g 1)) (pleft (i2g 2))

c2d_test = app c2d (toChurch 2)
c2d_test2 = app (lam (app (app (varN 0) (lam (pair (varN 0) zero))) zero)) (toChurch 2)
c2d_test3 = app (lam (app (varN 0) zero)) (lam (pair (varN 0) zero))

double_app = app (app (lam (lam (pair (varN 0) (varN 1)))) zero) zero

test_plus0 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c 255) zero))
test_plus1 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c 255) (i2g 1)))
test_plus254 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c 255) (i2g 254)))
test_plus255 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c 255) (i2g 255)))
test_plus256 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c 255) (i2g 256)))

one_plus_one =
  let succ = lam (pair (varN 0) zero)
      plus_app = app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
      plus = lam (lam (lam (lam plus_app)))
  in app c2d (app (app plus (toChurch 1)) (toChurch 1))

-- m f (n f x)
-- app (app m f) (app (app n f) x)
-- app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
three_plus_two =
  let succ = lam (pair (varN 0) zero)
      plus_app = app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
      plus = lam (lam (lam (lam plus_app)))
  in app c2d (app (app plus (toChurch 3)) (toChurch 2))

-- (m (n f)) x
-- app (app m (app n f)) x
three_times_two =
  let succ = lam (pair (varN 0) zero)
      times_app = app (app (varN 3) (app (varN 2) (varN 1))) (varN 0)
      times = lam (lam (lam (lam times_app)))
  in app (app (app (app times (toChurch 3)) (toChurch 2)) succ) zero

-- m n
-- app (app (app (m n)) f) x
three_pow_two =
  let succ = lam (pair (varN 0) zero)
      pow_app = app (app (app (varN 3) (varN 2)) (varN 1)) (varN 0)
      pow = lam (lam (lam (lam pow_app)))
  in app (app (app (app pow (toChurch 2)) (toChurch 3)) succ) zero

-- unbound type errors should be allowed for purposes of testing runtime
allowedTypeCheck :: Maybe TypeCheckError -> Bool
allowedTypeCheck Nothing = True
allowedTypeCheck (Just (UnboundType _)) = True
allowedTypeCheck _ = False

testEval :: IExpr -> IO IExpr
-- testEval iexpr = optimizedEval (SetEnv (Pair (Defer deserialized) Zero))
testEval iexpr = simpleEval (SetEnv (Pair (Defer deserialized) Zero))
    where serialized   = serialize iexpr
          deserialized = unsafeDeserialize serialized

unitTest :: String -> String -> IExpr -> Spec
unitTest name expected iexpr = it name $ if allowedTypeCheck (typeCheck ZeroTypeP (fromTelomare iexpr))
  then do
    result <- (show . PrettyIExpr) <$> testEval iexpr
    result `shouldBe` expected
  else expectationFailure ( concat [name, " failed typecheck: ", show (typeCheck ZeroTypeP (fromTelomare iexpr))])

unitTestRefinement :: String -> Bool -> IExpr -> Spec
unitTestRefinement name shouldSucceed iexpr = it name $ case inferType (fromTelomare iexpr) of
  Right t -> case (pureEval iexpr, shouldSucceed) of
    (Left err, True) -> do
      expectationFailure $ concat [name, ": failed refinement type -- ", show err]
    (Right _, False) -> do
      expectationFailure $ concat [name, ": expected refinement failure, but passed"]
    _ -> pure ()
  Left err -> do
    expectationFailure $ concat ["refinement test failed typecheck: ", name, " ", show err]

{-
unitTestOptimization :: String -> IExpr -> IO Bool
unitTestOptimization name iexpr = if optimize iexpr == optimize2 iexpr
  then pure True
  else (putStrLn $ concat [name, ": optimized1 ", show $ optimize iexpr, " optimized2 "
                          , show $ optimize2 iexpr])
  >> pure False
-}
quickcheckBuiltInOptimizedDoesNotChangeEval :: UnprocessedParsedTerm -> Bool
quickcheckBuiltInOptimizedDoesNotChangeEval up =
  let
      makeTelomare f = second (toTelomare . findChurchSize) (fmap splitExpr . (>>= debruijinize []) . validateVariables id . f . addBuiltins $ up)
      iexpr :: Either String (Maybe IExpr)
      iexpr = makeTelomare id -- x. validateVariables id . optimizeBuiltinFunctions $ up)
      iexpr' = makeTelomare optimizeBuiltinFunctions -- second (toTelomare . findChurchSize) (fmap splitExpr . (>>= debruijinize []) . validateVariables id $ up)
  in
    case (iexpr, iexpr') of
       (Right (Just ie), Right (Just ie')) -> pureEval ie == pureEval ie'
       _ | iexpr == iexpr'-> True
       _ | otherwise -> False

{-
unitTestQC :: Testable p => String -> Int -> p -> Spec
unitTestQC name times p = liftIO (quickCheckWithResult stdArgs { maxSuccess = times } p) >>= \result -> case result of
  (Success _ _ _ _ _ _) -> pure ()
  x -> expectationFailure $ concat [name, " failed: ", show x]
-}
unitTestQC :: Testable p => String -> Int -> p -> Spec
unitTestQC name times p = modifyMaxSuccess (const times) . it name . property $ p


churchType = (ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType))

{-
rEvaluationIsomorphicToIEvaluation :: ZeroTypedTestIExpr -> Bool
rEvaluationIsomorphicToIEvaluation vte = case (pureEval $ getIExpr vte, pureREval $ getIExpr vte) of
  (Left _, Left _) -> True
  (a, b) | a == b -> True
  _ -> False

debugREITIE :: IExpr -> IO Bool
debugREITIE iexpr = if pureEval iexpr == pureREval iexpr
  then pure True
  else do
  putStrLn . concat $ ["ieval: ", show $ pureEval iexpr]
  putStrLn . concat $ ["reval: ", show $ pureREval iexpr]
  pure False

partiallyEvaluatedIsIsomorphicToOriginal:: ArrowTypedTestIExpr -> Bool
--partiallyEvaluatedIsIsomorphicToOriginal vte = pureREval (app (getIExpr vte) 0) == pureREval (app ())
partiallyEvaluatedIsIsomorphicToOriginal vte =
  let iexpr = getIExpr vte
      sameError (GenericRunTimeError sa _) (GenericRunTimeError sb _) = sa == sb
      -- sameError (SetEnvError _) (SetEnvError _) = True
      sameError a b = a == b
  in case (\x -> pureREval (app x Zero)) <$> eval iexpr of
  Left (RTE e) -> Left e == pureREval (app iexpr Zero)
  Right x -> case (x, pureREval (app iexpr Zero)) of
    (Left a, Left b) -> sameError a b
    (a, b) -> a == b

debugPEIITO :: IExpr -> Expectation
debugPEIITO iexpr = do
  putStrLn "regular app:"
  putStrLn $ show (app iexpr Zero)
  putStrLn "r-optimized:"
  showROptimized $ app iexpr Zero
  putStrLn "evaled:"
  putStrLn $ show (eval iexpr)
  case (\x -> pureREval (app x Zero)) <$> eval iexpr of
    Left (RTE e) ->
      expectationFailure
        (unlines
           [ concat $ ["partially evaluated error: ", show e]
           , concat $ ["regular evaluation result: ", show (pureREval (app iexpr Zero))]])
    Right x ->
      expectationFailure
        (unlines
           [ concat $ ["partially evaluated result: ", show x]
           , concat $ ["normally evaluated result: ", show (pureREval (app iexpr Zero))]])

-}

-- partiallyEvaluatedIsIsomorphicToOriginal :: ArrowTypedTestIExpr -> Bool
-- --partiallyEvaluatedIsIsomorphicToOriginal vte = pureREval (app (getIExpr vte) 0) == pureREval (app ())
-- partiallyEvaluatedIsIsomorphicToOriginal vte =
--   let iexpr = getIExpr vte
--       sameError (GenericRunTimeError sa _) (GenericRunTimeError sb _) = sa == sb
--       -- sameError (SetEnvError _) (SetEnvError _) = True
--       sameError a b = a == b
--   in case (\x -> pureREval (app x Zero)) <$> eval iexpr of
--   Left (RTE e) -> Left e == pureREval (app iexpr Zero)
--   Right x -> case (x, pureREval (app iexpr Zero)) of
--     (Left a, Left b) -> sameError a b
--     (a, b) -> a == b

-- quickcheckBuiltInOptimizedDoesNotChangeEval :: UnprocessedParsedTerm -> Bool
-- quickcheckBuiltInOptimizedDoesNotChangeEval up =
--   let iexpr = toTelomare . findChurchSize <$> fmap splitExpr . (>>= debruijinize []) . validateVariables id $ up
--   in False

testRecur = concat
  [ "main = let layer = \\recur x -> recur (x, 0)"
  , "       in $3 layer (\\x -> x) 0"
  ]

-- unitTests_ :: (String -> String -> Spec) -> (String -> PartialType -> (Maybe TypeCheckError -> Bool) -> Spec) -> Spec
unitTests_ parse = do
  let unitTestType = unitTestType' parse
      unitTest2 = unitTest2' parse
      unitTestRuntime = unitTestRuntime' parse
      unitTestSameResult = unitTestSameResult' parse
  unitTestType "main = \\x -> (x,0)" (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (== Nothing)
  unitTestType "main = \\x -> (x,0)" ZeroTypeP isInconsistentType
  unitTestType "main = succ 0" ZeroTypeP (== Nothing)
  unitTestType "main = succ 0" (ArrTypeP ZeroTypeP ZeroTypeP) isInconsistentType
  unitTestType "main = or 0" (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (== Nothing)
  unitTestType "main = or 0" ZeroTypeP isInconsistentType
  unitTestType "main = or succ" (ArrTypeP ZeroTypeP ZeroTypeP) isInconsistentType
  unitTestType "main = 0 succ" ZeroTypeP isInconsistentType
  unitTestType "main = 0 0" ZeroTypeP isInconsistentType
  unitTestType "main = (if 0 then (\\x -> (x,0)) else (\\x -> (x,1))) 0" ZeroTypeP (== Nothing)
  -- I guess this is inconsistently typed now?
  unitTestType "main = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
    (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
  unitTestType "main = (\\x y -> x y x) (\\y x -> y (x y x))"
    (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
  unitTestType "main = (\\f -> (\\x -> x x) (\\x -> f (x x)))"
    (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
  unitTestType "main = (\\x y -> y (x x y)) (\\x y -> y ( x x y))"
    (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
  unitTestType "main = (\\x y -> y (\\z -> x x y z)) (\\x y -> y (\\z -> x x y z))"
    (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
  unitTestType "main = (\\f x -> f (\\v -> x x v) (\\x -> f (\\v -> x x v)))"
    (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
  unitTestType "main = (\\f -> f 0) (\\g -> (g,0))" ZeroTypeP (== Nothing)
  unitTestType "main : (\\x -> if x then \"fail\" else 0) = 0" ZeroTypeP (== Nothing)
  {-
  unitTest2 "main = quicksort [4,3,7,1,2,4,6,9,8,5,7]"
    "(0,(2,(3,(4,(4,(5,(6,(7,(7,(8,10))))))))))"
-}
  {-
  unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
  unitTest2 "main = c2d (minus $2 $1)" "1"
  unitTest2 "main = ? (\\r x -> if x then r (left x) else 0) (\\a -> 0) 1" "0"
-}
  {-
  unitTest2 "main = $3 ($2 succ) 0" "6"
  unitTest "3*2" "6" three_times_two
  unitTest2 "main = (if 0 then (\\x -> (x,0)) else (\\x -> ((x,0),0))) 1" "3"
  unitTest2 "main = $3 succ 0" "3"
  unitTest2 "main = (d2cG $4 3) succ 0" "3"
  unitTest "oneplusone" "2" one_plus_one
  unitTest "church 3+2" "5" three_plus_two
  unitTest "3*2" "6" three_times_two
  unitTest "3^2" "9" three_pow_two
  unitTest2 "main = $3 succ 0" "3"
  unitTest "test_tochurch" "2" test_toChurch
  unitTest "three" "3" three_succ
  unitTest "data 3+5" "8" $ app (app d_plus2 (i2g 3)) (i2g 5)
  unitTest "data 2+3" "5" $ app d_plus3 (i2g 3)
  unitTest "foldr" "13" $ app (app (app foldr_ d_plus) (i2g 1)) (ints2g [2,4,6])
  unitTest "listlength0" "0" $ app list_length zero
  unitTest "listlength3" "3" $ app list_length (ints2g [1,2,3])
  unitTest "zipwith" "((4,1),((5,1),((6,2),0)))"
    $ app (app (app zipWith_ (lam (lam (pair (varN 1) (varN 0)))))
                (ints2g [4,5,6]))
          (ints2g [1,1,2,3])
  unitTest "listequal1" "1" $ app (app list_equality (s2g "hey")) (s2g "hey")
  unitTest "listequal0" "0" $ app (app list_equality (s2g "hey")) (s2g "he")
  unitTest "listequal00" "0" $ app (app list_equality (s2g "hey")) (s2g "hel")
  unitTest "map" "(2,(3,5))" $ app (app map_ (lam (pair (varN 0) zero)))
                                    (ints2g [1,2,3])
-}

c2dApp = "main = (c2dG $4 3) $2 succ 0"

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _ = False

isRecursiveType (Just (RecursiveType _)) = True
isRecursiveType _ = False

unitTestTypeP :: IExpr -> Either TypeCheckError PartialType -> IO Bool
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
  let unitTestType = unitTestType' parse
      unitTest2 = unitTest2' parse
  describe "type checker" $ do
    unitTestType "main = \\x -> (x,0)" (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (== Nothing)
    unitTestType "main = \\x -> (x,0)" ZeroTypeP isInconsistentType
    unitTestType "main = succ 0" ZeroTypeP (== Nothing)
    unitTestType "main = succ 0" (ArrTypeP ZeroTypeP ZeroTypeP) isInconsistentType
    unitTestType "main = or 0" (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (== Nothing)
    unitTestType "main = or 0" ZeroTypeP isInconsistentType
    unitTestType "main = or succ" (ArrTypeP ZeroTypeP ZeroTypeP) isInconsistentType
    unitTestType "main = 0 succ" ZeroTypeP isInconsistentType
    unitTestType "main = 0 0" ZeroTypeP isInconsistentType
    unitTestType "main = (if 0 then (\\x -> (x,0)) else (\\x -> (x,1))) 0" ZeroTypeP (== Nothing)
    -- I guess this is inconsistently typed now?
    unitTestType "main = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
      (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> x y x) (\\y x -> y (x y x))"
      (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> (\\x -> x x) (\\x -> f (x x)))"
      (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> y (x x y)) (\\x y -> y ( x x y))"
      (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\x y -> y (\\z -> x x y z)) (\\x y -> y (\\z -> x x y z))"
      (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f x -> f (\\v -> x x v) (\\x -> f (\\v -> x x v)))"
      (ArrTypeP (ArrTypeP ZeroTypeP ZeroTypeP) ZeroTypeP) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> f 0) (\\g -> (g,0))" ZeroTypeP (== Nothing)
    unitTestType "main : (\\x -> if x then \"fail\" else 0) = 0" ZeroTypeP (== Nothing)
    unitTestType2
      (setenv (pair
               (setenv (pair
                        (defer (setenv (pair env env)))
                        (defer env)
                       )
               )
               zero
              )
      )
      ZeroTypeP isRecursiveType
  -- TODO fix
  --, unitTestType "main : (\\x -> if x then \"fail\" else 0) = 1" ZeroType isRefinementFailure
  describe "unitTest" $ do
    unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
    -- unitTest "abort" "1" (pair (Abort (pair zero zero)) zero)
    unitTest "notAbort" "2" (setenv (pair (setenv (pair Abort zero)) (pair (pair zero zero) zero)))
    unitTest "c2d" "2" c2d_test
    unitTest "c2d2" "2" c2d_test2
    unitTest "c2d3" "1" c2d_test3
    unitTest "oneplusone" "2" one_plus_one
    unitTest "church 3+2" "5" three_plus_two
    unitTest "3*2" "6" three_times_two
    unitTest "3^2" "9" three_pow_two
    unitTest "test_tochurch" "2" test_toChurch
    unitTest "three" "3" three_succ
    unitTest "data 3+5" "8" $ app (app d_plus (i2g 3)) (i2g 5)
    unitTest "foldr" "13" $ app (app (app foldr_ d_plus) (i2g 1)) (ints2g [2,4,6])
    unitTest "listlength0" "0" $ app list_length zero
    unitTest "listlength3" "3" $ app list_length (ints2g [1,2,3])
    unitTest "zipwith" "((4,1),((5,1),((6,2),0)))"
      $ app (app (app zipWith_ (lam (lam (pair (varN 1) (varN 0)))))
                 (ints2g [4,5,6]))
            (ints2g [1,1,2,3])
    unitTest "listequal1" "1" $ app (app list_equality (s2g "hey")) (s2g "hey")
    unitTest "listequal0" "0" $ app (app list_equality (s2g "hey")) (s2g "he")
    unitTest "listequal00" "0" $ app (app list_equality (s2g "hey")) (s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
    unitTest "map" "(2,(3,5))" $ app (app map_ (lam (pair (varN 0) zero)))
                                     (ints2g [1,2,3])
  describe "refinement" $ do
    unitTestRefinement "minimal refinement success" True (check zero (completeLam (varN 0)))
    unitTestRefinement "minimal refinement failure" False
      (check (i2g 1) (completeLam (ite (varN 0) (s2g "whoops") zero)))
    unitTestRefinement "refinement: test of function success" True
     (check (lam (pleft (varN 0))) (completeLam (app (varN 0) (i2g 1))))
    unitTestRefinement "refinement: test of function failure" False
     (check (lam (pleft (varN 0))) (completeLam (app (varN 0) (i2g 2))))
  describe "unitTest2" $ do
    unitTest2 "main = 0" "0"
    unitTest2 fiveApp "5"
    unitTest2 "main = plus $3 $2 succ 0" "5"
    unitTest2 "main = times $3 $2 succ 0" "6"
    unitTest2 "main = pow $3 $2 succ 0" "9"
    unitTest2 "main = (d2cG $4 3) succ 0" "3"
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
  {- TODO -- figure out why this broke
    unitTest2 "main = quicksort [4,3,7,1,2,4,6,9,8,5,7]"
      "(1,(2,(3,(4,(4,(5,(6,(7,(7,(8,10))))))))))"
quickcheckBuiltInOptimizedDoesNotChangeEval up =
-}
  -- , debugPEIITO (SetEnv (Twiddle (Twiddle (Pair (Defer Var) Zero))))
  -- , debugPEIITO (SetEnv (Pair (Defer Var) Zero))
  -- , debugPEIITO (SetEnv (Pair (Defer (Pair Zero Var)) Zero))
  -- , debugREITIE (SetEnv (Pair Env Env))
  -- , debugREITIE (Defer (SetEnv (Pair (Gate Env) (Pair Env Env))))
  -- , debugREITIE (SetEnv (Twiddle (Pair Env Env)))
  -- , debugREITIE (SetEnv (Pair (Gate (SetEnv (Pair (PRight Env) Env))) (Pair Env (Twiddle (PLeft Env)))))

  {-
  , Debugpcpt $ gate (check zero var)
  , debugPCPT $ app var (check zero var)
  , unitTestQC "promotingChecksPreservesType" promotingChecksPreservesType_prop
  , unitTestOptimization "listequal0" $ app (app list_equality (s2g "hey")) (s2g "he")
  , unitTestOptimization "map" $ app (app map_ (lam (pair (varN 0) zero))) (ints2g [1,2,3])
  -}
  -- warning: may be slow
  -- describe "quickcheck" $ do
  --   unitTestQC "builtinOptimizationDoesntBreakEvaluation" 100 quickcheckBuiltInOptimizedDoesNotChangeEval
  -- ++ quickCheckTests unitTest2 unitTestType

testExpr = concat
  [ "main = let a = 0\n"
  , "           b = 1\n"
  , "       in (a,1)\n"
  ]

fiveApp = concat
  [ "main = let fiveApp = $5\n"
  , "       in fiveApp (\\x -> (x,0)) 0"
  ]

nestedNamedFunctionsIssue = concat
  [ "main = let bindTest = \\tlb -> let f1 = \\f -> f tlb\n"
  , "                                  f2 = \\f -> succ (f1 f)\n"
  , "                               in f2 succ\n"
  , "       in bindTest 0"
  ]

{-
nexprTests :: Spec
nexprTests = do
  describe "nexpr eval" $ do
    it "literal" $
      NNum 42 `shouldEvalTo` 42
    it "add" $
      NNum 2 `NAdd` NNum 3 `shouldEvalTo` 5
    it "mul" $
      NNum 2 `NMult` NNum 3 `shouldEvalTo` 6
    it "ite false" $
      NITE (NNum 0) (NNum 1) (NNum 2) `shouldEvalTo` 2
    it "ite true" $
      NITE (NNum 1) (NNum 1) (NNum 2) `shouldEvalTo` 1
  where
    nexpr `shouldEvalTo` r = do
      RunResult r' _ <- llvmEval (NSetEnv (NPair (NDefer nexpr) NZero))
      r' `shouldBe` r
-}

foreign import capi "gc.h GC_INIT" gcInit :: IO ()
foreign import ccall "gc.h GC_allow_register_threads" gcAllowRegisterThreads :: IO ()

unitTest2' parse s r = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> fmap (show . PrettyIExpr) (testEval g) >>= \r2 -> if r2 == r
    then pure ()
    else expectationFailure $ concat [s, " result ", r2]

unitTestType' parse s t tef = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> let apt = typeCheck t $ fromTelomare g
             in if tef apt
                then pure ()
                else expectationFailure $
                      concat [s, " failed typecheck, result ", show apt]

unitTestType2 i t tef = it ("type check " <> show i) $
  let apt = typeCheck t $ fromTelomare i
  in if tef apt
     then pure ()
     else expectationFailure $ concat [show i, " failed typecheck, result ", show apt]

unitTestRuntime' parse s = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> verifyEval g >>= \x -> case x of
    Nothing -> pure ()
    Just (ir, nr) -> expectationFailure $ "expected result: " <> show ir <> "\nactual result: " <> show nr

unitTestSameResult' parse a b = it ("comparing to " <> a) $ case (parse a, parse b) of
  (Right ga, Right gb) -> do
    ra <- testNEval ga -- runExceptT . eval $ (fromTelomare ga :: NExprs)
    rb <- testNEval gb
    if (show ra == show rb)
      then pure ()
      else expectationFailure $ "results don't match: " <> show ra <> " --- " <> show rb
  _ -> expectationFailure "unitTestSameResult failed parsing somewhere"

main = do
  gcInit
  gcAllowRegisterThreads
  preludeFile <- Strict.readFile "Prelude.telomare"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    -- parse = fmap findChurchSize . parseMain prelude
    parse term = case fmap (toTelomare . findChurchSize) (parseMain prelude term) of
      Right (Just term) -> pure term
      Right Nothing -> Left "grammar conversion error"
      Left x -> Left $ show x
  {-
    unitTestP s g = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right pg -> if pg == g
        then pure ()
        else putStrLn $ concat ["parsed oddly ", s, " ", show pg, " compared to ", show g]
-}
  {-
    unitTest2 s r = it s $ case parse s of
      Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
      Right g -> fmap (show . PrettyIExpr) (testEval g) >>= \r2 -> if r2 == r
        then pure ()
        else expectationFailure $ concat [s, " result ", r2]
-}
  {-
    unitTest3 s r = let parsed = parseMain prelude s in case (inferType <$> parsed, parsed) of
      (Right (Right _), Right g) -> fmap (show . PrettyIExpr) (testEval g) >>= \r2 -> if r2 == r
        then pure True
        else (putStrLn $ concat [s, " result ", r2]) >> pure False
      e -> (putStrLn $ concat ["failed unittest3: ", s, " ", show e ]) >> pure False
    unitTest4 s t = let parsed = parseMain prelude s in case debugInferType <$> parsed of
      (Right (Right it)) -> if t == it
        then pure True
        else do
        putStrLn $ concat ["expected type ", show t, " inferred type ", show it]
        pure False
      e -> do
        putStrLn $ concat ["could not infer type ", show e]
        pure False
-}
  {-
    unitTestType s t tef = it s $ case parse s of
      Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
      Right g -> let apt = typeCheck t g
                 in if tef apt
                    then pure ()
                    else expectationFailure $
                          concat [s, " failed typecheck, result ", show apt]
-}
  {-
    parseTelomare s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
-}

  -- TODO change eval to use rEval, then run this over a long non-work period
  {-
  let isProblem (TestIExpr iexpr) = typeable (TestIExpr iexpr) && case eval iexpr of
        Left _ -> True
        _ -> False
  (Right mainAST) <- parseMain prelude <$> Strict.readFile "tictactoe.telomare"
  print . head $ shrinkComplexCase isProblem [TestIExpr mainAST]
  result <- pure False
-}
  hspec $ do
    unitTests parse
    --nexprTests
