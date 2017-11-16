module Main where

import Control.Applicative (liftA2)
import Debug.Trace
import Data.Char
import Data.Monoid
import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer
import System.Exit
import Test.QuickCheck
import qualified System.IO.Strict as Strict

class TestableIExpr a where
  getIExpr :: a -> IExpr

data TestIExpr = TestIExpr IExpr

data ValidTestIExpr = ValidTestIExpr TestIExpr

data TestCheckIExpr = TestCheckIExpr ValidTestIExpr

instance TestableIExpr TestIExpr where
  getIExpr (TestIExpr x) = x

instance Show TestIExpr where
  show (TestIExpr t) = show t

instance TestableIExpr ValidTestIExpr where
  getIExpr (ValidTestIExpr x) = getIExpr x

instance Show ValidTestIExpr where
  show (ValidTestIExpr v) = show v

instance TestableIExpr TestCheckIExpr where
  getIExpr (TestCheckIExpr x) = getIExpr x

instance Show TestCheckIExpr where
  show (TestCheckIExpr x) = show x

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
    Var -> []
    (Gate x) -> TestIExpr x : (map (lift1Texpr gate) . shrink $ TestIExpr x)
    (PLeft x) -> TestIExpr x : (map (lift1Texpr pleft) . shrink $ TestIExpr x)
    (PRight x) -> TestIExpr x : (map (lift1Texpr pright) . shrink $ TestIExpr x)
    (Trace x) -> TestIExpr x : (map (lift1Texpr Trace) . shrink $ TestIExpr x)
    (SetEnv x) -> TestIExpr x : (map (lift1Texpr SetEnv) . shrink $ TestIExpr x)
    (Defer x) -> TestIExpr x : (map (lift1Texpr Defer) . shrink $ TestIExpr x)
    (Twiddle x) -> TestIExpr x : (map (lift1Texpr Twiddle) . shrink $ TestIExpr x)
    (Check x) -> TestIExpr x : (map (lift1Texpr Check) . shrink $ TestIExpr x)
    (Pair a b) -> TestIExpr a : TestIExpr  b :
      [lift2Texpr pair a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]

typeable x = case inferType (getIExpr x) of
  Left _ -> False
  _ -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = map ValidTestIExpr . filter typeable $ shrink te

isCheck (Check _) = True
isCheck _ = False

instance Arbitrary TestCheckIExpr where
  arbitrary = TestCheckIExpr <$> arbitrary `suchThat`
    (getAny . monoidFold (Any . isCheck) . getIExpr)
  shrink (TestCheckIExpr te) =
    map TestCheckIExpr . filter (getAny . monoidFold (Any . isCheck) . getIExpr) $ shrink te

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
d2c baseType =
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
  in app (app (toChurch 255) layer) base

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = lam (ite (varN 0) (ite (pleft (varN 0)) zero (i2g 1)) zero)

d_to_equality = lam (lam (ite (varN 1)
                                          (app d_equals_one (app (app (app (d2c zero) (pleft $ varN 1)) (lam . pleft $ varN 0)) (varN 0)))
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
                                   (app (d2c zero) (varN 1))
                                   (app (d2c zero) (varN 0))
                                   )))

d2c_test = app (app (app (d2c zero) (i2g 2)) (lam (pair (varN 0) zero))) zero

c2d_test = app c2d (toChurch 2)
c2d_test2 = app (lam (app (app (varN 0) (lam (pair (varN 0) zero))) zero)) (toChurch 2)
c2d_test3 = app (lam (app (varN 0) zero)) (lam (pair (varN 0) zero))

double_app = app (app (lam (lam (pair (varN 0) (varN 1)))) zero) zero

test_plus0 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) zero))
test_plus1 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 1)))
test_plus254 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 254)))
test_plus255 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 255)))
test_plus256 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 256)))

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

unitTest :: String -> String -> IExpr -> IO Bool
unitTest name expected iexpr = if allowedTypeCheck (typeCheck ZeroType iexpr)
  then do
    result <- (show . PrettyIExpr) <$> optimizedEval iexpr
    if result == expected
      then pure True
      else (putStrLn $ concat [name, ": expected ", expected, " result ", result]) >>
           pure False
  else putStrLn ( concat [name, " failed typecheck: ", show (typeCheck ZeroType iexpr)])
       >> pure False

unitTestRefinement :: String -> Bool -> IExpr -> IO Bool
unitTestRefinement name shouldSucceed iexpr = if allowedTypeCheck (typeCheck ZeroType iexpr)
  then do
  case (pureEvalWithError iexpr, shouldSucceed) of
    (Left err, True) -> do
      putStrLn $ concat [name, ": failed refinement type -- ", show err]
      pure False
    (Right _, False) -> do
      putStrLn $ concat [name, ": expected refinement failure, but passed"]
      pure False
    _ -> pure True
  else do
  putStrLn $ concat ["refinement test failed typecheck: ", name]
  pure False
{-
unitTestOptimization :: String -> IExpr -> IO Bool
unitTestOptimization name iexpr = if optimize iexpr == optimize2 iexpr
  then pure True
  else (putStrLn $ concat [name, ": optimized1 ", show $ optimize iexpr, " optimized2 "
                          , show $ optimize2 iexpr])
  >> pure False
-}

churchType = (ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType))

-- check that refinements are correct after optimization
promotingChecksPreservesType_prop :: TestIExpr -> Bool
promotingChecksPreservesType_prop (TestIExpr iexpr) =
  inferType iexpr == inferType (promoteChecks iexpr)

debugPCPT :: IExpr -> IO Bool
debugPCPT iexpr = if inferType iexpr == inferType (promoteChecks iexpr)
  then pure True
  else (putStrLn $ concat ["failed ", show iexpr, " / ", show (promoteChecks iexpr)
                          , " -- ", show (inferType iexpr), " / "
                          , show (inferType (promoteChecks iexpr))]) >> pure False

unitTests_ unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  [ unitTestType "main = 0" ZeroType (== Nothing)
  , unitTestType "main : (\\x -> if x then \"fail\" else 0) = 0" ZeroType (== Nothing)
  --, unitTestType "main : (\\x -> if x then 1 else 0) = 0" ZeroType (== Nothing)
  ]

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _ = False

isRecursiveType (Just (RecursiveType _)) = True
isRecursiveType _ = False

isRefinementFailure (Just (RefinementFailure _)) = True
isRefinementFailure _ = False

unitTestTypeP :: IExpr -> Either TypeCheckError PartialType -> IO Bool
unitTestTypeP iexpr expected = if inferType iexpr == expected
  then pure True
  else do
  putStrLn $ concat ["type inference error ", show iexpr, " expected ", show expected
                    , " result ", show (inferType iexpr)
                    ]
  pure False

unitTestQC :: Testable p => String -> p -> IO Bool
unitTestQC name p = quickCheckResult p >>= \result -> case result of
  (Success _ _ _) -> pure True
  x -> (putStrLn $ concat [name, " failed: ", show x]) >> pure False

debugMark s = putStrLn s >> pure True

unitTests unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  [ unitTestType "main = \\x -> {x,0}" (PairType (ArrType ZeroType ZeroType) ZeroType) (== Nothing)
  , unitTestType "main = \\x -> {x,0}" ZeroType isInconsistentType
  , unitTestType "main = succ 0" ZeroType (== Nothing)
  , unitTestType "main = succ 0" (ArrType ZeroType ZeroType) isInconsistentType
  , unitTestType "main = or 0" (PairType (ArrType ZeroType ZeroType) ZeroType) (== Nothing)
  , unitTestType "main = or 0" ZeroType isInconsistentType
  {- broken tests... need to fix type checking for old style annotations or remove
  , unitTestType "main : {0,0} = 0" ZeroType False
  , unitTestType "main : {0,{0,0}} = \\x -> {x,0}" (ArrType ZeroType ZeroType) False
  , unitTestType "main : {0,0} = \\f -> f 0 0" (ArrType ZeroType (ArrType ZeroType ZeroType))
    False
  , unitTestType "main : 0 = \\x -> {x,0}" (ArrType ZeroType ZeroType) False
-}
  , unitTestType "main = or succ" (ArrType ZeroType ZeroType) isInconsistentType
  , unitTestType "main = 0 succ" ZeroType isInconsistentType
  , unitTestType "main = 0 0" ZeroType isInconsistentType
  -- I guess this is inconsistently typed now?
  , unitTestType "main = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
    (ArrType (ArrType ZeroType ZeroType) ZeroType) (/= Nothing) -- isRecursiveType
  , unitTestType "main = (\\f -> f 0) (\\g -> {g,0})" ZeroType (== Nothing)
  {- broken because lambdas now are represented by a pair of function and environment ... probably should remove
  , unitTestType "main : {{{0,0},{0,0}},{{{0,0},{0,0}},{{0,0},{0,0}}}} = \\m n f x -> m f (n f x)" (ArrType churchType (ArrType churchType churchType)) (== Nothing)
  , unitTestType "main = \\m n f x -> m f (n f x)" (ArrType churchType (ArrType churchType churchType)) (== Nothing)
-}
  , unitTestType "main : (\\x -> if x then \"fail\" else 0) = 0" ZeroType (== Nothing)
  -- TODO fix
  --, unitTestType "main : (\\x -> if x then \"fail\" else 0) = 1" ZeroType isRefinementFailure
  , unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
  , unitTest "c2d" "2" c2d_test
  , unitTest "c2d2" "2" c2d_test2
  , unitTest "c2d3" "1" c2d_test3
  , unitTest "oneplusone" "2" one_plus_one
  , unitTest "church 3+2" "5" three_plus_two
  , unitTest "3*2" "6" three_times_two
  , unitTest "3^2" "9" three_pow_two
  , unitTest "test_tochurch" "2" test_toChurch
  , unitTest "three" "3" three_succ
  , unitTest "data 3+5" "8" $ app (app d_plus (i2g 3)) (i2g 5)
  , unitTest "foldr" "13" $ app (app (app foldr_ d_plus) (i2g 1)) (ints2g [2,4,6])
  , unitTest "listlength0" "0" $ app list_length zero
  , unitTest "listlength3" "3" $ app list_length (ints2g [1,2,3])
  , unitTest "zipwith" "{{4,1},{{5,1},{{6,2},0}}}"
    $ app (app (app zipWith_ (lam (lam (pair (varN 1) (varN 0)))))
           (ints2g [4,5,6]))
    (ints2g [1,1,2,3])
  , unitTest "listequal1" "1" $ app (app list_equality (s2g "hey")) (s2g "hey")
  , unitTest "listequal0" "0" $ app (app list_equality (s2g "hey")) (s2g "he")
  , unitTest "listequal00" "0" $ app (app list_equality (s2g "hey")) (s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
  , unitTest "map" "{2,{3,5}}" $ app (app map_ (lam (pair (varN 0) zero)))
    (ints2g [1,2,3])
  , unitTestRefinement "minimal refinement success" True (check zero (pleft (lam (varN 0))))
  , unitTestRefinement "minimal refinement failure" False (check (i2g 1) (pleft (lam (ite (varN 0) (s2g "whoops") zero))))
  , unitTest2 "main = 0" "0"
  , unitTest2 fiveApp "5"
  , unitTest2 "main = plus $3 $2 succ 0" "5"
  , unitTest2 "main = times $3 $2 succ 0" "6"
  , unitTest2 "main = pow $3 $2 succ 0" "8"
  , unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
  , unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
  , unitTest2 "main = dEqual 0 0" "1"
  , unitTest2 "main = dEqual 1 0" "0"
  , unitTest2 "main = dEqual 0 1" "0"
  , unitTest2 "main = dEqual 1 1" "1"
  , unitTest2 "main = dEqual 2 1" "0"
  , unitTest2 "main = dEqual 1 2" "0"
  , unitTest2 "main = dEqual 2 2" "1"
  , unitTest2 "main = listLength []" "0"
  , unitTest2 "main = listLength [1,2,3]" "3"
  , unitTest2 "main = listEqual \"hey\" \"hey\"" "1"
  , unitTest2 "main = listEqual \"hey\" \"he\"" "0"
  , unitTest2 "main = listEqual \"hey\" \"hel\"" "0"
  , unitTest2 "main = listPlus [1,2] [3,4]" "{1,{2,{3,5}}}"
  , unitTest2 "main = listPlus 0 [1]" "2"
  , unitTest2 "main = listPlus [1] 0" "2"
  , unitTest2 "main = concat [\"a\",\"b\",\"c\"]" "{97,{98,100}}"
  , unitTest2 nestedNamedFunctionsIssue "2"
  , unitTest2 "main = take $0 [1,2,3]" "0"
  , unitTest2 "main = take $1 [1,2,3]" "2"
  , unitTest2 "main = take $5 [1,2,3]" "{1,{2,4}}"
  , unitTest2 "main = c2d (minus $4 $3)" "1"
  , unitTest2 "main = c2d (minus $4 $4)" "0"
  , unitTest2 "main = dMinus 4 3" "1"
  , unitTest2 "main = dMinus 4 4" "0"
  , unitTest2 "main = (if 0 then (\\x -> {x,0}) else (\\x -> {{x,0},0})) 1" "3"
  , unitTest2 "main = range 2 5" "{2,{3,5}}"
  , unitTest2 "main = range 6 6" "0"
  , unitTest2 "main = c2d (factorial 4)" "24"
  , unitTest2 "main = c2d (factorial 0)" "1"
  , unitTest2 "main = filter (\\x -> dMinus x 3) (range 1 8)"
    "{4,{5,{6,8}}}"
  , unitTest2 "main = quicksort [4,3,7,1,2,4,6,9,8,5,7]"
    "{1,{2,{3,{4,{4,{5,{6,{7,{7,{8,10}}}}}}}}}}"
  {-
  , debugPCPT $ gate (check zero var)
  , debugPCPT $ app var (check zero var)
  , unitTestQC "promotingChecksPreservesType" promotingChecksPreservesType_prop
  , unitTestOptimization "listequal0" $ app (app list_equality (s2g "hey")) (s2g "he")
  , unitTestOptimization "map" $ app (app map_ (lam (pair (varN 0) zero))) (ints2g [1,2,3])
  -}
  ]

testExpr = concat
  [ "main = let a = 0\n"
  , "           b = 1\n"
  , "       in {a,1}\n"
  ]

fiveApp = concat
  [ "main = let fiveApp = $5\n"
  , "       in fiveApp (\\x -> {x,0}) 0"
  ]

nestedNamedFunctionsIssue = concat
  [ "main = let bindTest = \\tlb -> let f1 = \\f -> f tlb\n"
  , "                                   f2 = \\f -> succ (f1 f)\n"
  , "                               in f2 succ\n"
  , "       in bindTest 0"
  ]

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    unitTestP s g = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right pg -> if pg == g
        then pure ()
        else putStrLn $ concat ["parsed oddly ", s, " ", show pg, " compared to ", show g]
    unitTest2 s r = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> fmap (show . PrettyIExpr) (optimizedEval g) >>= \r2 -> if r2 == r
        then pure True
        else (putStrLn $ concat [s, " result ", r2]) >> pure False
    unitTest3 s r = let parsed = parseMain prelude s in case (inferType <$> parsed, parsed) of
      (Right (Right _), Right g) -> fmap (show . PrettyIExpr) (optimizedEval g) >>= \r2 -> if r2 == r
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
    unitTestType s t tef = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> let apt = typeCheck t g
                 in if tef apt
                    then pure True
                    else (putStrLn $
                          concat [s, " failed typecheck, result ", show apt])
             >> pure False
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
  {-
  unitTest4 "main = (\\x -> {x,0}) 0" ZeroTypeP
  unitTest4 "main = $3" ZeroTypeP
  unitTest4 "main = $3 (\\x -> {x,0})" ZeroTypeP
-}
  result <- unitTests unitTest2 unitTestType
  exitWith $ if result then ExitSuccess else ExitFailure 1
