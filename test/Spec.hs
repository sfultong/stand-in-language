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
import Data.Void
import Debug.Trace
import Naturals
import System.Exit
import System.IO
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Decompiler
import Telomare.Eval
import Telomare.Optimizer
import Telomare.Parser
import Telomare.Possible
import Telomare.Resolver
import Telomare.RunTime
import Telomare.TypeChecker
import Test.Hspec
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck

-- Common datatypes for generating Telomare AST.
import Common

-- recursively finds shrink matching invariant, ordered simplest to most complex
shrinkComplexCase :: Arbitrary a => (a -> Bool) -> [a] -> [a]
shrinkComplexCase test a =
  let shrinksWithNextLevel = fmap (\x -> (x, filter test $ shrink x)) a
      (recurseable, nonRecursable) = partition (not . null . snd) shrinksWithNextLevel
  in (shrinkComplexCase test (concatMap snd recurseable) <> fmap fst nonRecursable)

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
  in layer (layer (layer (layer stopf))) i

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

times_two =
  let times_app = lam (lam (app (toChurch 2) (app (varN 1) (varN 0))))
  in app c2d (app times_app (toChurch 3))

times_three =
  let times_app = lam (lam (app (varN 1) (app (toChurch 3) (varN 0))))
  in app c2d (app times_app (toChurch 2))

times_wip =
  let times_app = lam (lam (app (varN 1) (app (toChurch 3) (varN 0))))
  -- in app c2d (app times_app (toChurch 2))
-- c2d = lam (app (app (varN 0) (lam (pair (varN 0) zero))) zero)
  in app c2d (toChurch 6)

function_argument =
  app (lam (app (varN 0) zero)) (lam (pair zero (varN 0)))

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

-- validate termination checking
inf_pairs =
  let firstArg = pleft env
      recur = defer (pair zero (setenv (pair firstArg env)))
  in setenv (pair recur (pair recur zero))

-- unbound type errors should be allowed for purposes of testing runtime
allowedTypeCheck :: Maybe TypeCheckError -> Bool
allowedTypeCheck Nothing                = True
allowedTypeCheck (Just (UnboundType _)) = True
allowedTypeCheck _                      = False

testEval :: IExpr -> IO IExpr
-- testEval iexpr = optimizedEval (SetEnv (Pair (Defer iexpr) Zero))
-- testEval iexpr = optimizedEval (SetEnv (Pair (Defer deserialized) Zero))
testEval iexpr = evalBU' (SetEnv (Pair (Defer iexpr) Zero))
-- testEval iexpr = evalB'' (SetEnv (Pair (Defer iexpr) Zero))

-- TODO get rid of testEval and just use this
testEval' iexpr = evalBU (SetEnv (Pair (Defer iexpr) Zero))

unitTest :: String -> String -> IExpr -> Spec
unitTest name expected iexpr = it name $ if allowedTypeCheck (typeCheck ZeroTypeP (fromTelomare iexpr))
  then do
    result <- show . PrettyIExpr <$> testEval iexpr
    result `shouldBe` expected
  else expectationFailure ( concat [name, " failed typecheck: ", show (typeCheck ZeroTypeP (fromTelomare iexpr))])

unitTestRefinement :: String -> Bool -> IExpr -> Spec
unitTestRefinement name shouldSucceed iexpr = it name $ case inferType (fromTelomare iexpr) of
  Right t -> case (pureEval iexpr, shouldSucceed) of
    (Left err, True) -> expectationFailure $ concat [name, ": failed refinement type -- ", show err]
    (Right _, False) -> expectationFailure $ name <> ": expected refinement failure, but passed"
    _ -> pure ()
  Left err -> expectationFailure $ concat ["refinement test failed typecheck: ", name, " ", show err]

unitTestQC :: Testable p => String -> Int -> p -> Spec
unitTestQC name times = modifyMaxSuccess (const times) . it name . property

churchType = ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType)

-- quickcheckBuiltInOptimizedDoesNotChangeEval :: UnprocessedParsedTerm -> Bool
-- quickcheckBuiltInOptimizedDoesNotChangeEval up =
--   let iexpr = toTelomare . findChurchSize <$> fmap splitExpr . (>>= debruijinize []) . validateVariables id $ up
--   in False
{-
quickcheckBuiltInOptimizedDoesNotChangeEval :: UnprocessedParsedTerm -> Bool
quickcheckBuiltInOptimizedDoesNotChangeEval up =
  let
      makeTelomare f = second (toTelomare . findChurchSize) (fmap splitExpr . (>>= debruijinize []) . validateVariables [] . f . addBuiltins $ up)
      iexpr :: Either String (Maybe IExpr)
      iexpr = makeTelomare id -- x. validateVariables id . optimizeBuiltinFunctions $ up)
      iexpr' = makeTelomare optimizeBuiltinFunctions -- second (toTelomare . findChurchSize) (fmap splitExpr . (>>= debruijinize []) . validateVariables id $ up)
  in
    case (iexpr, iexpr') of
       (Right (Just ie), Right (Just ie')) -> pureEval ie == pureEval ie'
       _ | iexpr == iexpr'-> True
       _ | otherwise -> False
-}

-- unitTestTypeP :: IExpr -> Either TypeCheckError PartialType -> IO Bool
  -- inferType (fromTelomare iexpr)
quickcheckDataTypedCorrectlyTypeChecks :: DataTypedIExpr -> Bool
quickcheckDataTypedCorrectlyTypeChecks (IExprWrapper x) = not . null $ inferType (fromTelomare x)

qcDecompileIExprAndBackEvalsSame :: DataTypedIExpr -> Bool
qcDecompileIExprAndBackEvalsSame (IExprWrapper x) = pure (showResult $ eval' x)
  -- == fmap (showResult . eval') (toTelomare . findChurchSize . splitExpr . showTrace . decompileTerm4 $ decompileIExpr x)
  == fmap (showResult' . eval') (showTrace' . toTelomare . comp . showTrace . dec $ x)
  where eval' = pureIEval
        debruijinize' x = case debruijinize [] x of
          Just r -> r
          _      -> error "debruijinize error"
        validateVariables' x = case validateVariables [] x of
          Right r -> r
          Left e  -> error ("validateVariables " <> e)
        parseLongExpr' x = case runTelomareParser (scn *> parseLongExpr <* scn) x of
          Just r -> r
          _      -> error "parseLongExpr' should be impossible"
        findChurchSize' x = case findChurchSize x of
          Right r -> r
          Left e  -> error ("findChurchSize' error: " <> show e)
        dec = decompileUPT . decompileTerm1 . decompileTerm2 . decompileTerm4 . decompileIExpr
        comp = findChurchSize' . splitExpr . debruijinize' . validateVariables' . optimizeBuiltinFunctions . parseLongExpr'
        showTrace x = x -- trace ("decompiled: " <> show x) x
        showTrace' x = x -- trace ("recompiled: " <> show x) x
        showResult x = x -- trace ("desired result: " <> show x) x
        showResult' x = x -- trace ("actual result: " <> show x) x

{-
qcTestMapBuilderEqualsRegularEval :: DataTypedIExpr -> Bool
qcTestMapBuilderEqualsRegularEval (IExprWrapper x) = (showResult $ eval' x)
  == pure (showResult' . decodePossible . showIntermediate $ possibleConvert AnyX (rootFrag termMap))
  where eval' = pureIEval
        (Term3 termMap) = splitExpr . decompileTerm4 $ decompileIExpr x
        annotateAux ur = pure . FunctionX $ AuxFrag ur -- should never actually be called
        possibleConvert i f = (\tmb -> runReader (State.evalStateT tmb mempty) (const 0)) $
          toPossible (termMap Map.!) testBuildingSetEval annotateAux i f
        -- tmb = toPossible (termMap Map.!) testBuildingSetEval annotateAux AnyX (rootFrag termMap)
        -- possibleResult = runReader (State.evalStateT tmb mempty) (const 0)
        decodePossible x' = case toIExprList' possibleConvert x' of
          DList.Cons r [] -> r
          _ -> error ("bad possible from " <> show x)
        showIntermediate x = trace ("intermediate possible: " <> show x) x
        showResult x = trace ("desired result: " <> show x) x
        showResult' x = trace ("actual result: " <> show x) x
-}

qcTestURSizing :: URTestExpr -> Bool
qcTestURSizing (URTestExpr t3) =
  let compile x = toTelomare <$> findChurchSize x
      compile' x = pure . toTelomare $ convertPT (const 255) x
  in (fmap . fmap) pureIEval (compile t3) == (fmap . fmap) pureIEval (compile' t3)
{-
qcTestAbortExtract :: (URTestExpr, Int) -> Bool
qcTestAbortExtract (URTestExpr (Term3 termMap), i) =
  null staticToPossible
  == extractedTestResult where
  staticToPossible :: Either IExpr (PossibleExpr BreakExtras Void)
  staticToPossible = toPossible (termMap' Map.!) staticAbortSetEval (pure . FunctionX . AuxFrag) AnyX (rootFrag termMap')
  sizer = const i
  (Term4 termMap') = convertPT sizer (Term3 termMap)
  mapLookup' = (termMap Map.!)
  annotateAux ur = pure . AnnotateX ur . FunctionX $ AuxFrag ur
  testMapBuilder = toPossible mapLookup' testBuildingSetEval annotateAux AnyX (rootFrag termMap)
  tests = splitTests . ($ i) . runReader .  (Map.! toEnum 0) . ($ sizer) . runReader $ State.execStateT testMapBuilder mempty
  wrapAux = pure . FunctionX . AuxFrag
  runTest (frag, inp) = null $ toPossible mapLookup' sizingAbortSetEval wrapAux inp frag
  extractedTestResult = or $ fmap runTest tests
-}

{-
qcTestBottomUp :: DataTypedIExpr -> Bool
qcTestBottomUp x =
  let exp = getIExpr x
  in evalS exp == evalBU exp
-}

testRecur = concat
  [ "main = let layer = \\recur x -> recur (x, 0)"
  , "\n"
  , "       in $3 layer (\\x -> x) 0"
  ]

testSBV'' = do
  r <- runIO testSBV'
  runIO $ if r == 4
    then pure ()
    else expectationFailure $ "testSBV failed, got result " <> show r
  -- assertEqual "testing SBV" r 3

-- unitTests_ :: (String -> String -> Spec) -> (String -> PartialType -> (Maybe TypeCheckError -> Bool) -> Spec) -> Spec
unitTests_ parse = do
  let unitTestType = unitTestType' parse
      unitTest2 = unitTest2' parse
      unitTestStaticChecks = unitTestStaticChecks' parse
      unitTestPossible = unitTestPossible' parse
      -- decompileExample = IExprWrapper (SetEnv (SetEnv (Pair (Defer (Pair (Gate Env Env) (Pair Zero Zero))) (SetEnv (SetEnv (SetEnv (PLeft (Pair (Pair (Defer (Pair (Defer (Pair (Defer Zero) Env)) Env)) Zero) Zero))))))))
      -- decompileExample = IExprWrapper (SetEnv (SetEnv (Pair (Defer (Pair (Gate Env Env) (Pair Zero Zero))) Zero)))
      decompileExample = IExprWrapper (SetEnv (SetEnv (Pair (Defer (Pair (Gate Env Env) (Pair Zero (Pair Zero Zero)))) Zero)))
      -- decompileExample = IExprWrapper (SetEnv (SetEnv (SetEnv (Pair (Defer (Pair (Defer (Pair (Defer Zero) Env)) Env)) Zero))))
  {-
      unitTestRuntime = unitTestRuntime' parse
      unitTestSameResult = unitTestSameResult' parse
-}
  -- unitTestQC "decompileIexprToTerm2AndBackEvalsSame" 2000 qcDecompileIExprAndBackEvalsSame
  -- unitTestQC "possibleEvalIsLikeRegularEval" 15000 qcTestMapBuilderEqualsRegularEval
  -- unitTestQC "qcTestAbortExtract" 2000 qcTestAbortExtract
  -- unitTestQC "qcTestURSizing" 2000 qcTestURSizing

  -- unitTest2 "main = ? (\\r x -> if x then r (left x) else 0) (\\a -> 0) 1" "0" -- we're good now, for every n
  -- unitTest2 "main = listLength [1,2,3]" "3" -- fails
  -- unitTest2 "main = foldr (\\a b -> (a,b)) [] [1,2]" "[1,2]"
  -- unitTestPossible "main : (\\x -> assert (not x) \"fail\") = 1" $ (== Left (StaticCheckError "user abort: fail"))
  -- unitTestPossible "main = let x : ((\\x -> assert (not x) \"fail\")) = 1 in x" null
  -- unitTestPossible "main = let x : ((\\x -> assert (not x) \"fail\")) = 1 in left (1, x)" (== Right (PairX ZeroX ZeroX))
  -- unitTestPossible "main = let x : ((\\x -> assert (not x) \"fail\")) = 1 in left (1, x)" (== Right (PairX ZeroX ZeroX))
  -- unitTestPossible "main = let f = (\\x -> let xb : (\\xb -> assert 0 \"fail\") = 0 in xb) in $1 (\\r l -> if l then r (left l) else 0) f [1,2]" null
  -- unitTestPossible "main = let f = (\\x -> let xb : (\\xb -> assert 0 \"fail\") = 0 in xb) in $1 (\\r mf l -> if l then (mf (left l), r (right l)) else 0) f succ [1,2]" null -- works fine
  -- unitTest2 "main = map succ [1,2]" "[2,3]" -- fails (CURRENTLY BEST FAIL?)
  -- unitTest2 "main = filter (\\x -> dMinus x 3) (range 1 8)" "(4,(5,(6,8)))" -- success!
  -- unitTestStaticChecks "main : (\\x -> assert (not (left x)) \"fail\") = 1" $ (not . null)
  {-
  unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
  unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
  -- unitTest "abort" "1" (pair (Abort (pair zero zero)) zero)
  --unitTest "notAbort" "2" (setenv (pair (setenv (pair Abort zero)) (pair (pair zero zero) zero)))
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
-}
  describe "bottom up eval" $ do
    {-
    it "test SBV" . liftIO $ do
      testSBV' == pure 3
-}
    testSBV''
  {-
    unitTest2 "main = plus $3 $2 succ 0" "5"
    unitTest2 "main = 0" "0"
    unitTest2 fiveApp "5"
    unitTest2 "main = plus $3 $2 succ 0" "5"
    unitTest2 "main = times $3 $2 succ 0" "6"
-}
    -- unitTest2 "main = d2c 2 succ 0" "2"
    -- unitTestStaticChecks "main : (\\x -> assert 1 \"A\") = 1" (not . null)
  describe "main function tests" $ do
    testMain <- runIO $ Strict.readFile "testchar.tel"
    case fmap compileMain (parse testMain) of
      Right (Right g) ->
        let eval = funWrap' evalBU g
            unitTestMain s i e = it ("main input " <> i) $ eval (Just (i, s)) `shouldBe` e
        in do
        unitTestMain Zero "A" ("ascii value of first char is odd", Just Zero)
        unitTestMain Zero "B" ("ascii value of first char is even", Just Zero)
      z -> runIO . expectationFailure $ "failed to compile main: " <> show z
  {-
  describe "main function tests" $ do
    testMain <- runIO $ Strict.readFile "minimal.tel"
    case fmap compileMain (parse testMain) of
      Right (Right g) ->
        let eval = funWrap' evalBU g
            unitTestMain s i e = it ("main input " <> i) $ eval (Just (i, s)) `shouldBe` e
        in do
        unitTestMain Zero " " ("#", Just Zero)
        -- unitTestMain Zero "B" ("ascii value of first char is odd", Just Zero)
      z -> runIO . expectationFailure $ "failed to compile main: " <> show z
-}
    -- unitTest2 "main = d2c 3 succ 0" "3"
    -- unitTestStaticChecks "main : (\\x -> assert (not ($2 left x)) \"A\") = 3" (== Left (StaticCheckError "user abort: X"))
    -- unitTest2 "main = map left [1,2]" "(0,2)" -- test "left" as a function rather than builtin requiring argument
    -- unitTest2 "main = listLength []" "0"
    -- unitTest2 "main = listLength [1,2,3]" "3"
    -- unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
    -- unitTest2 "main = d2c 3 succ 0" "3"
    -- unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
  {-
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
-}

c2dApp = "main = (c2dG $4 3) $2 succ 0"

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _                              = False

isRecursiveType (Just (RecursiveType _)) = True
isRecursiveType _                        = False

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
      unitTestStaticChecks = unitTestStaticChecks' parse
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
    -- unitTestType "main = ? (\\r l -> if l then r (left l) else 0) (\\l -> 0) 2" ZeroTypeP (== Nothing)
    unitTestType "main = {id,\\r l -> r (left l),id} 2" ZeroTypeP (== Nothing)
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
    unitTestType2 inf_pairs ZeroTypeP isRecursiveType
  describe "unitTest" $ do
    unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
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
    case fmap compileMain (parse testMain) of
      Right (Right g) ->
        let eval = funWrap' evalBU g
            unitTestMain s i e = it ("main input " <> i) $ eval (Just (i, s)) `shouldBe` e
        in do
        unitTestMain Zero "A" ("ascii value of first char is odd", Just Zero)
        unitTestMain Zero "B" ("ascii value of first char is even", Just Zero)
      z -> runIO . expectationFailure $ "failed to compile main: " <> show z
  {-
  describe "unsizedEval tests" $ do
    unitTestUnsized parse "main = d2c 3 succ 0"
    unitTestUnsized parse
      $  "main =\n"
      <> "  let t = \\i -> i\n"
      <> "      r = \\recur i -> recur (left i)\n"
      <> "      b = \\i -> (i, 0)\n"
      <> "  in {t,r,b} 3"
-}


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
  --   unitTestQC "propertyDecompileThenCompileIsIdentity" 1000 propertyDecompileThenCompileIsIdentity
  --   unitTestQC "builtinOptimizationDoesntBreakEvaluation" 100 quickcheckBuiltInOptimizedDoesNotChangeEval
  -- ++ quickCheckTests unitTest2 unitTestType

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

unitTest2' parse s r = it s $ case fmap compileUnitTest (parse s) of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right (Right g) -> testEval g >>= (\r2 -> if r2 == r
    then pure ()
    else expectationFailure $ concat [s, " result ", r2]) . show . PrettyIExpr
  Right (Left e) -> expectationFailure $ "failed to compile: " <> show e

-- TODO make this do something meaningful. Currently compiling will remove UnsizedF parts from grammar, so unsizedStepM never triggers
{-
unitTestUnsized parse s = it ("test unsized with " <> s) $ case fmap compileUnitTest (parse s) of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right (Right g) ->
    let evalStep :: UnsizedExprF (StrictAccum SizedRecursion UnsizedExpr) -> StrictAccum SizedRecursion UnsizedExpr
        evalStep = basicStepM (stuckStepM (abortStepM (unsizedStepM 255 evalStep unhandledError)))
        evalU :: UnsizedExpr -> StrictAccum SizedRecursion UnsizedExpr
        evalU = transformNoDeferM evalStep
        unhandledError z = error $ ("test unsized " <> s <> " unhandled thing ") -- <> show (getX z))
        evalUnsized = toTelomare . getX . evalU
    in pure (testEval' g) `shouldBe` evalUnsized (fromTelomare g)
-}

{-
runPossible iexpr = evalS (SetEnv (Pair (Defer iexpr) Zero))

unitTestPossible' parse s f = it s $ case fmap runPossible (parse s) of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right r' -> if f r'
    then pure ()
    else expectationFailure $ s <> " result " <> show (r')
-}
unitTestPossible' = undefined

unitTestType' parse s t tef = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> let apt = typeCheck t g
             in if tef apt
                then pure ()
                else expectationFailure $
                      concat [s, " failed typecheck, result ", show apt]

unitTestStaticChecks' parse s c = it s $ case parse s of
  Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> let rr = findChurchSize g >>= runStaticChecks
              in if c rr
                then pure ()
                else do
    --putStrLn $ "grammar is " <> show g
    expectationFailure $ "static check failed with " <> show rr

unitTestType2 i t tef = it ("type check " <> show i) $
  let apt = typeCheck t $ fromTelomare i
  in if tef apt
     then pure ()
     else expectationFailure $ concat [show i, " failed typecheck, result ", show apt]

{-
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
-}

main = do
  preludeFile <- Strict.readFile "Prelude.tel"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    parse = parseMain prelude

  hspec $ unitTests_ parse
    --nexprTests
