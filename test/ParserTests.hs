{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main where

import           Common
import           Control.Lens.Fold
import           Control.Lens.Plated
import           Control.Monad
import           Control.Monad.Except      (ExceptT, MonadError, catchError,
                                            runExceptT, throwError)
import           Control.Monad.Fix         (fix)
import           Control.Monad.IO.Class    (liftIO)
import qualified Control.Monad.State       as State
import           Data.Algorithm.Diff       (getGroupedDiff)
import           Data.Algorithm.DiffOutput (ppDiff)
import           Data.Bifunctor
import           Data.Either               (fromRight)
import           Data.Functor.Foldable
import           Data.List
import           Data.Map                  (Map, fromList, toList)
import qualified Data.Map                  as Map
import           Data.Ord
import qualified Data.Semigroup            as Semigroup
import qualified Data.Set                  as Set
import           Debug.Trace               (trace, traceShowId)
import qualified System.IO.Strict          as Strict
import           System.IO.Unsafe          (unsafePerformIO)
import           Telomare
import           Telomare.Eval
import           Telomare.Parser
import           Telomare.RunTime
import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck     as QC
import           Text.Megaparsec
import           Text.Megaparsec.Debug
import           Text.Megaparsec.Error
import           Text.Show.Pretty          (ppShow)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, qcProps]

qcProps = testGroup "Property tests (QuickCheck)"
  [ QC.testProperty "Arbitrary UnprocessedParsedTerm to test hash uniqueness of HashUP's" $
      \x -> withMaxSuccess 16 $
        containsTHash x QC.==> checkAllHashes . generateAllHashes $ x
  -- , QC.testProperty "Have the total amount of THash + ? be equal to total ? after generateAllHashes" $
  --     \x -> withMaxSuccess 10 $
  --       containsTHash x QC.==> checkNumberOfHashes x
  , QC.testProperty "See that generateAllHashes only changes HashUP to ListUP" $
      \x -> withMaxSuccess 16 $
        containsTHash x QC.==> onlyHashUPsChanged x
  ]

-- -- The trace statements help showing why this doesn't work: the number of TPair's isn't cosntat for all processed `THash`es
-- checkNumberOfHashes :: Term2 -> Bool
-- checkNumberOfHashes term2 = let tterm2 = generateAllHashes term2
--                             in trace
--                                 ("!!!!!!!!!!!!!!!!!!! 1: " <> (show $ length (term2 ^.. (cosmos . _THash)) + length (term2 ^.. (cosmos . _TZero))))
--                                 (1675 * (length (term2 ^.. (cosmos . _THash))) + length (term2 ^.. (cosmos . _TZero))) ==
--                                   trace
--                                     ("!!!!!!!!!!!!!!!!!!! 2: " <> (show $ length (tterm2 ^.. (cosmos . _TZero))))
--                                     (length (tterm2 ^.. (cosmos . _TZero)))

containsTHash :: Term2 -> Bool
containsTHash = \case
  THash _    -> True
  TITE a b c -> containsTHash a || containsTHash b || containsTHash c
  TPair a b  -> containsTHash a || containsTHash b
  TApp a b   -> containsTHash a || containsTHash b
  TCheck a b -> containsTHash a || containsTHash b
  TLam _ a   -> containsTHash a
  TLeft a    -> containsTHash a
  TRight a   -> containsTHash a
  TTrace a   -> containsTHash a
  x          -> False

onlyHashUPsChanged :: Term2 -> Bool
onlyHashUPsChanged term2 = let diffList = diffTerm2 (term2, generateAllHashes term2)
                               isHash :: Term2 -> Bool
                               isHash = \case
                                 THash _ -> True
                                 _       -> False
                           in and $ fmap (isHash . fst) diffList

diffTerm2 :: (Term2, Term2) -> [(Term2, Term2)]
diffTerm2 = \case
  (TITE a b c, TITE a' b' c') -> diffTerm2 (a, a') <> diffTerm2 (b, b') <> diffTerm2 (c, c')
  (TPair a b, TPair a' b') -> diffTerm2 (a, a') <> diffTerm2 (b, b')
  (TApp a b, TApp a' b') -> diffTerm2 (a, a') <> diffTerm2 (b, b')
  (TCheck a b, TCheck a' b') -> diffTerm2 (a, a') <> diffTerm2 (b, b')
  (TLam _ a, TLam _ a') -> diffTerm2 (a, a')
  (TLeft a, TLeft a') -> diffTerm2 (a, a')
  (TRight a, TRight a') -> diffTerm2 (a, a')
  (TTrace a, TTrace a') -> diffTerm2 (a, a')
  (x, x') | x /= x' -> [(x, x')]
  _ -> []

checkAllHashes :: Term2 -> Bool
checkAllHashes = noDups . allHashesToTerm2

noDups = not . f []
  where
    f seen (x:xs) = x `elem` seen || f (x:seen) xs
    f seen []     = False

allHashesToTerm2 :: Term2 -> [Term2]
allHashesToTerm2 term2 =
  let term2WithoutTHash = generateAllHashes term2
      interm :: (Term2, Term2) -> [Term2]
      interm = \case
        (THash _ , x) -> [x]
        (TITE a b c, TITE a' b' c') -> interm (a, a') <> interm (b, b') <> interm (c, c')
        (TPair a b, TPair a' b') -> interm (a, a') <> interm (b, b')
        (TApp a b, TApp a' b') -> interm (a, a') <> interm (b, b')
        (TCheck a b, TCheck a' b') -> interm (a, a') <> interm (b, b')
        (TLam _ a, TLam _ a') -> interm (a, a')
        (TLeft a, TLeft a') -> interm (a, a')
        (TRight a, TRight a') -> interm (a, a')
        (TTrace a, TTrace a') -> interm (a, a')
        (x, x') | x /= x' -> error "x and x' should be the same (inside of allHashesToTerm2, within interm)"
        (x, x') -> []
  in curry interm term2 term2WithoutTHash

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "different values get different hashes" $ do
      let res1 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest0
          res2 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest1
      (res1 == res2) `compare` False @?= EQ
      -- #^This commmented test tests if two variables having the same value are assigned the same hash
  , testCase "same functions have the same hash even with different variable names" $ do
     let res1 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest2
         res2 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest3
     res1 `compare` res2  @?= EQ
  , testCase "parse uniqueUP" $ do
      res <- parseSuccessful parseHash "# (\\x -> x)"
      res `compare` True @?= EQ
  , testCase "Ad hoc user defined types success" $ do
      res <- testUserDefAdHocTypes userDefAdHocTypesSuccess
      -- res `compare` "\n\4603\a\ndone" @?= EQ
      (length res) `compare` 7 @?= EQ -- This might be weak, but the above is too fragil. The number 4603 can change and the test should still be successful.
  , testCase "Ad hoc user defined types failure" $ do
      res <- testUserDefAdHocTypes userDefAdHocTypesFailure
      res `compare` "\nMyInt must not be 0\ndone" @?= EQ
  , testCase "test function applied to a string that has whitespaces in both sides inside a structure" $ do
      res1 <- parseSuccessful parseLongExpr "(foo \"woops\" , 0)"
      res2 <- parseSuccessful parseLongExpr "(foo \"woops\" )"
      res3 <- parseSuccessful parseLongExpr "if 0 then foo \"woops\" else 0"
      res4 <- parseSuccessful parseLongExpr "[ foo \"woops\" ]"
      (res1 && res2 && res3 && res4) `compare` True @?= EQ
  , testCase "test Pair 0" $ do
      res <- parseSuccessful (parsePair >> eof) testPair0
      res `compare` True @?= EQ
  , testCase "test ITE 1" $ do
      res <- parseSuccessful parseITE testITE1
      res `compare` True @?= EQ
  , testCase "test ITE 2" $ do
      res <- parseSuccessful parseITE testITE2
      res `compare` True @?= EQ
  , testCase "test ITE 3" $ do
      res <- parseSuccessful parseITE testITE3
      res `compare` True @?= EQ
  , testCase "test ITE 4" $ do
      res <- parseSuccessful parseITE testITE4
      res `compare` True @?= EQ
  , testCase "test ITE with Pair" $ do
      res <- parseSuccessful parseITE testITEwPair
      res `compare` True @?= EQ
  , testCase "test if Complete Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testCompleteLambdawITEwPair
      res `compare` True @?= EQ
  , testCase "test if Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testLambdawITEwPair
      res `compare` True @?= EQ
  , testCase "test parse assignment with Complete Lambda with ITE with Pair" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseAssignmentwCLwITEwPair1
      res `compare` True @?= EQ
  , testCase "test if testParseTopLevelwCLwITEwPair parses successfuly" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseTopLevelwCLwITEwPair
      res `compare` True @?= EQ
  , testCase "test parseMain with CL with ITE with Pair parses" $ do
      res <- runTestMainwCLwITEwPair
      res `compare` True @?= EQ
  , testCase "testList0" $ do
      res <- parseSuccessful parseList testList0
      res `compare` True @?= EQ
  , testCase "testList1" $ do
      res <- parseSuccessful parseList testList1
      res `compare` True @?= EQ
  , testCase "testList2" $ do
      res <- parseSuccessful parseList testList2
      res `compare` True @?= EQ
  , testCase "testList3" $ do
      res <- parseSuccessful parseList testList3
      res `compare` True @?= EQ
  , testCase "testList4" $ do
      res <- parseSuccessful parseList testList4
      res `compare` True @?= EQ
  , testCase "testList5" $ do
      res <- parseSuccessful parseList testList5
      res `compare` True @?= EQ
  , testCase "test parse Prelude.tel" $ do
      res <- runTestParsePrelude
      res `compare` True @?= EQ
  , testCase "test parse tictactoe.tel" $ do
      res <- testWtictactoe
      res `compare` True @?= EQ
  , testCase "test Main with Type" $ do
      res <- runTestMainWType
      res `compare` True @?= EQ
  , testCase "testShowBoard0" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard0
      res `compare` True @?= EQ
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard1
      res `compare` True @?= EQ
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard2
      res `compare` True @?= EQ
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard3
      res `compare` True @?= EQ
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard4
      res `compare` True @?= EQ
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard5
      res `compare` True @?= EQ
  , testCase "testShowBoard6" $ do
      res <- parseSuccessful (parseApplied) testShowBoard6
      res `compare` True @?= EQ
  , testCase "testLetShowBoard0" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard0
      res `compare` True @?= EQ
  , testCase "testLetShowBoard1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard1
      res `compare` True @?= EQ
  , testCase "testLetShowBoard2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard2
      res `compare` True @?= EQ
  , testCase "testLetShowBoard3" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard3
      res `compare` True @?= EQ
  , testCase "testLetShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testLetShowBoard4
      res `compare` True @?= EQ
  , testCase "testLetShowBoard5" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard5
      res `compare` True @?= EQ
  , testCase "testLetShowBoard8" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard8
      res `compare` True @?= EQ
  , testCase "testLetShowBoard9" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard9
      res `compare` True @?= EQ
  , testCase "AST terms as functions" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app left (pair zero zero)"
      res `compare` True @?= EQ
  , testCase "left with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "left (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res `compare` True @?= EQ
  , testCase "right with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "right (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res `compare` True @?= EQ
  , testCase "trace with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "trace (\\x -> (\\y -> (x,y))) 0 0"
      res `compare` True @?= EQ
  , testCase "app with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app (\\x y z -> x) 0 1 2"
      res `compare` True @?= EQ
  , testCase "testLetIndentation" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIndentation
      res `compare` True @?= EQ
  , testCase "testLetIncorrectIndentation1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation1
      res `compare` False @?= EQ
  , testCase "testLetIncorrectIndentation2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation2
      res `compare` False @?= EQ
  , testCase "test automatic open close lambda" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> (x, y)"
      (fromRight TZero $ validateVariables [] res) `compare` closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 2" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x y -> (x, y)"
      (fromRight TZero $ validateVariables [] res) `compare` closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 3" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> z"
      (fromRight TZero $ validateVariables [] res) `compare` expr6 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> (x, x)"
      (fromRight TZero $ validateVariables [] res) `compare` expr5 @?= EQ
  , testCase "test automatic open close lambda 5" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\x -> \\x -> x"
      (fromRight TZero $ validateVariables [] res) `compare` expr4 @?= EQ
  , testCase "test automatic open close lambda 6" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> [x,y,z]"
      (fromRight TZero $ validateVariables [] res) `compare` expr3 @?= EQ
  , testCase "test automatic open close lambda 7" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\a -> (a, (\\a -> (a,0)))"
      (fromRight TZero $ validateVariables [] res) `compare` expr2 @?= EQ
  ]

hashtest0 = unlines ["let wrapper = 2",
                "  in (# wrapper)"]

hashtest1 = unlines ["let var = 3",
                "  in (# var)"]
hashtest2 = unlines [ "let a = \\y -> y"
               , "in (# a)"
               ]
hashtest3 = unlines [ "let b = \\x -> x"
               , "in (# b)"
               ]

testUserDefAdHocTypes :: String -> IO String
testUserDefAdHocTypes input = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error pe
    runMain :: String -> IO String
    runMain s = case compileUnitTest <$> parseMain prelude s of
      Left e -> error $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop_ g
      Right z -> error $ "compilation failed somehow, with result " <> show z
  runMain input

test_rEval = simpleEval $ SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair Zero (Pair (Defer (Pair Zero Zero)) Zero))))

aux1 = Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair Zero (Pair (Defer (Pair Zero Zero)) Zero))
aux2 = Pair Zero (Pair Zero Zero)

test_rEval' :: String -> IO String
test_rEval' input = runMain input
  where
    runMain :: String -> IO String
    runMain s = case compileUnitTest <$> parseMain [] s of
      Left e -> error $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop_ $ g
      Right z -> error $ "compilation failed somehow, with result " <> show z

rEvalError = unlines $
  [ "main = \\i -> (0, 0)"
  ]

userDefAdHocTypesSuccess = unlines $
  [ "MyInt = let wrapper = \\h -> ( \\i -> if not i"
  , "                        then \"MyInt must not be 0\""
  , "                   else  i"
  , "           , \\i -> if dEqual (left i)"
  , "                   then 0"
  , "                   else \"expecting MyInt\""
  , "           )"
  , "        in wrapper (# wrapper)"
  , "main = \\i -> ((left MyInt) 8, 0)"
  ]

userDefAdHocTypesFailure = unlines $
  [ "MyInt = let wrapper = \\h -> ( \\i -> if not i"
  , "                        then \"MyInt must not be 0\""
  , "                   else  i"
  , "           , \\i -> if dEqual (left i)"
  , "                   then 0"
  , "                   else \"expecting MyInt\""
  , "           )"
  , "        in wrapper (# wrapper)"
  , "main = \\i -> ((left MyInt) 0, 0)"
  ]



myTrace a = trace (show a) a

dependantTopLevelBindings = unlines $
  [ "f = (0,0)"
  , "g = (0,0)"
  , "h = [f,g,f]"
  ]

-- |Usefull to see if tictactoe.tel was correctly parsed
-- and was usefull to compare with the deprecated Telomare.Parser
-- Parsec implementation
testWtictactoe = do
  preludeFile <- Strict.readFile "Prelude.tel"
  tictactoe <- Strict.readFile "tictactoe.tel"
  let
    prelude = case parsePrelude preludeFile of
                Right p -> p
                Left pe -> error pe
  case parseMain prelude tictactoe of
    Right _ -> return True
    Left _  -> return False

letExpr = unlines $
  [ "let x = 0"
  , "    y = 0"
  , "    f = (x,y)"
  , "in f"
  ]

-- | Telomare Parser AST representation of: \x -> \y -> \z -> [zz1, yy3, yy4, z, zz6]
expr9 = TLam (Closed ("x"))
          (TLam (Open ("y"))
            (TLam (Open ("z"))
              (TPair
                (TVar ("zz1"))
                (TPair
                  (TVar ("yy3"))
                  (TPair
                    (TVar ("yy5"))
                    (TPair
                      (TVar ("z"))
                      (TPair
                        (TVar ("zz6"))
                        TZero)))))))

-- | Telomare Parser AST representation of: \x -> \y -> \z -> [zz, yy0, yy0, z, zz]
expr8 = TLam (Closed ("x"))
          (TLam (Open ("y"))
            (TLam (Open ("z"))
              (TPair
                (TVar ("zz"))
                (TPair
                  (TVar ("yy0"))
                  (TPair
                    (TVar ("yy0"))
                    (TPair
                      (TVar ("z"))
                      (TPair
                        (TVar ("zz"))
                        TZero)))))))

-- | Telomare Parser AST representation of: "\z -> [x,x,y,x,z,y,z]"
expr7 = TLam (Open ("z"))
          (TPair
            (TVar ("x"))
            (TPair
              (TVar ("x"))
              (TPair
                (TVar ("y"))
                (TPair
                  (TVar ("x"))
                  (TPair
                    (TVar ("z"))
                    (TPair
                      (TVar ("y"))
                      (TPair
                        (TVar ("z"))
                        TZero)))))))

-- | Telomare Parser AST representation of: \x -> \y -> \z -> z
expr6 :: Term1
expr6 = TLam (Closed ("x"))
          (TLam (Closed ("y"))
            (TLam (Closed ("z"))
              (TVar ("z"))))

-- | Telomare Parser AST representation of: \x -> (x, x)
expr5 = TLam (Closed ("x"))
          (TPair
            (TVar ("x"))
            (TVar ("x")))

-- | Telomare Parser AST representation of: \x -> \x -> \x -> x
expr4 = TLam (Closed ("x"))
          (TLam (Closed ("x"))
            (TLam (Closed ("x"))
              (TVar ("x"))))

-- | Telomare Parser AST representation of: \x -> \y -> \z -> [x,y,z]
expr3 = TLam (Closed ("x"))
          (TLam (Open ("y"))
            (TLam (Open ("z"))
              (TPair
                (TVar ("x"))
                (TPair
                  (TVar ("y"))
                  (TPair
                    (TVar ("z"))
                    TZero)))))

-- | Telomare Parser AST representation of: \a -> (a, (\a -> (a,0)))
expr2 = TLam (Closed ("a"))
          (TPair
            (TVar ("a"))
            (TLam (Closed ("a"))
              (TPair
                (TVar ("a"))
                TZero)))


-- | Telomare Parser AST representation of: \x -> [x, x, x]
expr1 = TLam (Closed ("x"))
          (TPair
            (TVar ("x"))
            (TPair
              (TVar ("x"))
              (TPair
                (TVar ("x"))
                TZero)))

expr = TLam (Closed ("x"))
         (TLam (Open ("y"))
           (TPair
             (TVar ("x"))
             (TVar ("y"))))

range = unlines
  [ "range = \\a b -> let layer = \\recur i -> if dMinus b i"
  , "                                           then (i, recur (i,0))"
  , "                                           else 0"
  , "                in ? layer (\\i -> 0) a"
  , "r = range 2 5"
  ]

closedLambdaPair = TLam (Closed ("x")) (TLam (Open ("y")) (TPair (TVar ("x")) (TVar ("y"))))

testLetIndentation = unlines
  [ "let x = 0"
  , "    y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation1 = unlines
  [ "let x = 0"
  , "  y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation2 = unlines
  [ "let x = 0"
  , "      y = 1"
  , "in (x,y)"
  ]

testPair0 = "(\"Hello World!\", \"0\")"

testPair1 = unlines
  [ "("
  , " \"Hello World!\""
  , ", \"0\""
  , ")"
  ]

testITE1 = unlines $
  [ "if"
  , "  1"
  , "then 1"
  , "else"
  , "  2"
  ]
testITE2 = unlines $
  [ "if 1"
  , "  then"
  , "                1"
  , "              else 2"
  ]
testITE3 = unlines $
  [ "if 1"
  , "   then"
  , "                1"
  , "              else 2"
  ]
testITE4 = unlines $
  [ "if 1"
  , "    then"
  , "                1"
  , "              else 2"
  ]

testITEwPair = unlines $
  [ "if"
  , "    1"
  , "  then (\"Hello, world!\", 0)"
  , "  else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testCompleteLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.tel"
  case parsePrelude preludeFile of
    Right _ -> return True
    Left _  -> return False

testParseAssignmentwCLwITEwPair2 = unlines $
  [ "main = \\input -> if 1"
  , "                  then"
  , "                   (\"Hello, world!\", 0)"
  , "                  else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair3 = unlines $
  [ "main = \\input ->"
  , "  if 1"
  , "   then"
  , "     (\"Hello, world!\", 0)"
  , "   else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair4 = unlines $
  [ "main = \\input"
  , "-> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair5 = unlines $
  [ "main"
  , "  = \\input"
  , "-> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair6 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair7 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "       then"
  , "             (\"Hello, world!\", 0)"
  , "           else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair1 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "       (\"Hello, world!\", 0)"
  , "     else (\"Goodbye, world!\", 0)"
  ]

testParseTopLevelwCLwITEwPair = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMainwCLwITEwPair = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMain3 = "main = 0"

test4 = "(\\x -> if x then \"f\" else 0)"
test5 = "\\x -> if x then \"f\" else 0"
test6 = "if x then \"1\" else 0"
test7 = unlines $
  [ "if x then \"1\""
  , "else 0"
  ]
test8 = "if x then 1 else 0"

runTestMainwCLwITEwPair = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error pe
  case parseMain prelude testMainwCLwITEwPair of
    Right x  -> return True
    Left err -> return False

testMain2 = "main : (\\x -> if x then \"fail\" else 0) = 0"

runTestMainWType = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error pe
  case parseMain prelude $ testMain2 of
    Right x  -> return True
    Left err -> return False

testList0 = unlines $
  [ "[ 0"
  , ", 1"
  , ", 2"
  , "]"
  ]

testList1 = "[0,1,2]"

testList2 = "[ 0 , 1 , 2 ]"

testList3 = unlines $
  [ "[ 0 , 1"
  , ", 2 ]"
  ]

testList4 = unlines $
  [ "[ 0 , 1"
  , ",2 ]"
  ]

testList5 = unlines $
  [ "[ 0,"
  , "  1,"
  , "  2 ]"
  ]

testITEParsecResult = "TITE (TPair TZero TZero) (TPair TZero TZero) (TPair (TPair TZero TZero) TZero)"

-- TODO: does it matter that one parses succesfuly and the other doesnt?
parseApplied0 = unlines
  [ "foo (bar baz"
  , "     )"
  ]
parseApplied1 = unlines
  [ "foo (bar baz"
  , "         )"
  ]


testShowBoard0 = unlines
  [ "main = or (and validPlace"
  , "                    (and (not winner)"
  , "                         (not filledBoard)))"
  , "          (1)"
  ]

testShowBoard1 = unlines
  [ "main = or (0)"
  , "               (1)"
  ]

testShowBoard2 = unlines
  [ "main = or (and 1"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard3 = unlines
  [ "main = or (and x"
  , "                    0)"
  , "               (1)"
  ]

testLetShowBoard0 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        (and (not winner)"
  , "                             (not filledBoard)"
  , "                        )"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard1 = unlines
  [ "let showBoard = or (0)"
  , "                   (1)"
  , "in 0"
  ]

testLetShowBoard3 = unlines
  [ "or (and 1"
  , "        1"
  , "   )"
  , "   (not boardIn)"
  ]

testLetShowBoard5 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1)"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard2 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard4 = unlines
  [ "main = or (and 0"
  , "                    1)"
  , "               (not boardIn)"
  ]

testLetShowBoard8 = unlines
  [ "or (0"
  , "   )"
  , "   1"
  ]
testLetShowBoard9 = unlines
  [ "or 0"
  , "   1"
  ]

testShowBoard6 = unlines
  [ "or (or x"
  , "       (or 0"
  , "           1))"
  , "   (1)"
  ]

testShowBoard4 = unlines
  [ "main = or (and x"
  , "                    (or 0"
  , "                        (1)))"
  , "               (1)"
  ]

testShowBoard5 = unlines
  [ "main = or (or x"
  , "                   (or 0"
  , "                       1))"
  , "               (1)"
  ]

fiveApp = concat
  [ "main = let fiveApp = $5\n"
  , "       in fiveApp (\\x -> (x,0)) 0"
  ]

showAllTransformations :: String -- ^ Telomare code
                       -> IO ()
showAllTransformations input = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let section description body = do
        putStrLn "\n-----------------------------------------------------------------"
        putStrLn $ "----" <> description <> ":\n"
        putStrLn $ body
      prelude = case parsePrelude preludeFile of
                  Right x  -> x
                  Left err -> error err
      upt = case parseWithPrelude prelude input of
              Right x -> x
              Left x  -> error x
  section "Input" input
  section "UnprocessedParsedTerm" $ show upt
  section "optimizeBuiltinFunctions" $ show . optimizeBuiltinFunctions $ upt
  let optimizeBuiltinFunctionsVar = optimizeBuiltinFunctions upt
      str1 = lines . show $ optimizeBuiltinFunctionsVar
      str0 = lines . show $ upt
      diff = getGroupedDiff str0 str1
  section "Diff optimizeBuiltinFunctions" $ ppDiff diff
  -- let optimizeBindingsReferenceVar = optimizeBindingsReference optimizeBuiltinFunctionsVar
  --     str2 = lines . show $ optimizeBindingsReferenceVar
  --     diff = getGroupedDiff str1 str2
  -- section "optimizeBindingsReference" . show $ optimizeBindingsReferenceVar
  -- section "Diff optimizeBindingsReference" $ ppDiff diff
  let validateVariablesVar = validateVariables prelude optimizeBuiltinFunctionsVar
      str3 = lines . show $ validateVariablesVar
      diff = getGroupedDiff str3 str1
  section "validateVariables" . show $ validateVariablesVar
  section "Diff validateVariables" $ ppDiff diff
  let Right debruijinizeVar = (>>= debruijinize []) validateVariablesVar
      str4 = lines . show $ debruijinizeVar
      diff = getGroupedDiff str4 str3
  section "debruijinize" . show $ debruijinizeVar
  section "Diff debruijinize" $ ppDiff diff
  let splitExprVar = splitExpr debruijinizeVar
      str5 = lines . ppShow $ splitExprVar
      diff = getGroupedDiff str5 str4
  section "splitExpr" . ppShow $ splitExprVar
  section "Diff splitExpr" $ ppDiff diff
  let Just toTelomareVar = toTelomare . findChurchSize $ splitExprVar
      str6 = lines . show $ toTelomareVar
      diff = getGroupedDiff str6 str5
  section "toTelomare" . show $ toTelomareVar
  section "Diff toTelomare" $ ppDiff diff
  putStrLn "\n-----------------------------------------------------------------"
  putStrLn $ "---- stepEval:\n"
  x <- stepIEval toTelomareVar
  print x
  -- let iEvalVar0 = iEval () Zero toTelomareVar

stepIEval :: IExpr -> IO IExpr
stepIEval =
  let wio :: IExpr -> WrappedIO IExpr
      wio = rEval Zero
  in wioIO . wio

data WrappedIO a = WrappedIO
  { wioIO :: IO a
  } deriving (Functor)

instance Show (WrappedIO IExpr) where
  show = show . unsafePerformIO . wioIO

instance Applicative WrappedIO where
  pure = WrappedIO . pure
  (<*>) (WrappedIO f) (WrappedIO a) = WrappedIO $ f <*> a

instance Monad WrappedIO where
  (>>=) (WrappedIO a) f = WrappedIO $ a >>= (wioIO . f)

instance (MonadError RunTimeError) WrappedIO where
  throwError = undefined
  catchError = undefined

-- TODO: Remove
-- iEval :: MonadError RunTimeError m => (IExpr -> IExpr -> m IExpr) -> IExpr -> IExpr -> m IExpr

-- -- |EvalStep :: * -> *
-- type EvalStep = ExceptT RunTimeError IO

-- myIEval :: (IExpr -> IExpr -> EvalStep IExpr) -> IExpr -> IExpr -> EvalStep IExpr
-- myIEval f e g = do
--   liftIO $ print (g, e)
--   iEval f e g

-- Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env)))))
--   ,Left Can't SetEnv: Pair Zero (Pair Zero Zero))


-- Main> pureREval (check zero (completeLam (varN 0)))
-- (Pair (Defer (SetEnv (Pair (SetEnv (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))))) (PRight Env)))) (Pair (Pair (Defer (PLeft Env)) Zero) Zero),Right (Pair (Defer (SetEnv (Pair (SetEnv (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))))) (PRight Env)))) (Pair (Pair (Defer (PLeft Env)) Zero) Zero)))
-- (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env)),Right (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair Zero Zero)))
-- (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))),Right (Pair Zero (Pair Zero Zero)))
-- (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))),Left Can't SetEnv: Pair Zero (Pair Zero Zero))
-- (Pair (SetEnv (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))))) (PRight Env),Left Can't SetEnv: Pair Zero (Pair Zero Zero))
-- Left Can't SetEnv: Pair Zero (Pair Zero Zero)


-- Main> stepIEval (check zero (completeLam (varN 0)))
-- (SetEnv (Pair (Defer (SetEnv (Pair (SetEnv (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))))) (PRight Env)))) (Pair (Pair (Defer (PLeft Env)) Zero) Zero)),Zero)
-- (Pair (Defer (SetEnv (Pair (SetEnv (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))))) (PRight Env)))) (Pair (Pair (Defer (PLeft Env)) Zero) Zero),Zero)
-- (Defer (SetEnv (Pair (SetEnv (Pair Abort (SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env))))) (Pair (PRight Env) (PLeft Env))))))) (PRight Env))),Zero)
-- (Pair (Pair (Defer (PLeft Env)) Zero) Zero,Zero)
-- (Pair (Defer (PLeft Env)) Zero,Zero)
-- (Defer (PLeft Env),Zero)
-- (Zero,Zero)
-- (Zero,Zero)
