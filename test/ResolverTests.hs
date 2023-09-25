{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Main where

import CaseTests (qcPropsCase, unitTestsCase)
import Common
import Control.Monad.Except (ExceptT, MonadError, catchError, runExceptT,
                             throwError)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import System.IO
import qualified System.IO.Strict as Strict
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.IO
import System.Posix.Process
import System.Posix.Types
import Telomare
import Telomare.Eval
import Telomare.Parser
import Telomare.Resolver
import Telomare.RunTime
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Megaparsec (eof)
import Text.Show.Pretty (ppShow)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, qcProps, unitTestsCase, qcPropsCase]

---------------------
------ Property Tests
---------------------

qcProps = testGroup "Property tests (QuickCheck)"
  [ QC.testProperty "Arbitrary UnprocessedParsedTerm to test hash uniqueness of HashUP's" $
      \x -> withMaxSuccess 16 $
        containsTHash x QC.==> checkAllHashes . generateAllHashes $ x
  , QC.testProperty "See that generateAllHashes only changes HashUP to ListUP" $
      \x -> withMaxSuccess 16 $
        containsTHash x QC.==> onlyHashUPsChanged x
  ]

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

-----------------
------ Unit Tests
-----------------

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "different values get different hashes" $ do
      let res1 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest0
          res2 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest1
      (res1 == res2) `compare` False @?= EQ
  , testCase "same functions have the same hash even with different variable names" $ do
     let res1 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest2
         res2 = generateAllHashes <$> runTelomareParser2Term2 parseLet [] hashtest3
     res1 `compare` res2  @?= EQ
  , testCase "Ad hoc user defined types success" $ do
      res <- testUserDefAdHocTypes userDefAdHocTypesSuccess
      res `compare` "\a\ndone\n" @?= EQ
  , testCase "Ad hoc user defined types failure" $ do
      res <- testUserDefAdHocTypes userDefAdHocTypesFailure
      res `compare` "MyInt must not be 0\ndone\n" @?= EQ
  , testCase "test automatic open close lambda" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> (x, y)"
      validateVariables [] res `compare` Right closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 2" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x y -> (x, y)"
      validateVariables [] res `compare` Right closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 3" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> z"
      validateVariables [] res `compare` Right expr6 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> (x, x)"
      validateVariables [] res `compare` Right expr5 @?= EQ
  , testCase "test automatic open close lambda 5" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\x -> \\x -> x"
      validateVariables [] res `compare` Right expr4 @?= EQ
  , testCase "test automatic open close lambda 6" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> [x,y,z]"
      validateVariables [] res `compare` Right expr3 @?= EQ
  , testCase "test automatic open close lambda 7" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\a -> (a, (\\a -> (a,0)))"
      validateVariables [] res `compare` Right expr2 @?= EQ
  , testCase "test tictactoe.tel" $ do
      res <- tictactoe
      fullRunTicTacToeString `compare` res  @?= EQ
  ]

tictactoe :: IO String
tictactoe = do
  telomareString <- Strict.readFile "tictactoe.tel"
  runTelomare telomareString $ \(pid, hIn, hOut, hErr) -> do
      hPutStrLn hIn "1"
      hFlush hIn
      hPutStrLn hIn "9"
      hFlush hIn
      hPutStrLn hIn "2"
      hFlush hIn
      hPutStrLn hIn "8"
      hFlush hIn
      hPutStrLn hIn "3"
      hFlush hIn

fullRunTicTacToeString = unlines
  [ "1|2|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|9"
  , "Player 2's turn"
  , "please input number of square: "
  , "O|2|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|9"
  , "Player 1's turn"
  , "please input number of square: "
  , "O|2|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|X"
  , "Player 2's turn"
  , "please input number of square: "
  , "O|O|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|X"
  , "Player 1's turn"
  , "please input number of square: "
  , "O|O|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|X|X"
  , "Player 2's turn"
  , "please input number of square: "
  , "Player 2 wins!"
  , "done"
  ]

-- | Telomare Parser AST representation of: \x -> \y -> \z -> z
expr6 :: Term1
expr6 = TLam (Closed "x")
          (TLam (Closed "y")
            (TLam (Closed "z")
              (TVar "z")))

-- | Telomare Parser AST representation of: \x -> (x, x)
expr5 = TLam (Closed "x")
          (TPair
            (TVar "x")
            (TVar "x"))

-- | Telomare Parser AST representation of: \x -> \x -> \x -> x
expr4 = TLam (Closed "x")
          (TLam (Closed "x")
            (TLam (Closed "x")
              (TVar "x")))

-- | Telomare Parser AST representation of: \x -> \y -> \z -> [x,y,z]
expr3 = TLam (Closed "x")
          (TLam (Open "y")
            (TLam (Open "z")
              (TPair
                (TVar "x")
                (TPair
                  (TVar "y")
                  (TPair
                    (TVar "z")
                    TZero)))))

-- | Telomare Parser AST representation of: \a -> (a, (\a -> (a,0)))
expr2 = TLam (Closed "a")
          (TPair
            (TVar "a")
            (TLam (Closed "a")
              (TPair
                (TVar "a")
                TZero)))

closedLambdaPair = TLam (Closed "x") (TLam (Open "y") (TPair (TVar "x") (TVar "y")))

testUserDefAdHocTypes :: String -> IO String
testUserDefAdHocTypes input = do
  preludeString <- Strict.readFile "Prelude.tel"
  (_, _, hOut, _) <- forkWithStandardFds $ runMain preludeString input
  hGetContents hOut

userDefAdHocTypesSuccess = unlines
  [ "MyInt = let wrapper = \\h -> ( \\i -> if not i"
  , "                                      then \"MyInt must not be 0\""
  , "                                      else  i"
  , "                             , \\i -> if dEqual (left i) h"
  , "                                      then 0"
  , "                                      else \"expecting MyInt\""
  , "                             )"
  , "        in wrapper (# wrapper)"
  , "main = \\i -> ((left MyInt) 8, 0)"
  ]

userDefAdHocTypesFailure = unlines
  [ "MyInt = let wrapper = \\h -> ( \\i -> if not i"
  , "                                      then \"MyInt must not be 0\""
  , "                                      else  i"
  , "                             , \\i -> if dEqual (left i) h"
  , "                                      then 0"
  , "                                      else \"expecting MyInt\""
  , "                             )"
  , "        in wrapper (# wrapper)"
  , "main = \\i -> ((left MyInt) 0, 0)"
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

-- TODO: do something with this
showAllTransformations :: String -- ^ Telomare code
                       -> IO ()
showAllTransformations input = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let section description body = do
        putStrLn "\n-----------------------------------------------------------------"
        putStrLn $ "----" <> description <> ":\n"
        putStrLn body
      prelude = case parsePrelude preludeFile of
                  Right x  -> x
                  Left err -> error err
      upt = case parseWithPrelude prelude input of
              Right x -> x
              Left x  -> error x
  section "Input" input
  section "UnprocessedParsedTerm" $ show upt
  section "optimizeBuiltinFunctions" . show . optimizeBuiltinFunctions $ upt
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
  let Right (Just toTelomareVar) = fmap toTelomare . findChurchSize $ splitExprVar
      str6 = lines . show $ toTelomareVar
      diff = getGroupedDiff str6 str5
  section "toTelomare" . show $ toTelomareVar
  section "Diff toTelomare" $ ppDiff diff
  putStrLn "\n-----------------------------------------------------------------"
  putStrLn "---- stepEval:\n"
  x <- stepIEval toTelomareVar
  print x
  -- let iEvalVar0 = iEval () Zero toTelomareVar

stepIEval :: IExpr -> IO IExpr
stepIEval =
  let wio :: IExpr -> WrappedIO IExpr
      wio = rEval Zero
  in wioIO . wio

newtype WrappedIO a = WrappedIO
  { wioIO :: IO a
  } deriving (Functor)

instance Show (WrappedIO IExpr) where
  show = show . unsafePerformIO . wioIO

instance Applicative WrappedIO where
  pure = WrappedIO . pure
  (<*>) (WrappedIO f) (WrappedIO a) = WrappedIO $ f <*> a

instance Monad WrappedIO where
  (>>=) (WrappedIO a) f = WrappedIO $ a >>= wioIO . f

instance (MonadError RunTimeError) WrappedIO where
  throwError = undefined
  catchError = undefined
