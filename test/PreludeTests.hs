{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main where

import RefinementTests (assertExprWith, evalWithBindings, loadBindings,
                        refinementTests)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Prelude Tests" [ unitTestsNatArithmetic
                                 , qcPropsNatArithmetic
                                 , refinementTests
                                 ]

-- |Evaluate @expr@ in the scope of @Prelude.tel@ alone.
evalExprString :: String -> IO (Either String String)
evalExprString input = do
  preludeBindings <- loadBindings "Prelude.tel"
  evalWithBindings preludeBindings input

assertExpr :: String -> String -> Assertion
assertExpr = assertExprWith evalExprString

genInt :: Gen Int
genInt = choose (0, 100)

genInt2 :: Gen Int
genInt2 = choose (0, 85)

genInt3 :: Gen Int
genInt3 = choose (0, 15) -- products stay within a byte (Num 255)

genInt4 :: Gen Int
genInt4 = choose (0, 6)

-----------------
------ Unit Tests
-----------------

unitTestsNatArithmetic :: TestTree
unitTestsNatArithmetic = testGroup "Unit tests on natural arithmetic expresions"
  [ testCase "test addition" $ assertExpr "plusByte 1 2" (show (1 + 2 :: Integer))
  , testCase "test subtraction" $ assertExpr "minusByte 5 3" (show (5 - 3 :: Integer))
  , testCase "test substraction lower limit" $ assertExpr "minusByte 0 1" "0"
  , testCase "test multiplication" $ assertExpr "timesByte 3 4" (show (3 * 4 :: Integer))
  , testCase "test division" $ assertExpr "dDiv 8 2" (show (8 `div` 2 :: Integer))
  , testCase "test division by zero" $ assertExpr "dDiv 1 0" "check failed on 0"
  , testCase "test equality" $ assertExpr "dEqual 3 3" "1"
  , testCase "test inequality" $ assertExpr "dEqual 3 4" "0"
  , testCase "test modulo" $ assertExpr "modByte 10 3" (show (10 `mod` 3 :: Integer))
  , testCase "test gcd" $ assertExpr "gcd 48 18" (show (gcd 48 18 :: Integer))
  , testCase "test lcm" $ assertExpr "lcm 12 15" (show (lcm 12 15 :: Integer))
  , testCase "test exponentiation" $ assertExpr "powByte 2 3" (show (2 ^ (3 :: Integer) :: Integer))
  , testCase "test exponentiation with zero exponent" $ assertExpr "powByte 5 0" "1"
  , testCase "test raise zero to the zero power" $ assertExpr "powByte 0 0" "1"
  ]

---------------------
------ Property Tests
---------------------

qcPropsNatArithmetic :: TestTree
qcPropsNatArithmetic = testGroup "Property tests on natural arithmetic expressions (QuickCheck)"
  [ QC.testProperty "Commutative Additive" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt
        y <- generate genInt
        res <- evalExprString
                 ( "dEqual (plusByte " <> show x <> " " <> show y <>
                   ") (plusByte " <> show y <> " " <> show x <> ")" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Associative Additive" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt2
        y <- generate genInt2
        z <- generate genInt2
        res <- evalExprString
                 ( "dEqual (plusByte (plusByte " <> show x <> " " <> show y
                 <> ")" <> show z <> ") (plusByte " <> show x <> "(plusByte "
                 <> show y <> " " <> show z <>"))" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Neutral Additive" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x   <- generate genInt
        res <- evalExprString ("plusByte " <> show x <> " 0")
        pure $ case res of
          Left err  -> err === show x
          Right val -> val === show x
  , QC.testProperty "Commutative Multiplicative" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt3
        y <- generate genInt3
        res <- evalExprString
                 ( "dEqual (timesByte " <> show x <> " " <> show y <>
                   ") (timesByte " <> show y <> " " <> show x <> ")" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Associative Multiplicative" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt4
        y <- generate genInt4
        z <- generate genInt4
        res <- evalExprString
                 ( "dEqual (timesByte (timesByte " <> show x <> " " <> show y
                 <> ")" <> show z <> ") (timesByte " <> show x <> "(timesByte "
                 <> show y <> " " <> show z <>"))" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Neutral Multiplicative" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x   <- generate genInt
        res <- evalExprString ("timesByte " <> show x <> " 1")
        pure $ case res of
          Left err  -> err === show x
          Right val -> val === show x
  ]

