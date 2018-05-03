module Main where

import SIL.Serializer
import SIL

import Test.Hspec
import Test.QuickCheck

import Common

serializerSpec :: Spec
serializerSpec = do
   describe "C dynamic representation" $ do
        it "Serializing to C dynamic representation and back will give the same result" $ do
        -- Construct the tree using typeProduct
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                c_rep  <- toC   iexpr
                hs_rep <- fromC c_rep 
                iexpr `shouldBe` hs_rep
                ) 


main :: IO ()
main = hspec serializerSpec


