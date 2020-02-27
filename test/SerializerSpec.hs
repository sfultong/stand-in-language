module Main where

import SIL.Serializer.C
import SIL.Serializer
import SIL

import Foreign.Marshal.Alloc

import Test.Hspec
import Test.QuickCheck

import Common

serializerSpec :: Spec
serializerSpec = do
   describe "C dynamic representation" $ do
        it "Serializing to C dynamic representation and back will give the same result" $ do
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                c_rep  <- toC   iexpr
                hs_rep <- fromC c_rep 
                sil_free c_rep
                hs_rep `shouldBe` iexpr
                ) 
   describe "Vector serialization" $ do
        it "Serializing to Vector Word8 and back will give the same result" $ do
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                    serialized   = serialize iexpr
                    deserialized = unsafeDeserialize serialized
                deserialized `shouldBe` iexpr
                ) 
   describe "C FFI and Haskell" $ do
        it "IExpr -> Vector Word8 -> SIL_Serialized -> Vector Word8 -> IExpr: IExprs will be the same" $ do
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                    serialized   = serialize iexpr
                ptr_serialized <- serializedToC serialized
                serialized2 <- serializedFromC ptr_serialized
                let deserialized = unsafeDeserialize serialized2
                free ptr_serialized
                deserialized `shouldBe` iexpr
                ) 
        it "IExpr -> CRep -> SIL_Serialized -> CRep -> IExpr: IExprs will be the same" $ do
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                c_rep <- toC iexpr
                c_serialized <- sil_serialize c_rep
                c_deserialized <- sil_deserialize c_serialized
                hs_rep <- fromC c_deserialized
                sil_free c_deserialized
                free c_serialized
                hs_rep `shouldBe` iexpr
                )
        it "IExpr -> Vector Word8 -> SIL_Serialized -> CRep -> IExpr: IExprs will be the same" $ do
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                    serialized   = serialize iexpr
                ptr_serialized <- serializedToC serialized
                c_deserialized <- sil_deserialize ptr_serialized
                hs_rep         <- fromC c_deserialized
                sil_free c_deserialized
                free ptr_serialized
                hs_rep `shouldBe` iexpr
                ) 
        it "IExpr -> CRep -> SIL_Serialized -> Vector Word8 -> IExpr: IExprs will be the same" $ do
            property (\test_iexpr -> do
                let (TestIExpr iexpr) = test_iexpr
                c_rep <- toC iexpr
                ptr_serialized <- sil_serialize c_rep
                serialized2 <- serializedFromC ptr_serialized
                let deserialized = unsafeDeserialize serialized2
                sil_free c_rep
                free ptr_serialized
                deserialized `shouldBe` iexpr
                ) 

main :: IO ()
--main = hspec serializerSpec
main = pure ()


