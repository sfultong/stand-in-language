module Main where

import Data.Char
import qualified Data.Vector.Storable as S

import Criterion.Main
import Criterion.Types

import SIL
--import SIL.Llvm
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType)
import SIL.Optimizer
import SIL.Eval
import SIL.Serializer
import SIL.Serializer.C
import qualified System.IO.Strict as Strict

performTests :: IExpr -> IO ()
performTests iexpr = do
    let serialized = serialize iexpr
        len = S.length serialized
    c_rep        <- toC iexpr  
    c_serialized <- serializedToC serialized
    putStrLn $ "The vector contains " ++ show len ++ " bytes."
    defaultMain $ 
      [ bgroup "Vector Word8"
        [ bench "serialization"   $ nf serialize   iexpr
        , bench "deserialization" $ whnf deserialize serialized
        ]
      , bgroup "C dynamic representation"
        [ bench "serialization"   $ nfIO   (toC   iexpr)
        , bench "deserialization" $ whnfIO (fromC c_rep)
        ]
      , bgroup "Vector <-> SIL_Serialized"
        [ bench "to SIL_Serialized"   $ nfIO (serializedToC   iexpr)
        , bench "from SIL_Serialized" $ nfIO (serializedFromC c_serialized)
        ]
      ]


main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    runMain s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> performTests g

  Strict.readFile "tictactoe.sil" >>= runMain
