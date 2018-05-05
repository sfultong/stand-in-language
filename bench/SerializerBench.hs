{-#LANGUAGE StandaloneDeriving #-}
module Main where

import Control.DeepSeq
import Data.Char
import qualified Data.Vector.Storable as S

import Foreign.Marshal.Alloc


import Criterion.Main
import Criterion.Types
import Criterion.Measurement


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

import System.Mem

performTests :: IExpr -> IO ()
performTests iexpr = do
    let serialized = serialize iexpr
        len = S.length serialized
    serialized `deepseq` putStrLn $ "GC stats:"
    performGC
    print =<< getGCStatistics
    putStrLn $ "The vector contains " ++ show len ++ " bytes."
    c_rep        <- toC iexpr  
    c_serialized <- serializedToC serialized

    defaultMain $ 
      [ bgroup "Vector"
        [ bench "serialization"   $ nf serialize   iexpr
        , bench "deserialization" $ nf deserialize serialized
        ]
      , bgroup "CRep"
        [ bench "serialization"   $ nfIO (toC   iexpr)
        , bench "deserialization" $ nfIO (fromC c_rep)
        ] 
      , bgroup "SIL_Serialized"
        [ bench "from Vector"   $ nfIO (free =<< serializedToC   serialized)
        , bench "to Vector" $ nfIO (serializedFromC c_serialized)
        , bench "from CRep" $ nfIO (free =<< sil_serialize c_rep)
        , bench "to CRep" $ nfIO (sil_deserialize c_serialized)
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
