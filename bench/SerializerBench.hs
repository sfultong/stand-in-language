module Main where

import Control.DeepSeq
import Data.Char
import qualified Data.Vector.Storable as S

import Foreign.Marshal.Alloc


import Criterion.Main
import Criterion.Measurement
import Criterion.Types


import Telomare
--import Telomare.Llvm
import qualified System.IO.Strict as Strict
import Telomare.Eval
import Telomare.Optimizer
import Telomare.Parser
import Telomare.RunTime
import Telomare.Serializer
import Telomare.Serializer.C
import Telomare.TypeChecker (inferType, typeCheck)

import System.Mem

performTests :: IExpr -> IO ()
performTests iexpr = do
    let serialized = serialize iexpr
        len = S.length serialized
    serialized `deepseq` putStrLn $ "GC stats:"
    performGC
    print =<< getGCStatistics
    putStrLn ("The vector contains " <> (show len <> " bytes."))
    c_rep        <- toC iexpr
    c_serialized <- serializedToC serialized

    defaultMain
      [ bgroup "Vector"
        [ bench "serialization"   $ nf serialize   iexpr
        , bench "deserialization" $ nf deserialize serialized
        ]
      , bgroup "CRep"
        [ bench "serialization"   $ nfIO (toC   iexpr)
        , bench "deserialization" $ nfIO (fromC c_rep)
        ]
      , bgroup "Telomare_Serialized"
        [ bench "from Vector"   $ nfIO (free =<< serializedToC   serialized)
        , bench "to Vector" $ nfIO (serializedFromC c_serialized)
        , bench "from CRep" $ nfIO (free =<< telomare_serialize c_rep)
        , bench "to CRep" $ nfIO (telomare_deserialize c_serialized)
        ]
      ]


main = do
  preludeFile <- Strict.readFile "Prelude.tel"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    runMain s = case parseMain prelude s of
      Left e  -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> performTests g

  Strict.readFile "tictactoe.tel" >>= runMain
