module Main where

import Data.Char
import SIL
--import SIL.Llvm
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType)
import SIL.Optimizer
import SIL.Eval
import qualified System.IO.Strict as Strict

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ getErrorString pe
    runMain s = case toSIL . findChurchSize <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", e]
      Right (Just g) -> evalLoop $ g
    --testData = Twiddle $ Pair (Pair (Pair Zero Zero) Zero) (Pair Zero Zero)
    --testData = PRight $ Pair (Pair (Pair Zero Zero) Zero) (Pair Zero Zero)
    --testData = SetEnv $ Pair (Defer $ Pair Zero Env) Zero
    testData = ite (Pair Zero Zero) (Pair (Pair Zero Zero) Zero) (Pair Zero (Pair Zero Zero))

  --print $ makeModule testData
  {-
  runJIT (makeModule testData) >>= \result -> case result of
    Left err -> putStrLn $ concat ["JIT error: ", err]
    Right mod -> putStrLn "JIT seemed to finish ok"
-}

  testSBV' >>= print
  -- printBindingTypes prelude
  -- Strict.readFile "tictactoe.sil" >>= runMain
  -- Strict.readFile "hello.sil" >>= runMain
  --runMain "main = #x -> 0"
  --runMain "main = #x -> if x then 0 else (\"Test message\", 0)"
  --runMain "main = #x -> if listEqual (left x) \"quit\" then 0 else (\"type quit to exit\", 1)"
