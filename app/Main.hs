module Main where

import Data.Char
import SIL
--import SIL.Llvm
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType)
import SIL.Optimizer
import SIL.Eval
import PrettyPrint
import qualified System.IO.Strict as Strict

unitTestType' parse s t tef = case parse s of
  Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
  Right g -> let apt = typeCheck t g
             in do
              putStrLn $ showPIE g
              -- error "whatever"
              if tef apt
                then pure ()
                else putStrLn $ concat [s, " failed typecheck, result ", show apt]

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    testMethod n s = case resolveBinding n <$> parseWithPrelude prelude s of
      Right (Just iexpr) -> simpleEval iexpr >>= \r -> print (PrettyExpr r)
      x -> print x
    runMain s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> evalLoop g
    --testData = Twiddle $ Pair (Pair (Pair Zero Zero) Zero) (Pair Zero Zero)
    --testData = PRight $ Pair (Pair (Pair Zero Zero) Zero) (Pair Zero Zero)
    --testData = SetEnv $ Pair (Defer $ Pair Zero Env) Zero
    testData = ite (Pair Zero Zero) (Pair (Pair Zero Zero) Zero) (Pair Zero (Pair Zero Zero))
    parse = parseMain prelude
    unitTestType = unitTestType' parse

  --print $ makeModule testData
  {-
  runJIT (makeModule testData) >>= \result -> case result of
    Left err -> putStrLn $ concat ["JIT error: ", err]
    Right mod -> putStrLn "JIT seemed to finish ok"
-}

  -- printBindingTypes prelude
  -- Strict.readFile "tictactoe.sil" >>= runMain
  unitTestType "main = {{{{{{{{{{{{{{{{{{{{{{0,0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0},0}" DataOnlyTypeP (== Nothing)
  --runMain "main = #x -> 0"
  --runMain "main = #x -> if x then 0 else {\"Test message\", 0}"
  --runMain "main = #x -> if listEqual (left x) \"quit\" then 0 else {\"type quit to exit\", 1}"
