module Main where

import Data.Char
import Data.Either
import SIL
--import SIL.Llvm
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType)
import SIL.Optimizer
import SIL.Eval
import qualified System.IO.Strict as Strict

-- TODO:
-- Get some expressions/groups of expressions.
-- Measure memory needed to:
--   1. parse and create AST
--   2. compile

-- Compiling is problematic. So... we'll see.

main = do
  preludeFile <- Strict.readFile "SlimPrelude.sil"

  let
    e_prelude = parsePrelude preludeFile
    prelude = case e_prelude of
      Right p -> p
      Left pe -> error $ show pe
    testMethod n s = case resolveBinding n <$> parseWithPrelude prelude s of
      Right (Just iexpr) -> simpleEval iexpr >>= \r -> print (PrettyIExpr r)
      x -> print x
    runMain s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> evalLoop g
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

  -- printBindingTypes prelude
  putStrLn "Parsing prelude..."
  print $ isRight e_prelude
  bench_code <- Strict.readFile "bench.sil"
  let e_bench_parsed       = parseMain prelude bench_code
      (Right bench_parsed) = e_bench_parsed
  if isRight e_bench_parsed 
      then print bench_parsed >> evalLoop bench_parsed
      else return ()
