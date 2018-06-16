module Main where

import Data.Char
import Data.Either
import Control.Applicative

import SIL
--import SIL.Llvm
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType, TypeCheckError(..))
import SIL.Optimizer
import SIL.Eval
import qualified System.IO.Strict as Strict

import Cases
import Paths_sil

import Weigh

-- TODO:
-- Get some expressions/groups of expressions.
-- Measure memory needed to:
--   1. parse and create AST
--   2. compile

-- Compiling is problematic. So... we'll see.

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _ = False

unitTests unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  (
  [ unitTestType "main = \\x -> {x,0}" (PairType (ArrType ZeroType ZeroType) ZeroType) (== Nothing)
  , unitTestType "main = \\x -> {x,0}" ZeroType isInconsistentType
  , unitTestType "main = succ 0" ZeroType (== Nothing)
  , unitTestType "main = succ 0" (ArrType ZeroType ZeroType) isInconsistentType
  , unitTestType "main = or 0" (PairType (ArrType ZeroType ZeroType) ZeroType) (== Nothing)
  , unitTestType "main = or 0" ZeroType isInconsistentType
  , unitTestType "main = or succ" (ArrType ZeroType ZeroType) isInconsistentType
  , unitTestType "main = 0 succ" ZeroType isInconsistentType
  , unitTestType "main = 0 0" ZeroType isInconsistentType
  , unitTest2 "main = succ 1" "2"
  , unitTest2 "main = plus $3 $2 succ 0" "5"
  , unitTest2 "main = times $3 $2 succ 0" "6"
  , unitTest2 "main = pow $3 $2 succ 0" "8"
  , unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
  , unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
  ])


testEval :: IExpr -> IO IExpr
testEval iexpr = optimizedEval (SetEnv (Pair (Defer iexpr) Zero))

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    e_prelude = parsePrelude preludeFile
    prelude = case e_prelude of
      Right p -> p
      Left pe -> error $ show pe

    unitTest2 s r = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> do
          evaluated <- (testEval g)
          
          let action True  = return True
              action False = (putStrLn $ concat [s, " result ", pretty]) >> return False
              pretty = (show . PrettyIExpr) $ evaluated
          -- putStrLn $ concat [show pretty, " vs ", show evaluated, "\nfrom ", show g]
          action $ pretty == r

    unitTestType s t tef = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> do
          let apt   = typeCheck t g
              error = putStrLn $ concat [s, " failed typecheck, result ", show apt] 
              action True  = return True
              action False = error >> return False 
          print g
          action $ tef apt

  filepath <- getDataFileName "bench/cases/funs"
  cases <- loadCases filepath
  print cases

  putStrLn "Parsing prelude..."
  print $ isRight e_prelude
  bench_code <- Strict.readFile "bench.sil"
  result <- unitTests unitTest2 unitTestType
  print result
