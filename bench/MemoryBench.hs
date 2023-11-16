{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Data.Char
import           Data.Either
import           GHC.Generics         (Generic)
import           System.IO            (hPutStrLn, stderr)

import qualified System.IO.Strict     as Strict
import           Telomare
import           Telomare.Eval
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker (TypeCheckError (..), inferType,
                                       typeCheck)

import           MemoryBench.Cases
-- import           MemoryBench.LLVM
import           Paths_telomare

import           Text.Parsec.Error    (ParseError)
import qualified Weigh                as Weigh
import           Weigh                hiding (Case, Max)

import           Debug.Trace

-- TODO:
-- Get some expressions/groups of expressions.
-- Measure memory needed to:
--   1. parse and create AST
--   2. compile

-- Compiling is problematic. So... we'll see.

-- Required by Weigh - we do not have access to ParseError's constructor.
instance NFData ParseError where
    rnf a = ()

type Bindings = [(String, UnprocessedParsedTerm)]

processCase :: Bindings -> Case -> Weigh ()
processCase bindings (Case label code) = do
    let e_parsed       = fmap toTelomare $ parseMain bindings code
        (Right (Just parsed)) = e_parsed --Taking advantage of lazy evalutation here
    let parsing = func "parsing" (parseMain bindings) code -- Parsing
        evals   = [ io "simpleEval" benchEvalSimple parsed
                  , io "optimizedEval" benchEvalOptimized parsed
                  ]
        weighs  = if isRight e_parsed
                     then sequence_ (parsing : evals)
                     else parsing
    wgroup label weighs

processAllCases :: Bindings -> [Case] -> Weigh ()
processAllCases bindings cases = mapM_ (processCase bindings) cases

benchEvalSimple :: IExpr -> IO IExpr
benchEvalSimple iexpr = simpleEval (SetEnv (Pair (Defer iexpr) Zero))

benchEvalOptimized :: IExpr -> IO IExpr
benchEvalOptimized iexpr = optimizedEval (SetEnv (Pair (Defer iexpr) Zero))

config :: Config
config = Config [Weigh.Case, Allocated, GCs, Live] "" Plain

main = do
  preludeFile <- Strict.readFile "Prelude.tel"

  let
    e_prelude = parsePrelude preludeFile
    prelude = case e_prelude of
      Right p -> p
      Left pe -> error $ show pe


  cases <- loadCases =<< getDataFileName "bench/MemoryBench/cases"
  mainWith $ setConfig config >> processAllCases prelude cases

