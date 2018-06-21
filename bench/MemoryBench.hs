{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveGeneric       #-}
module Main where

import Data.Char
import Data.Either
import Control.Applicative
import Control.Monad
import Control.DeepSeq
import Control.Exception
import System.IO (hPutStrLn, stderr)
import GHC.Generics (Generic)

import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType, TypeCheckError(..))
import SIL.Optimizer
import SIL.Eval
import qualified System.IO.Strict as Strict

import MemoryBench.LLVM
import MemoryBench.Cases
import Paths_sil

import Weigh hiding (Case, Max)
import qualified Weigh as Weigh
import Text.Parsec.Error (ParseError)

import Debug.Trace

-- TODO:
-- Get some expressions/groups of expressions.
-- Measure memory needed to:
--   1. parse and create AST
--   2. compile

-- Compiling is problematic. So... we'll see.

-- Required by Weigh - we do not have access to ParseError's constructor.
instance NFData ParseError where
    rnf a = ()


processCase :: Bindings -> Case -> Weigh ()
processCase bindings (Case label code) = do
    let e_parsed       = parseMain bindings code
        (Right parsed) = e_parsed --Taking advantage of lazy evalutation here
        details = benchLLVMDetails parsed
    let parsing = func "parsing" (parseMain bindings) code -- Parsing
        evals   = [ io "simpleEval" benchEvalSimple parsed
                  , io "fasterEval" benchEvalFaster parsed
                  , io "optimizedEval" benchEvalOptimized parsed
                  , details
                  ]
        weighs  = if isRight e_parsed 
                     then sequence_ (parsing : evals) 
                     else parsing
    wgroup label weighs
        
processAllCases :: Bindings -> [Case] -> Weigh ()
processAllCases bindings cases = mapM_ (processCase bindings) cases 

benchEvalSimple :: IExpr -> IO IExpr
benchEvalSimple iexpr = simpleEval (SetEnv (Pair (Defer iexpr) Zero))

benchEvalFaster :: IExpr -> IO IExpr
benchEvalFaster iexpr = fasterEval (SetEnv (Pair (Defer iexpr) Zero))

benchEvalOptimized :: IExpr -> IO IExpr
benchEvalOptimized iexpr = optimizedEval (SetEnv (Pair (Defer iexpr) Zero))

config :: Config
config = Config [Weigh.Case, Allocated, GCs, Live] "" Plain

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    e_prelude = parsePrelude preludeFile
    prelude = case e_prelude of
      Right p -> p
      Left pe -> error $ show pe


  cases <- loadCases =<< getDataFileName "bench/MemoryBench/cases"
  mainWith $ setConfig config >> processAllCases prelude cases

