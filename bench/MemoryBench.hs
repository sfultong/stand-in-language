{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified SIL.Llvm as LLVM
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (typeCheck, inferType, TypeCheckError(..))
import SIL.Optimizer
import SIL.Eval
import qualified System.IO.Strict as Strict

import LLVM.AST
import LLVM.AST.DataLayout
import LLVM.AST.ThreadLocalStorage
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.Visibility
import LLVM.AST.DLL
import LLVM.AST.Type
import LLVM.AST.Constant
import LLVM.AST.AddrSpace
import LLVM.AST.Float
import LLVM.AST.IntegerPredicate
import LLVM.AST.FloatingPointPredicate
import LLVM.AST.ParameterAttribute
import LLVM.AST.RMWOperation
import LLVM.AST.InlineAssembly

import LLVM.AST.Operand
import LLVM.AST.FunctionAttribute
import LLVM.AST.COMDAT

import Cases
import Paths_sil

import Weigh hiding (Case, Max)
import qualified Weigh as Weigh
import Text.Parsec.Error (ParseError)
-- TODO:
-- Get some expressions/groups of expressions.
-- Measure memory needed to:
--   1. parse and create AST
--   2. compile

-- Compiling is problematic. So... we'll see.

-- Required by Weigh - we do not have access to ParseError's constructor.
instance NFData ParseError where
    rnf a = ()

instance NFData DataLayout
instance NFData Endianness
instance NFData Mangling
instance NFData AddrSpace
instance NFData AlignmentInfo
instance NFData AlignType

instance NFData Definition
instance NFData Global
instance NFData Linkage
instance NFData Visibility
instance NFData StorageClass
instance NFData Model
instance NFData UnnamedAddr
instance NFData CallingConvention
instance NFData ParameterAttribute
instance NFData Parameter
instance NFData BasicBlock

instance NFData Constant
instance NFData SomeFloat
instance NFData IntegerPredicate
instance NFData FloatingPointPredicate

instance NFData Type
instance NFData FloatingPointType

instance NFData a => NFData (Named a)
instance NFData Instruction
instance NFData FastMathFlags
instance NFData SynchronizationScope
instance NFData Terminator
instance NFData MemoryOrdering
instance NFData RMWOperation
instance NFData InlineAssembly
instance NFData TailCallKind
instance NFData Dialect
instance NFData LandingPadClause

instance NFData Name
instance NFData MetadataNodeID
instance NFData Metadata
instance NFData MetadataNode
instance NFData Operand
instance NFData GroupID
instance NFData FunctionAttribute
instance NFData SelectionKind


instance NFData Module


processCase :: Bindings -> Case -> Weigh ()
processCase bindings (Case label code) = do
    let e_parsed       = parseMain bindings code
        (Right parsed) = e_parsed --Taking advantage of lazy evalutation here
        parsing = func "parsing" (parseMain bindings) code -- Parsing
        evals   = [ io "simpleEval" benchEvalSimple parsed
                  , io "fasterEval" benchEvalFaster parsed
                  , io "optimizedEval" benchEvalOptimized parsed
                  , benchLLVMDetails parsed
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

benchEvalMyllvm :: IExpr -> IO IExpr
benchEvalMyllvm iexpr = myllvmEval (SetEnv (Pair (Defer iexpr) Zero))

config :: Config
config = Config [Weigh.Case, Allocated, GCs, Live] "" Plain

benchLLVMDetails :: IExpr -> Weigh ()
benchLLVMDetails iexpr = do
    let wrap_iexpr = SetEnv (Pair (Defer iexpr) Zero)
        lmod = LLVM.makeModule wrap_iexpr
    sequence_ [ func "---------------" id              ()
              , func "LLVM.makeModule" LLVM.makeModule wrap_iexpr
              , io   "LLVM.evalJIT"    LLVM.evalJIT    lmod
              ]


myllvmEval :: IExpr -> IO IExpr
myllvmEval iexpr = do
  let lmod = LLVM.makeModule iexpr
  result <- catch (LLVM.evalJIT lmod) $ \(e :: SomeException) -> pure . Left $ show e
  case result of
    Left s -> do
      hPutStrLn stderr . show $ iexpr
      hPutStrLn stderr $ "failed llvmEval: " ++ s
      fail s
    Right x -> do
      pure x

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    e_prelude = parsePrelude preludeFile
    prelude = case e_prelude of
      Right p -> p
      Left pe -> error $ show pe


  cases <- loadCases =<< getDataFileName "bench/cases/funs"
  mainWith $ setConfig config >> processAllCases prelude cases

