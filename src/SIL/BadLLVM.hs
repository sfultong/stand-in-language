{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SIL.BadLLVM where

import Foreign.Storable
import Control.Monad.State.Strict
import Data.Int (Int64)
import Foreign.Ptr (FunPtr, castFunPtr, castPtrToFunPtr, wordPtrToPtr, Ptr, WordPtr(..), plusPtr, castPtr, nullPtr)
import qualified Data.ByteString.Char8 as ByteString

import LLVM.AST
import LLVM.AST.Global
import LLVM.Context
import LLVM.Module as Mod
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt
import qualified LLVM.Relocation as Reloc

import qualified Data.ByteString as BS
import qualified LLVM.AST as AST
import qualified LLVM.AST.AddrSpace as AddrSpace
import qualified LLVM.AST.Constant as C
import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as OJ
import qualified LLVM.Target as Target

import qualified SIL as SIL

testModule :: AST.Module
testModule = defaultModule
  { moduleDefinitions =
    [ pairHeap, llvmTest2]
  , moduleName = "SILModule"
  }

resolver :: OJ.IRCompileLayer l -> OJ.SymbolResolver
resolver compileLayer = OJ.SymbolResolver
  (\s -> OJ.findSymbol compileLayer s True)
  (\s -> fmap (\a -> OJ.JITSymbol a (OJ.JITSymbolFlags False True)) (Linking.getSymbolAddressInProcess s))

withTargetMachine :: (Target.TargetMachine -> IO a) -> IO a
withTargetMachine f = do
  Target.initializeAllTargets
  triple <- Target.getProcessTargetTriple
  cpu <- Target.getHostCPUName
  features <- Target.getHostCPUFeatures
  (target, _) <- Target.lookupTarget Nothing triple
  Target.withTargetOptions $ \options ->
    Target.withTargetMachine target triple cpu features options Reloc.Default
      -- We need to set the CodeModel to JITDefault to allow for larger relocations
      CodeModel.JITDefault
      CodeGenOpt.Default f

evalJIT :: AST.Module -> IO ()
evalJIT amod = do
  withContext $ \ctx ->
    withModuleFromAST ctx amod $ \mod -> do
      ByteString.putStrLn =<< moduleLLVMAssembly mod
      withTargetMachine $ \tm ->
        OJ.withObjectLinkingLayer $ \objectLayer ->
          OJ.withIRCompileLayer objectLayer tm $ \compileLayer ->
            OJ.withModule compileLayer mod (resolver compileLayer) $ \_ -> do
              mainSymbol <- OJ.mangleSymbol compileLayer $ "main"
              (OJ.JITSymbol mainFn _) <- OJ.findSymbol compileLayer mainSymbol True
              if mainFn == WordPtr 0
                then do
                putStrLn "Could not find main"
                pure $ error "Couldn't find main"
                else do
                  -- Get the pointer to "pair_heap"
                  ptr <- mkMain (castPtrToFunPtr (wordPtrToPtr mainFn))
                  -- Read the value stored at that pointer
                  print =<< (peek (plusPtr nullPtr (fromIntegral ptr)) :: IO Int64)

foreign import ccall "dynamic"
  mkMain :: FunPtr (IO Int64) -> IO Int64

-- name counter, block instruction list (reversed), block name, block list, definition list, definition counter
type FunctionState a = State (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word) a

startFunctionState :: (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word)
startFunctionState = (1, [], UnName 0, [], [], 0)

intT :: Type
intT = IntegerType 64

heapPType :: Type
heapPType = PointerType intT (AddrSpace.AddrSpace 0)

heapN :: Name
heapN = "pair_heap"

pairHeap :: Definition
pairHeap = GlobalDefinition
  $ globalVariableDefaults
  { name = heapN
  , LLVM.AST.Global.type' = intT
  , initializer = Just (C.Int 64 0)
  }

zero :: Operand
zero = ConstantOperand (C.Int 64 0)

doInst :: Instruction -> FunctionState Operand
doInst inst = state $ \(c, l, n, b, d, dc) ->
  if c == maxBound
  then error "BasicBlock instruction limit reached"
  else (LocalReference intT $ UnName c, (c + 1, (UnName c := inst) : l, n, b, d, dc))

doBlock :: Terminator -> FunctionState Name
doBlock term = state $ \(c, l, n, b, d, dc) ->
  if c == maxBound
  then error "BasicBlock limit reached"
  else (n, (c, [], UnName c, BasicBlock n (reverse l) (Do term) : b, d, dc))

heapC :: Operand
heapC = ConstantOperand (C.GlobalReference heapPType heapN)

llvmTest2 :: Definition
llvmTest2 =
  let (_, (_, _, _, blocks, _, _)) = runState testDef startFunctionState
      testDef = do
        failure <- doInst $ PtrToInt heapC intT []
        doBlock (Ret (Just failure) [])
  in GlobalDefinition $ functionDefaults
       { name = "main"
       , parameters = ([], False)
       , returnType = intT
       , basicBlocks = reverse blocks
       }
