{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SIL.Llvm where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Data
import Data.Int (Int64)
import Data.String (fromString)
import Debug.Trace
import Foreign.Ptr (FunPtr, castFunPtr, castPtrToFunPtr, wordPtrToPtr, Ptr, WordPtr(..), plusPtr, castPtr)
import Foreign.Storable (peek)
import System.Clock
import System.IO (hPutStrLn, stderr)
import Text.Printf

import LLVM.AST hiding (Monotonic)
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.Context
import LLVM.Module as Mod

import qualified Data.ByteString.Char8 as BSC
import qualified LLVM.AST as AST
import qualified LLVM.AST.AddrSpace as AddrSpace
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Global as G
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.CodeGenOpt as CodeGenOpt
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as OJ
import qualified LLVM.OrcJIT.CompileLayer as OJ
import qualified LLVM.Relocation as Reloc
import qualified LLVM.Target as Target


import LLVM.PassManager

import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Internal.SnocList
import qualified LLVM.IRBuilder.Instruction as IRI
import qualified LLVM.IRBuilder.Constant as IRC
import qualified LLVM.IRBuilder.Module as IRM

import Naturals

import Debug.Trace

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Int64)) -> IO (Ptr Int64)

run :: JITConfig -> WordPtr -> IO (Int64, [(Int64,Int64)])
run jitConfig fn = do
  let
    mungedPtr :: FunPtr (IO (Ptr Int64))
    mungedPtr = castPtrToFunPtr . wordPtrToPtr $ fn
  result <- haskFun mungedPtr
  debugLog jitConfig "finished evaluation"
  numPairs <- peek result
  resultPair <- peek (plusPtr result 8)
  startHeap <- peek (plusPtr result 16)
  let readPair (addr,l) _ = do
        lp <- peek addr
        rp <- peek $ plusPtr addr 8
        pure (plusPtr addr 16, (lp,rp):l)
  pairs <- (reverse . snd) <$> foldM readPair (startHeap, []) [1..numPairs]
  pure (resultPair, pairs)

convertPairs :: (Int64, [(Int64,Int64)]) -> NExpr
convertPairs (x, pairs)=
  let convertPair 0 = NZero
      convertPair n = let (l,r) = pairs !! fromIntegral n
                      in NPair (convertPair l) (convertPair r)
  in convertPair x

makeModule :: NExpr -> AST.Module
makeModule iexpr = flip evalState startBuilderInternal . buildModuleT "SILModule" $ do
  mapM_ emitDefn [pairHeap, heapIndex, resultStructure]

  -- | Load the first element of the pair pointed to by the argument.
  IRM.function "goLeft" [(intT, ParameterName "x")] intT $ \[x] -> do
    la <- IRI.gep heapC [zero, x, zero32]
    l <- IRI.load la 0
    emitTerm (Ret (Just l) [])

  -- | Load the second element of the pair pointed to by the argument.
  IRM.function "goRight" [(intT, ParameterName "x")] intT $ \[x] -> do
    la <- IRI.gep heapC [zero, x, one32]
    l <- IRI.load la 0
    emitTerm (Ret (Just l) [])

  IRM.extern "w_setjmp" [] intT
  IRM.extern "w_longjmp" [intT] VoidType

  IRM.function "main" [] (PointerType resultStructureT (AddrSpace.AddrSpace 0))
    $ \_ -> do
        -- wrap the evaluation of iexpr in a setjmp branch, so that an abort instruction can return for an early exit
        preludeB <- freshUnName
        emitBlockStart preludeB
        jumped <- IRI.call (ConstantOperand (C.GlobalReference setjmpT "w_setjmp")) []
        mainB <- freshUnName
        exitB <- freshUnName
        brCond <- IRI.icmp IP.EQ jumped zero
        emitTerm (CondBr brCond mainB exitB [])

        emitBlockStart mainB
        mainExp <- toLLVM iexpr
        endMainB <- currentBlock
        emitTerm (Br exitB [])

        emitBlockStart exitB
        result <- IRI.phi [(mainExp, endMainB), (jumped, preludeB)]
        heapC <- IRI.load heapIndexC 0
        numPairs <- IRI.gep resultC [zero, zero32]
        resultPair <- IRI.gep resultC [zero, one32]
        heapStart <- IRI.gep resultC [zero, two32]
        IRI.store numPairs 0 heapC
        IRI.store resultPair 0 result
        IRI.store heapStart 0 (ConstantOperand (C.PtrToInt (C.GlobalReference heapPType heapN) intT))
        emitTerm (Ret (Just resultC) [])

data DebugModule = DebugModule AST.Module

instance Show DebugModule where
  show (DebugModule m) = concatMap showDefinition $ moduleDefinitions m
    where showDefinition (GlobalDefinition f@(Function _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) = displayFunction f
          showDefinition _ = ""
          displayFunction f = concat [show (name f), "\n", (concatMap displayBlock (basicBlocks f)), "\n"]
          displayBlock (BasicBlock n inst term) =
            concat ["  ", show n, "\n", concatMap displayInstruction inst, "    ", show term, "\n"]
          displayInstruction i = concat ["    ", show i, "\n"]

resolver :: OJ.CompileLayer l => l -> OJ.SymbolResolver
resolver compileLayer = OJ.SymbolResolver
  (\s -> OJ.findSymbol compileLayer s True)
  (\s -> fmap (\a -> Right $ OJ.JITSymbol a (OJ.defaultJITSymbolFlags { OJ.jitSymbolExported = True })) (Linking.getSymbolAddressInProcess s))

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

debugLog :: JITConfig -> String -> IO ()
debugLog jitConfig = if debugOutput jitConfig
  then hPutStrLn stderr
  else const $ pure ()

optimizeModule :: JITConfig -> Mod.Module -> IO ()
optimizeModule jitConfig module' = do
  withPassManager defaultCuratedPassSetSpec
    { optLevel = Just (optimizerLevelToWord (optimizerLevel jitConfig)) } $ \pm -> do
    _ <- runPassManager pm module'
    pure ()

data JITConfig = JITConfig
  { debugOutput :: !Bool
  , timingOutput :: !Bool
  , optimizerLevel :: !OptimizerLevel
  }

defaultJITConfig :: JITConfig
defaultJITConfig = JITConfig {debugOutput = False, timingOutput = False, optimizerLevel = Two}

data OptimizerLevel
  = None
  | One
  | Two
  | Three

optimizerLevelToWord :: OptimizerLevel -> Word
optimizerLevelToWord l =
  case l of
    None -> 0
    One -> 1
    Two -> 2
    Three -> 3

evalJIT :: JITConfig -> AST.Module -> IO (Either String NExpr)
evalJIT jitConfig amod = do
  b <- Linking.loadLibraryPermanently Nothing
  withContext $ \ctx -> do
    t0 <- getTime Monotonic
    withModuleFromAST ctx amod $ \mod -> do
      t1 <- getTime Monotonic
      optimizeModule jitConfig mod
      t2 <- getTime Monotonic
      when (debugOutput jitConfig) $ do
        asm <- moduleLLVMAssembly mod
        BSC.putStrLn asm
      withTargetMachine $ \tm ->
        OJ.withObjectLinkingLayer $ \objectLayer -> do
          debugLog jitConfig "in objectlinkinglayer"
          OJ.withIRCompileLayer objectLayer tm $ \compileLayer -> do
            debugLog jitConfig "in compilelayer"
            t3 <- getTime Monotonic
            OJ.withModule compileLayer mod (resolver compileLayer) $ \_ -> do
              t4 <- getTime Monotonic
              debugLog jitConfig "in modulelayer"
              mainSymbol <- OJ.mangleSymbol compileLayer "main"
              jitSymbolOrError <- OJ.findSymbol compileLayer mainSymbol True
              case jitSymbolOrError of
                Left err -> do
                  debugLog jitConfig ("Could not find main: " <> show err)
                  pure $ error "Couldn't find main"
                Right (OJ.JITSymbol mainFn _) -> do
                  debugLog jitConfig "running main"
                  t5 <- getTime Monotonic
                  res <- run jitConfig mainFn
                  t6 <- getTime Monotonic
                  when (timingOutput jitConfig) $ printTimings t0 t1 t2 t3 t4 t5 t6
                  pure . Right $ convertPairs res

printTimings :: TimeSpec -> TimeSpec -> TimeSpec -> TimeSpec -> TimeSpec -> TimeSpec -> TimeSpec -> IO ()
printTimings beforeModuleSerialization afterModuleSerialization afterOptimizer beforeAddingModule afterAddingModule beforeRun afterRun = do
  printf "module serialization: %s, optimizer %s, adding module: %s, run: %s\n"
    (fmtTS moduleSerialization)
    (fmtTS optimizer)
    (fmtTS addingModule)
    (fmtTS run)
  where
    moduleSerialization = afterModuleSerialization `diffTimeSpec` beforeModuleSerialization
    optimizer = afterOptimizer `diffTimeSpec` afterModuleSerialization
    addingModule = afterAddingModule `diffTimeSpec` beforeAddingModule
    run = afterRun `diffTimeSpec` beforeRun

fmtTS :: TimeSpec -> String
fmtTS (TimeSpec s ns) = printf "%.3f" (fromIntegral s + fromIntegral ns / (10 ^ (9 :: Int)) :: Double)

intT :: Type
intT = IntegerType 64

boolT :: Type
boolT = IntegerType 1

intPtrT :: Type
intPtrT = PointerType intT $ AddrSpace.AddrSpace 0

funT :: Type
funT = PointerType (FunctionType intT [intT] False) (AddrSpace.AddrSpace 0)

voidFunT :: Type
voidFunT = PointerType (FunctionType VoidType [] False) (AddrSpace.AddrSpace 0)

setjmpT :: Type
setjmpT = PointerType (FunctionType intT [] False) (AddrSpace.AddrSpace 0)

longjmpT :: Type
longjmpT = PointerType (FunctionType VoidType [intT] False) (AddrSpace.AddrSpace 0)

funPtrT :: Type
funPtrT = PointerType funT $ AddrSpace.AddrSpace 0

pairT :: Type
pairT = StructureType False [intT, intT]

heapType :: Type
heapType = ArrayType heapSize pairT

heapPType :: Type
heapPType = PointerType heapType (AddrSpace.AddrSpace 0)

heapSize = 655350

emptyPair :: C.Constant
emptyPair = C.Struct Nothing False [C.Int 64 0, C.Int 64 0]

heapN :: Name
heapN = "pair_heap"

pairHeap :: Definition
pairHeap = GlobalDefinition
  $ globalVariableDefaults
  { name = heapN
  , LLVM.AST.Global.type' = heapType
  , initializer = Just (C.AggregateZero heapType)
  }

heapIndexN :: Name
heapIndexN = "heapIndex"

-- index of next free pair structure
heapIndex :: Definition
heapIndex = GlobalDefinition
  $ globalVariableDefaults
  { name = heapIndexN
  , LLVM.AST.Global.type' = intT
  , initializer = Just (C.Int 64 1)
  }

resultStructureN :: Name
resultStructureN = "resultStructure"

resultStructureT :: Type
resultStructureT = StructureType False [intT,intT,intT]

resultStructure :: Definition
resultStructure = GlobalDefinition
  $ globalVariableDefaults
  { name = resultStructureN
  , LLVM.AST.Global.type' = resultStructureT
  , initializer = Just $ C.Struct Nothing False [C.Int 64 0, C.Int 64 0, C.Int 64 0]
  }

zero :: Operand
zero = ConstantOperand (C.Int 64 0)
one :: Operand
one = ConstantOperand (C.Int 64 1)
zero32 :: Operand
zero32 = ConstantOperand (C.Int 32 0)
one32 :: Operand
one32 = ConstantOperand (C.Int 32 1)
two32 :: Operand
two32 = ConstantOperand (C.Int 32 2)

type BuilderInternal = State Int
startBuilderInternal = 0
type SILBuilder = IRBuilderT (ModuleBuilderT BuilderInternal)

getFunctionName :: BuilderInternal Name
getFunctionName = state $ \n -> (fromString $ 'f' : show n, n + 1)

-- | Wrap the argument in a function that accepts an integer (index to environment) as its argument.
doFunction :: SILBuilder Operand -> SILBuilder Operand
doFunction body = do
  name <- lift $ lift getFunctionName
  lift $ IRM.function name [(intT, ParameterName "env")] intT $ \_ -> (body >>= \op -> emitTerm (Ret (Just op) []))
  pure $ ConstantOperand (C.PtrToInt (C.GlobalReference funT name) intT)

heapC :: Operand
heapC = ConstantOperand (C.GlobalReference heapPType heapN)

pairOffC :: Operand
pairOffC = ConstantOperand (C.Int 64 16)

-- put "official" start of heap at index one. index zero "points" to itself, so traversing left/right stays there
leftStartC :: Operand
leftStartC = ConstantOperand (C.PtrToInt (C.GlobalReference heapPType heapN) intT)

rightStartC :: Operand
rightStartC = ConstantOperand (C.Add True True (C.PtrToInt (C.GlobalReference heapPType heapN) intT) (C.Int 64 8))

heapIndexC :: Operand
heapIndexC = ConstantOperand (C.GlobalReference intPtrT heapIndexN)

-- | @makePair a b@ allocates a new pair (a,b) at the current heap
-- index and increments the heap index.
makePair :: MonadIRBuilder m => Operand -> Operand -> m Operand
makePair a b = do
  heap <- IRI.load heapIndexC 0
  l <- IRI.gep heapC [zero, heap, zero32]
  r <- IRI.gep heapC [zero, heap, one32]
  IRI.store l 0 a
  IRI.store r 0 b
  nc <- IRI.add heap one
  IRI.store heapIndexC 0 nc
  pure heap

-- | @doLeft p@ loads the first element of the pair @p@.
doLeft :: MonadIRBuilder m => Operand -> m Operand
doLeft xp = do
  la <- IRI.gep heapC [zero, xp, zero32]
  IRI.load la 0

-- | @doRight p@ loads the second element of the pair @p@.
doRight :: MonadIRBuilder m => Operand -> m Operand
doRight xp = do
  ra <- IRI.gep heapC [zero, xp, one32]
  IRI.load ra 0

envC :: Operand
envC = LocalReference intT "env"

lComment :: a -> (a, MDRef MDNode)
lComment s = (s, MDInline (MDTuple []))

toLLVM :: NExpr -> SILBuilder Operand
-- chunks of AST that can be translated to optimized instructions
toLLVM (NSetEnv (NPair (NGate i) (NPair e t))) = case i of
  NZero -> toLLVM e
  (NPair _ _) -> toLLVM t
  _ -> do
    ip <- toLLVM i
    elseB <- freshUnName
    thenB <- freshUnName
    exitB <- freshUnName
    brCond <- IRI.icmp IP.EQ ip zero
    emitTerm (CondBr brCond elseB thenB [])

    emitBlockStart elseB
    ep <- toLLVM e
    endElseB <- currentBlock
    emitTerm (Br exitB [])

    emitBlockStart thenB
    tp <- toLLVM t
    endThenB <- currentBlock
    emitTerm (Br exitB [])

    emitBlockStart exitB
    IRI.phi [(ep, endElseB), (tp, endThenB)]
-- single instruction translation
toLLVM NZero = pure zero
toLLVM (NPair a b) = do
  oa <- toLLVM a
  ob <- toLLVM b
  makePair oa ob
toLLVM (NLeft x) = toLLVM x >>= doLeft
toLLVM (NRight x) = toLLVM x >>= doRight
toLLVM NEnv = pure envC
toLLVM (NDefer x) = doFunction $ toLLVM x
toLLVM (NSetEnv x) = do
  -- Evaluate x to (clo, env)
  xp <- toLLVM x
  l <- IRI.gep heapC [zero, xp, zero32]
  r <- IRI.gep heapC [zero, xp, one32]
  clo <- IRI.load l 0
  env <- IRI.load r 0
  funPtr <- IRI.inttoptr clo funT
  -- Call the function stored at clo with argument env
  IRI.call funPtr [(env, [])]
toLLVM (NGate x) = do
  lx <- toLLVM x
  bool <- IRI.icmp IP.NE lx zero
  IRI.select bool
    (ConstantOperand (C.PtrToInt (C.GlobalReference funT "goRight") intT))
    (ConstantOperand (C.PtrToInt (C.GlobalReference funT "goLeft") intT))
toLLVM (NAbort x) = do
  lx <- toLLVM x

  abortB <- freshUnName
  exitB <- freshUnName
  brCond <- IRI.icmp IP.EQ lx zero
  emitTerm (CondBr brCond exitB abortB [])

  emitBlockStart abortB
  IRI.call (ConstantOperand (C.GlobalReference longjmpT "w_longjmp")) [(lx, [])]
  emitTerm (Unreachable [])

  emitBlockStart exitB
  pure zero

-- TODO this will be hard
toLLVM (NTrace x) = toLLVM x

resultC :: Operand
resultC = ConstantOperand $ C.GlobalReference (PointerType resultStructureT (AddrSpace.AddrSpace 0)) resultStructureN
