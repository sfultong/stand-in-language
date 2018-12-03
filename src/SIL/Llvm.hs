{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SIL.Llvm where

import Control.Monad.Except
import Control.Monad.State.Strict
import Crypto.Hash.SHA256 (hashlazy)
import Data.Binary (encode)
import Data.ByteString (ByteString)
import Data.ByteString.Short (toShort)
import Data.Int (Int64)
import Data.Map.Strict (Map)
import Data.String (fromString)
import Foreign.Ptr (FunPtr, castPtrToFunPtr, wordPtrToPtr, Ptr, WordPtr(..), plusPtr, IntPtr(..), intPtrToPtr)
import Foreign.Storable (peek)
import System.Clock
import System.IO (hPutStrLn, stderr)
import Text.Printf
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map

import LLVM.AST hiding (Monotonic)
import LLVM.AST.Global as G
import LLVM.Context
import LLVM.IRBuilder.Constant (int64)
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.Module as Mod
import LLVM.PassManager

import qualified LLVM.AST as AST
import qualified LLVM.AST.AddrSpace as AddrSpace
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.ParameterAttribute as PA
import qualified LLVM.AST.Type as T
import qualified LLVM.CodeGenOpt as CodeGenOpt
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.IRBuilder.Instruction as IRI
import qualified LLVM.IRBuilder.Module as IRM
import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as OJ
import qualified LLVM.OrcJIT.CompileLayer as OJ
import qualified LLVM.Relocation as Reloc
import qualified LLVM.Target as Target

import Naturals

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Int64)) -> IO (Ptr Int64)

data RunResult = RunResult
  { resultValue :: Int64
  , resultNumPairs :: Int64
  }

run :: JITConfig -> WordPtr -> IO RunResult
run jitConfig fn = do
  let
    mungedPtr :: FunPtr (IO (Ptr Int64))
    mungedPtr = castPtrToFunPtr . wordPtrToPtr $ fn
  result <- haskFun mungedPtr
  debugLog jitConfig "finished evaluation"
  numPairs <- peek result
  resultVal <- peek (plusPtr result 8)
  pure (RunResult resultVal numPairs)


-- | Recursively follow all integers by interpreting them as indices
-- in the pair array until a 0 is found.
convertPairs :: RunResult -> IO NExpr
convertPairs (RunResult x _) = go x
  where
    go 0 = pure NZero
    go i = do
      let ptr = intPtrToPtr (IntPtr (fromIntegral i))
      l <- peek ptr
      r <- peek (ptr `plusPtr` 8)
      NPair <$> go l <*> go r

makeModule :: NExpr -> AST.Module
makeModule iexpr = flip evalState (Map.empty, 0) . buildModuleT "SILModule" $ do
  _ <- emitDefn
    (GlobalDefinition (functionDefaults {
                          name = "GC_malloc",
                          returnType = PointerType (IntegerType 8) (AddrSpace.AddrSpace 0),
                          G.returnAttributes = [PA.NoAlias],
                          parameters = ([Parameter intT "" []], False)
                          }))
  gcRegisterMyThread <- extern "SIL_register_my_thread" [] T.void
  mapM_ emitDefn [heapIndex, resultStructure]

  _ <- goLeft
  _ <- goRight

  setJmp <- IRM.extern "w_setjmp" [] intT
  _ <- IRM.extern "w_longjmp" [intT] VoidType

  IRM.function "main" [] (PointerType resultStructureT (AddrSpace.AddrSpace 0))
    $ \_ -> mdo
        -- wrap the evaluation of iexpr in a setjmp branch, so that an abort instruction can return for an early exit
        preludeB <- block `named` "prelude"
        _ <- IRI.call gcRegisterMyThread []
        jumped <- IRI.call setJmp []
        brCond <- IRI.icmp IP.EQ jumped zero
        IRI.condBr brCond mainB exitB

        mainB <- block `named` "main"
        -- TODO fix
        -- mainExp <- toLLVM iexpr
        mainExp <- undefined
        endMainB <- currentBlock
        IRI.br exitB
        emitTerm (Br exitB [])

        exitB <- block `named` "exit"
        result <- IRI.phi [(mainExp, endMainB), (jumped, preludeB)]
        heapC <- IRI.load heapIndexC 0
        numPairs <- IRI.gep resultC [zero, zero32]
        resultPair <- IRI.gep resultC [zero, one32]
        IRI.store numPairs 0 heapC
        IRI.store resultPair 0 result
        IRI.ret resultC

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

evalJIT :: JITConfig -> AST.Module -> IO (Either String RunResult)
evalJIT jitConfig amod = do
  _ <- Linking.loadLibraryPermanently Nothing
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
                  pure . Right $ res

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

gcMallocT :: Type
gcMallocT = PointerType (FunctionType (PointerType (IntegerType 8) (AddrSpace.AddrSpace 0)) [intT] False) (AddrSpace.AddrSpace 0)

funPtrT :: Type
funPtrT = PointerType funT $ AddrSpace.AddrSpace 0

pairT :: Type
pairT = StructureType False [intT, intT]

pairPtrT :: Type
pairPtrT = PointerType pairT (AddrSpace.AddrSpace 0)

heapIndexN :: Name
heapIndexN = "heapIndex"

-- index of next free pair structure
heapIndex :: Definition
heapIndex = GlobalDefinition
  $ globalVariableDefaults
  { name = heapIndexN
  , G.type' = intT
  , initializer = Just (C.Int 64 1)
  }

resultStructureN :: Name
resultStructureN = "resultStructure"

resultStructureT :: Type
resultStructureT = StructureType False [intT,intT]

resultStructure :: Definition
resultStructure = GlobalDefinition
  $ globalVariableDefaults
  { name = resultStructureN
  , G.type' = resultStructureT
  , initializer = Just $ C.Struct Nothing False [C.Int 64 0, C.Int 64 0]
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

type BuilderInternal = State (Map ByteString Operand, Int)
type SILBuilder = IRBuilderT (ModuleBuilderT BuilderInternal)

-- | Wrap the argument in a function that accepts an integer (index to environment) as its argument.
doFunction :: NExpr -> SILBuilder Operand
doFunction body = do
  (functions, _) <- get
  case Map.lookup h functions of
    Just f -> pure f
    Nothing -> do
      let name = Name ("function_" <> toShort (Base16.encode h))
      _ <- lift $ IRM.function name [(intT, ParameterName "env")] intT $ \_ -> do
         -- TODO fix
         -- x <- toLLVM body
         x <- undefined
         IRI.ret x
      let r = ConstantOperand (C.PtrToInt (C.GlobalReference funT name) intT)
      modify (\(m, i) -> (Map.insert h r m, i))
      pure r
  where h = hashlazy (encode body)

doAnonFunction :: SILBuilder Operand -> SILBuilder Operand
doAnonFunction doBody = do
  (_, fn) <- get
  let name = Name $ fromString ("anonFunction_" ++ show fn)
  _ <- lift $ IRM.function name [(intT, ParameterName "env")] intT $ \_ -> doBody >>= IRI.ret
  modify (\(m, i) -> (m, i + 1))
  pure $ ConstantOperand (C.PtrToInt (C.GlobalReference funT name) intT)

pairOffC :: Operand
pairOffC = ConstantOperand (C.Int 64 16)

heapIndexC :: Operand
heapIndexC = ConstantOperand (C.GlobalReference intPtrT heapIndexN)

gcMallocPair :: MonadIRBuilder m => m Operand
gcMallocPair = do
  sizePtr <- IRI.gep (ConstantOperand (C.Null pairPtrT)) [one32]
    `named` "size.ptr"
  size <- IRI.ptrtoint sizePtr intT `named` "size"
  ptr <- IRI.call (ConstantOperand (C.GlobalReference gcMallocT "GC_malloc")) [(size, [])]
  IRI.bitcast ptr pairPtrT

-- | @makePair a b@ allocates a new pair (a,b) at the current heap
-- index and increments the heap index.
makePair :: MonadIRBuilder m => Operand -> Operand -> m Operand
makePair a b = do
  ptr <- gcMallocPair
  l <- IRI.gep ptr [zero, zero32]
  r <- IRI.gep ptr [zero, one32]
  IRI.store l 0 a
  IRI.store r 0 b
  heap <- IRI.load heapIndexC 0
  nc <- IRI.add heap one
  IRI.store heapIndexC 0 nc
  IRI.ptrtoint ptr intT

-- | @goLeft p@ loads the first element of the pair @p@.
goLeft :: (MonadModuleBuilder m, MonadFix m) => m Operand
goLeft = IRM.function "goLeft" [(intT, ParameterName "x")] intT $ \[xp] -> mdo
  cond <- IRI.icmp IP.EQ xp zero
  IRI.condBr cond ptrZero ptrNonZero

  ptrZero <- block
  ptrZeroRes <- pure zero
  IRI.br exit

  ptrNonZero <- block
  ptr <- IRI.inttoptr xp pairPtrT
  la <- IRI.gep ptr [zero, zero32]
  ptrNonZeroRes <- IRI.load la 0
  IRI.br exit

  exit <- block
  res <- IRI.phi [(ptrZeroRes, ptrZero), (ptrNonZeroRes, ptrNonZero)]
  IRI.ret res

-- | @goRight p@ loads the second element of the pair @p@.
goRight :: (MonadModuleBuilder m, MonadFix m) => m Operand
goRight = IRM.function "goRight" [(intT, ParameterName "x")] intT $ \[xp] -> mdo
  cond <- IRI.icmp IP.EQ xp zero
  IRI.condBr cond ptrZero ptrNonZero

  ptrZero <- block
  ptrZeroRes <- pure zero
  IRI.br exit

  ptrNonZero <- block
  ptr <- IRI.inttoptr xp pairPtrT
  la <- IRI.gep ptr [zero, one32]
  ptrNonZeroRes <- IRI.load la 0
  IRI.br exit

  exit <- block
  res <- IRI.phi [(ptrZeroRes, ptrZero), (ptrNonZeroRes, ptrNonZero)]
  IRI.ret res

doLeft :: MonadIRBuilder m => Operand -> m Operand
doLeft x = IRI.call (ConstantOperand (C.GlobalReference funT "goLeft")) [(x, [])]

doRight :: MonadIRBuilder m => Operand -> m Operand
doRight x = IRI.call (ConstantOperand (C.GlobalReference funT "goRight")) [(x, [])]

envC :: Operand
envC = LocalReference intT "env"

lComment :: a -> (a, MDRef MDNode)
lComment s = (s, MDInline (MDTuple []))

toLLVM :: (Map FragIndex ExprFrag, FragType -> ExprFrag -> FragType) -> FragType -> ExprFrag -> SILBuilder Operand
toLLVM = undefined
-- chunks of AST that can be translated to optimized instructions
-- single instruction translation
{-
toLLVM _ _ FZero = pure zero
toLLVM helpers envType (FPair a b) = do
  oa <- toLLVM helpers envType a
  ob <- toLLVM helpers envType b
  makePair oa ob
toLLVM helpers (FLeft x) = toLLVM helpers x >>= doLeft
toLLVM helpers (FRight x) = toLLVM helpers x >>= doRight
toLLVM _ FEnv = pure envC
toLLVM helpers (FDefer x) = doFunction x
toLLVM helpers (FSetEnv x) = do
  -- Evaluate x to (clo, env)
  xp <- toLLVM helpers x
  ptr <- IRI.inttoptr xp pairPtrT
  l <- IRI.gep ptr [zero, zero32]
  r <- IRI.gep ptr [zero, one32]
  clo <- IRI.load l 0
  env <- IRI.load r 0
  funPtr <- IRI.inttoptr clo funT
  -- Call the function stored at clo with argument env
  IRI.call funPtr [(env, [])]
toLLVM helpers (FGate x) = do
  lx <- toLLVM helpers x
  bool <- IRI.icmp IP.NE lx zero
  IRI.select bool
    (ConstantOperand (C.PtrToInt (C.GlobalReference funT "goRight") intT))
    (ConstantOperand (C.PtrToInt (C.GlobalReference funT "goLeft") intT))
toLLVM helpers (FAbort x) = mdo
  lx <- toLLVM helpers x
  brCond <- IRI.icmp IP.EQ lx zero
  emitTerm (CondBr brCond exitB abortB [])

  abortB <- block `named` "abort"
  _ <- IRI.call (ConstantOperand (C.GlobalReference longjmpT "w_longjmp")) [(lx, [])]
  IRI.unreachable

  exitB <- block `named` "exit"
  pure zero
-- toLLVM (NNum i) = int64 (fromIntegral i)
toLLVM (NAdd a b) = do
  a' <- toLLVM a
  b' <- toLLVM b
  IRI.add a' b'
toLLVM (NMult a b) = do
  a' <- toLLVM a
  b' <- toLLVM b
  IRI.mul a' b'
toLLVM (NITE c t f) = mdo
  c' <- toLLVM c
  cond <- IRI.icmp IP.NE c' zero
  IRI.condBr cond ifThen ifElse

  ifThen <- block `named` "if.then"
  trueVal <- toLLVM t
  ifThenEnd <- currentBlock
  IRI.br ifExit

  ifElse <- block `named` "if.else"
  falseVal <- toLLVM f
  ifElseEnd <- currentBlock
  IRI.br ifExit

  ifExit <- block `named` "if.exit"
  IRI.phi [(trueVal, ifThenEnd), (falseVal, ifElseEnd)]
toLLVM (NtoChurch x) = do
  cf <- doAnonFunction $ do
    innerF <- doAnonFunction $ mdo
      startI <- toLLVM x
      fun <- doRight envC >>= doLeft
      funPtr <- IRI.inttoptr fun funT
      savedEnv <- doRight envC
      entry <- currentBlock
      IRI.br loop

      loop <- block `named` "toChurch.loop"
      currentI <- IRI.phi [(startI, entry), (nextI, loop)]
      currentVal <- IRI.phi [(envC, entry), (nextV, loop)]
      fResult <- IRI.call funPtr [(currentVal, [])]
      nextV <- makePair fResult savedEnv
      nextI <- IRI.sub currentI one
      cond <- IRI.icmp IP.EQ nextI zero
      IRI.condBr cond exit loop

      exit <- block `named` "toChurch.exit"
      pure fResult
    makePair innerF envC
  makePair cf envC
-- TODO this will be hard
toLLVM (NTrace x) = toLLVM x
-}

resultC :: Operand
resultC = ConstantOperand $ C.GlobalReference (PointerType resultStructureT (AddrSpace.AddrSpace 0)) resultStructureN
