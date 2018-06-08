{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SIL.Llvm where

import Control.Exception
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Int (Int64)
import Data.String (fromString)
import Debug.Trace
import Foreign.Ptr (FunPtr, castFunPtr, castPtrToFunPtr, wordPtrToPtr, Ptr, WordPtr(..), plusPtr, castPtr)
import Foreign.Storable (peek)
import System.IO (hPutStrLn, stderr)

import LLVM.AST
import LLVM.AST.Float
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.Context
import LLVM.Module as Mod
import LLVM.PassManager

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Short as SBS
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
import qualified LLVM.Relocation as Reloc
import qualified LLVM.Target as Target

import qualified SIL as SIL

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Int64)) -> IO (Ptr Int64)

run :: WordPtr -> IO (Int64, [(Int64,Int64)])
run fn = do
  let
    mungedPtr :: FunPtr (IO (Ptr Int64))
    mungedPtr = castPtrToFunPtr . wordPtrToPtr $ fn
  result <- haskFun mungedPtr
  debugLog "finished evaluation"
  numPairs <- peek result
  resultPair <- peek (plusPtr result 8)
  startHeap <- peek (plusPtr result 16)
  let readPair (addr,l) _ = do
        lp <- peek addr
        rp <- peek $ plusPtr addr 8
        pure (plusPtr addr 16, (lp,rp):l)
  pairs <- (reverse . snd) <$> foldM readPair (startHeap, []) [1..numPairs]
  pure (resultPair, pairs)

convertPairs :: (Int64, [(Int64,Int64)]) -> SIL.IExpr
convertPairs (x, pairs)=
  let convertPair 0 = SIL.Zero
      convertPair n = let (l,r) = pairs !! fromIntegral n
                      in SIL.Pair (convertPair l) (convertPair r)
  in convertPair x

makeModule :: SIL.IExpr -> AST.Module
makeModule iexpr = defaultModule
  { moduleDefinitions =
    [ pairHeap, heapIndex, resultStructure, goLeft, goRight, jumpBufTypeDef, jumpBuf, testFun ]
    ++ (toLLVM' iexpr)
    -- ++ testLLVM
  , moduleName = "SILModule"
  }

data DebugModule = DebugModule AST.Module

instance Show DebugModule where
  show (DebugModule m) = concatMap showDefinition $ moduleDefinitions m
    where showDefinition (GlobalDefinition f@(Function _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) = displayFunction f
          showDefinition _ = ""
          displayFunction f = concat [show (name f), "\n", (concatMap displayBlock (basicBlocks f)), "\n"]
          displayBlock (BasicBlock n inst term) =
            concat ["  ", show n, "\n", concatMap displayInstruction inst, "    ", show term, "\n"]
          displayInstruction i = concat ["    ", show i, "\n"]

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

debugLog :: String -> IO ()
debugLog = hPutStrLn stderr
--debugLog = pure ()

evalJIT :: AST.Module -> IO (Either String SIL.IExpr)
evalJIT amod = do
  b <- Linking.loadLibraryPermanently Nothing
  withContext $ \ctx ->
    withModuleFromAST ctx amod $ \mod -> do
      asm <- moduleLLVMAssembly mod
      BSC.putStrLn asm
      withTargetMachine $ \tm ->
        OJ.withObjectLinkingLayer $ \objectLayer -> do
          debugLog "in objectlinkinglayer"
          OJ.withIRCompileLayer objectLayer tm $ \compileLayer -> do
            debugLog "in compilelayer"
            OJ.withModule compileLayer mod (resolver compileLayer) $ \_ -> do
              debugLog "in modulelayer"
  {-
              tasm <- moduleTargetAssembly tm mod
              BSC.putStrLn tasm
              debugLog "really?????"
-}
              mainSymbol <- OJ.mangleSymbol compileLayer "main"
              (OJ.JITSymbol mainFn _) <- OJ.findSymbol compileLayer mainSymbol True
              if mainFn == WordPtr 0
                then do
                debugLog "Could not find main"
                pure $ error "Couldn't find main"
                else do
                  debugLog "running main"
                  res <- run mainFn
                  -- debugLog . show $ res
                  pure . Right $ convertPairs res

-- name counter, block instruction list (reversed), block name, block list, definition list, definition counter
type FunctionState a = State (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word) a

startFunctionState :: (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word)
startFunctionState = (1, [], UnName 0, [], [], 0)

intT :: Type
intT = IntegerType 64

boolT :: Type
boolT = IntegerType 1

intPtrT :: Type
intPtrT = PointerType intT $ AddrSpace.AddrSpace 0

funT :: Type
funT = PointerType (FunctionType intT [intT] False) (AddrSpace.AddrSpace 0)

funPtrT :: Type
funPtrT = PointerType funT $ AddrSpace.AddrSpace 0

jumpBufType :: Type
jumpBufType = StructureType False [ArrayType 8 intT, IntegerType 32, StructureType False [ArrayType 16 intT]]

jumpBufTypeDef :: Definition
jumpBufTypeDef = TypeDefinition "jump_buf_type" $ Just jumpBufType

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
  , initializer = Just (C.Array pairT . take (fromIntegral heapSize) $ repeat emptyPair)
  }

jumpBufN :: Name
jumpBufN = "jumpBuf"

jumpBuf :: Definition
jumpBuf = GlobalDefinition
  $ globalVariableDefaults
  { name = jumpBufN
  , LLVM.AST.Global.type' = jumpBufType
  , linkage = Internal
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
{-
negOne :: Operand
negOne = ConstantOperand (C.Int 64 (-1))
-}

doInst :: Instruction -> FunctionState Operand
doInst inst = state $ \(c, l, n, b, d, dc) ->
  if c == maxBound
  then error "BasicBlock instruction limit reached"
  else (LocalReference intT $ UnName c, (c + 1, (UnName c := inst) : l, n, b, d, dc))

doVoidInst :: Instruction -> FunctionState ()
doVoidInst inst = state $ \(c, l, n, b, d, dc) ->
  ((), (c, Do inst : l, n, b, d, dc))

doNamedInst :: Name -> Instruction -> FunctionState ()
doNamedInst name inst = state $ \(c, l, n, b, d, dc) ->
  ((), (c, (name := inst) : l, n, b, d, dc))

doTypedInst :: Type -> Instruction -> FunctionState Operand
doTypedInst t inst = state $ \(c, l, n, b, d, dc) ->
  if c == maxBound
  then error "BasicBlock instruction limit reached"
  else (LocalReference t $ UnName c, (c + 1, (UnName c := inst) : l, n, b, d, dc))

doBlock :: Terminator -> FunctionState Name
doBlock term = state $ \(c, l, n, b, d, dc) ->
  if c == maxBound
  then error "BasicBlock limit reached"
  else (n, (c, [], UnName c, BasicBlock n (reverse l) (Do term) : b, d, dc))

-- probably slightly redundant
doNamedBlock :: Name -> Terminator -> FunctionState ()
doNamedBlock name term = state $ \(c, l, n, b, d, dc) ->
  ((), (c, [], n, BasicBlock name (reverse l) (Do term) : b, d, dc))

getName :: FunctionState Name
getName = state $ \(c, l, n, b, d, dc) -> (UnName c, (c + 1, l, n, b, d, dc))

setBlockName :: Name -> FunctionState ()
setBlockName n = state $ \(c, l, _, b, d, dc) -> ((), (c, l, n, b, d, dc))

doFunction :: FunctionState Operand -> FunctionState Operand
doFunction body = do
  (c, ins, n, blks, def, defC) <- get
  let (_, (_, _, _, blks2, def2, defC2)) = runState (body >>= \op -> doBlock (Ret (Just op) []))
        (1, [], UnName 0, [], def, defC)
      newName = fromString ('f' : show defC2)
      newDef = (GlobalDefinition $ functionDefaults
                { name = newName
                , parameters = ([Parameter intT "env" []], False)
                , G.callingConvention = CC.Fast
                , returnType = intT
                , basicBlocks = reverse blks2
                })
  put (c, ins, n, blks, newDef : def2, defC2 + 1)
  pure $ ConstantOperand (C.PtrToInt (C.GlobalReference funT newName) intT)
  --doInst $ PtrToInt (ConstantOperand (C.GlobalReference funT newName)) intT []

heapC :: Operand
heapC = ConstantOperand (C.GlobalReference heapPType heapN)

pairOffC :: Operand
pairOffC = ConstantOperand (C.Int 64 16)

-- put "official" start of heap at index one for pointer arithmetic trick for left/right on zero
leftStartC :: Operand
-- leftStartC = ConstantOperand (C.Add False False (C.PtrToInt (C.GlobalReference heapPType heapN) intT) (C.Int 64 16))
leftStartC = ConstantOperand (C.PtrToInt (C.GlobalReference heapPType heapN) intT)

rightStartC :: Operand
rightStartC = ConstantOperand (C.Add True True (C.PtrToInt (C.GlobalReference heapPType heapN) intT) (C.Int 64 8))

makePair :: Operand -> Operand -> FunctionState Operand
makePair a b = do
  heap <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
  l <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, heap, zero32] []
  r <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, heap, one32] []
  doVoidInst $ Store False l a Nothing 0 []
  doVoidInst $ Store False r b Nothing 0 []
  nc <- doInst $ AST.Add False False heap one []
  doVoidInst $ Store False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) nc Nothing 0 []
  pure heap

doLeft :: Operand -> FunctionState Operand
doLeft xp = do
  offset <- doInst $ Mul False False xp pairOffC []
  addr <- doInst $ Add False False leftStartC offset []
  ptr <- doInst $ IntToPtr addr intPtrT []
  doInst $ Load False ptr Nothing 0 []

doRight :: Operand -> FunctionState Operand
doRight xp = do
  offset <- doInst $ Mul False False xp pairOffC []
  addr <- doInst $ Add False False rightStartC offset []
  ptr <- doInst $ IntToPtr addr intPtrT []
  doInst $ Load False ptr Nothing 0 []

envC :: Operand
envC = LocalReference intT "env"

lComment :: a -> (a, MetadataNode)
lComment s = (s, MetadataNode [])

toLLVM :: SIL.IExpr -> FunctionState Operand
-- chunks of AST that can be translated to optimized instructions
toLLVM (SIL.SetEnv (SIL.Pair (SIL.Gate i) (SIL.Pair e t))) = do
  ip <- toLLVM i
  elseB <- getName
  thenB <- getName
  exitB <- getName
  brCond <- doTypedInst boolT $ ICmp IP.EQ ip zero [lComment "optimized_if_conditional"]
  _ <- doBlock (CondBr brCond elseB thenB [])

  setBlockName elseB
  ep <- toLLVM e
  endElseB <- doBlock (Br exitB [lComment "elseB"])

  setBlockName thenB
  tp <- toLLVM t
  endThenB <- doBlock (Br exitB [lComment "thenB"])

  setBlockName exitB
  result <- doInst $ Phi intT [(ep, endElseB), (tp, endThenB)] [lComment "from_if_else"]
  pure result
{-
toLLVM (SIL.Pair oof@(SIL.Defer (SIL.Pair (SIL.Defer apps) SIL.Env)) SIL.Zero) =
  let countApps x (SIL.PLeft SIL.Env) = x
      countApps x (SIL.SetEnv (SIL.Twiddle (SIL.Pair ia (SIL.PLeft (SIL.PRight SIL.Env))))) = countApps (x + 1) ia
      countApps _ _ = 0
      appCount = countApps 0 apps
  in if appCount > 0
     then do
    trace "doing it" $ pure ()
    innerF <- doFunction $ do
      initialP <- doInst $ AST.GetElementPtr False heapC [zero, envC, zero32] []
      initialVal <- doInst $ Load False initialP Nothing 0 []
      cloP <- doInst $ AST.GetElementPtr False heapC [zero, envC, one32] []
      cloVal <- doInst $ Load False cloP Nothing 0 []
      fun <- doLeft cloVal >>= doLeft
      funPtr <- doInst $ IntToPtr fun funT []
      loop <- getName
      exitB <- getName
      entry <- doBlock (Br loop [])

      setBlockName loop
      nextCount <- getName
      nextValue <- getName
      count <- doInst $ Phi intT [(zero, entry), (LocalReference intT nextCount, loop)] []
      value <- doInst $ Phi intT [(initialVal, entry), (LocalReference intT nextValue, loop)] []
      doNamedInst nextValue $ Call (Just Tail) CC.Fast [] (Right funPtr) [(value, [])] [] []
      doNamedInst nextCount $ Add False False count one []
      cond <- doTypedInst boolT $ ICmp IP.ULT (LocalReference intT nextCount) (ConstantOperand (C.Int 64 appCount)) []
      _ <- doBlock (CondBr cond loop exitB [])

      setBlockName exitB
      pure $ LocalReference intT nextValue

    outerF <- doFunction $ makePair innerF (LocalReference intT $ Name "env")
    makePair outerF zero

    -- not actually church numeral, run normal processing
     else toLLVM oof >>= \x -> makePair x negOne
-}
-- single instruction translation
toLLVM SIL.Zero = pure zero
toLLVM (SIL.Pair a b) = do
  oa <- toLLVM a
  ob <- toLLVM b
  makePair oa ob
toLLVM (SIL.Twiddle x) = do
  xp <- toLLVM x
  -- get values for current pairs
  ia <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, xp, zero32] []
  ca <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, xp, one32] []
  i <- doInst $ Load False ia Nothing 0 []
  c <- doInst $ Load False ca Nothing 0 []
  cla <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, c, zero32] []
  cea <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, c, one32] []
  cl <- doInst $ Load False cla Nothing 0 []
  ce <- doInst $ Load False cea Nothing 0 []
  -- create new pairs
  nenv <- makePair i ce
  makePair cl nenv
toLLVM (SIL.PLeft x) = toLLVM x >>= doLeft
toLLVM (SIL.PRight x) = toLLVM x >>= doRight
toLLVM SIL.Env = pure envC
toLLVM (SIL.Defer x) = doFunction $ toLLVM x
toLLVM (SIL.SetEnv x) = do
  xp <- toLLVM x
  l <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, xp, zero32] []
  r <- doTypedInst intPtrT $ AST.GetElementPtr False heapC [zero, xp, one32] []
  clo <- doInst $ Load False l Nothing 0 []
  env <- doInst $ Load False r Nothing 0 []
  funPtr <- doInst $ IntToPtr clo funT []
  doInst $ Call (Just Tail) CC.Fast [] (Right funPtr) [(env, [])] [] []
toLLVM (SIL.Gate x) = do
  lx <- toLLVM x
  bool <- doInst $ ICmp IP.NE lx zero []
  doInst $ Select bool
    (ConstantOperand (C.PtrToInt (C.GlobalReference funT "goRight") intT))
    (ConstantOperand (C.PtrToInt (C.GlobalReference funT "goLeft") intT))
    []
-- TODO
toLLVM (SIL.Abort _) = pure zero
toLLVM (SIL.Trace x) = toLLVM x

resultC :: Operand
resultC = ConstantOperand $ C.GlobalReference (PointerType resultStructureT (AddrSpace.AddrSpace 0)) resultStructureN

finishMain :: Operand -> FunctionState Name
finishMain result = do
  heapC <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
  numPairs <- doTypedInst intPtrT $ AST.GetElementPtr False resultC [zero, zero32] []
  resultPair <- doTypedInst intPtrT $ AST.GetElementPtr False resultC [zero, one32] []
  heapStart <- doTypedInst intPtrT $ AST.GetElementPtr False resultC [zero, two32] []
  doVoidInst $ Store False numPairs heapC Nothing 0 []
  doVoidInst $ Store False resultPair result Nothing 0 []
  doVoidInst $ Store False heapStart (ConstantOperand (C.PtrToInt (C.GlobalReference heapPType heapN) intT))
       Nothing 0 []
  doBlock (Ret (Just resultC) [])

toLLVM' :: SIL.IExpr -> [Definition]
toLLVM' iexpr =
  let (_, (_, _, _, blocks, definitions, _)) =
        runState (toLLVM iexpr >>= finishMain) startFunctionState
  in (GlobalDefinition $ functionDefaults
       { name = "main"
       , parameters = ([], False)
       , returnType = PointerType resultStructureT (AddrSpace.AddrSpace 0)
       , basicBlocks = reverse blocks
       }
     ) : definitions

testLLVM :: [Definition]
testLLVM =
  let (_, (_, _, _, blocks, definitions, _)) =
        runState (testMain >>= finishMain) startFunctionState
  {-
      testMain = do
        doInst $ Call (Just Tail) CC.Fast [] (Right (ConstantOperand (C.GlobalReference funT (Name "testf")))) [(zero, [])] [] []
-}
  {-
      testMain = do
        num2 <- doInst $ GetElementPtr False heapC [zero, zero, zero32] []
        doVoidInst $ Store False num2 (ConstantOperand (C.PtrToInt (C.GlobalReference funT (Name "testf")) intT)) Nothing 0 []
        num7 <- doInst $ Load False num2 Nothing 0 []
        num9 <- doInst $ IntToPtr num7 funT []
        doInst $ Call (Just Tail) CC.Fast [] (Right num9) [(zero, [])] [] []
-}
  {-
      testMain = do
        num1 <- doInst $ PtrToInt (ConstantOperand (C.GlobalReference funT (Name "testf"))) intT []
        num2 <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
        num3 <- doTypedInst intPtrT $ GetElementPtr False heapC [zero, num2, zero32] []
        num4 <- doTypedInst intPtrT $ GetElementPtr False heapC [zero, num2, one32] []
        doVoidInst $ Store False num3 num1 Nothing 0 []
        doVoidInst $ Store False num4 zero Nothing 0 []
        num5 <- doInst $ Add False False num2 one []
        doVoidInst $ Store False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) num5 Nothing 0 []
        num6 <- doInst $ GetElementPtr False heapC [zero, num2, zero32] []
        num7 <- doInst $ GetElementPtr False heapC [zero, num2, one32] []
        num8 <- doInst $ Load False num6 Nothing 0 []
        num9 <- doInst $ Load False num7 Nothing 0 []
        num10 <- doInst $ IntToPtr num8 funT []
        doInst $ Call (Just Tail) CC.Fast [] (Right num10) [(num9, [])] [] []
-}
      testMain = do
        num1 <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
        num2 <- doTypedInst intPtrT $ GetElementPtr False heapC [zero, num1, zero32] []
        num3 <- doTypedInst intPtrT $ GetElementPtr False heapC [zero, num1, one32] []
        doVoidInst $ Store False num2 (ConstantOperand (C.PtrToInt (C.GlobalReference funT (Name "testf")) intT)) Nothing 0 []
        doVoidInst $ Store False num3 zero Nothing 0 []
        num4 <- doInst $ Add False False num1 one []
        doVoidInst $ Store False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) num4 Nothing 0 []
        num5 <- doTypedInst intPtrT $ GetElementPtr False heapC [zero, num1, zero32] []
        num6 <- doTypedInst intPtrT $ GetElementPtr False heapC [zero, num1, one32] []
        num7 <- doInst $ Load False num5 Nothing 0 []
        num8 <- doInst $ Load False num6 Nothing 0 []
        num9 <- doInst $ IntToPtr num7 funT []
        doInst $ Call (Just Tail) CC.Fast [] (Right num9) [(num8, [])] [] []

  in (GlobalDefinition $ functionDefaults
       { name = "main"
       , parameters = ([], False)
       , returnType = PointerType resultStructureT (AddrSpace.AddrSpace 0)
       , basicBlocks = reverse blocks
       }
     ) : definitions

--- TODO make always inlined
goLeft :: Definition
goLeft = GlobalDefinition $ functionDefaults
  { name = "goLeft"
  , parameters = ([Parameter intT "x" []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock "gl1"
      [ UnName 0 := Mul False False (LocalReference intT "x") pairOffC []
      , UnName 1 := Add False False leftStartC (LocalReference intT (UnName 0)) []
      , UnName 2 := IntToPtr (LocalReference intT (UnName 1)) intPtrT []
      , UnName 3 := Load False (LocalReference intPtrT (UnName 2)) Nothing 0 []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 3))) [])
    ]
  }

-- TODO make always inlined
goRight :: Definition
goRight = GlobalDefinition $ functionDefaults
  { name = "goRight"
  , parameters = ([Parameter intT "x" []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock "gr1"
      [ UnName 0 := Mul False False (LocalReference intT "x") pairOffC []
      , UnName 1 := Add False False rightStartC (LocalReference intT (UnName 0)) []
      , UnName 2 := IntToPtr (LocalReference intT (UnName 1)) intPtrT []
      , UnName 3 := Load False (LocalReference intPtrT (UnName 2)) Nothing 0 []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 3))) [])
    ]
  }

testFun :: Definition
testFun = GlobalDefinition $ functionDefaults
  { name = "testf"
  , parameters = ([Parameter intT "x" []], False)
  , returnType = intT
  , G.callingConvention = CC.Fast
  , basicBlocks =
    [ BasicBlock (UnName 0)
      [ UnName 4 := ICmp IP.EQ zero zero []
      ]
      (Do $ CondBr (LocalReference boolT (UnName 4)) (UnName 1) (UnName 2) [])
    , BasicBlock (UnName 1) []
      (Do $ Br (UnName 3) [])
    , BasicBlock (UnName 2) []
      (Do $ Br (UnName 3) [])
    , BasicBlock (UnName 3)
      [ UnName 5 := Phi intT [(zero, UnName 1), (zero, UnName 2)] []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 5))) [])
    ]
    {-
  , basicBlocks =
    [ BasicBlock "whatevs"
      [ UnName 0 := Load False (ConstantOperand (C.GetElementPtr True (C.GlobalReference heapPType heapN) [C.Int 32 0, C.Int 32 0, C.Int 32 0])) Nothing 0 []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 0))) [])
    ]
-}
    {-
toLLVM (SIL.Gate x) = do
  lx <- toLLVM x
  bool <- doInst $ ICmp IP.NE lx zero []
  doInst $ Select bool
    (ConstantOperand (C.GlobalReference intT "goRight"))
    (ConstantOperand (C.GlobalReference intT "goLeft"))
    []
  result <- doInst $ Phi intT [(ep, endElseB), (tp, endThenB)] [lComment "from_if_else"]
-}
  }
