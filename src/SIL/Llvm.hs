{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SIL.Llvm where

import Control.Exception
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Int (Int64)
import Debug.Trace
import Foreign.Ptr (FunPtr, castFunPtr, castPtrToFunPtr, wordPtrToPtr, Ptr, WordPtr(..), plusPtr, castPtr)
import Foreign.Storable (peek)

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
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.Linkage as Linkage
import qualified LLVM.AST.Visibility as Visibility
import qualified LLVM.ExecutionEngine as EE
import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as OJ
import qualified LLVM.Target as Target

import qualified SIL as SIL

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Int64)) -> IO (Ptr Int64)

run :: WordPtr -> IO (Int64, [(Int64,Int64)])
run fn = do
  let
    mungedPtr :: FunPtr (IO (Ptr Int64))
    mungedPtr = castPtrToFunPtr . wordPtrToPtr $ fn
  result <- haskFun mungedPtr
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
  let convertPair (-1) = SIL.Zero
      convertPair n = let (l,r) = pairs !! fromIntegral n
                      in SIL.Pair (convertPair l) (convertPair r)
  in convertPair x

packSBS :: String -> SBS.ShortByteString
packSBS = SBS.toShort . BSC.pack

makeModule :: SIL.IExpr -> AST.Module
makeModule iexpr = defaultModule
  { moduleDefinitions =
    [ pairTypeDef, pairHeap, heapIndex, resultStructure, goLeft, goRight, jumpBufTypeDef, jumpBuf ]
    ++ (toLLVM' iexpr)
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

evalJIT2 :: AST.Module -> IO (Either String SIL.IExpr)
evalJIT2 amod = do
  b <- Linking.loadLibraryPermanently Nothing
  withContext $ \ctx ->
    withModuleFromAST ctx amod $ \mod -> do
      asm <- moduleLLVMAssembly mod
      BSC.putStrLn asm
      putStrLn "really?"
      Target.withHostTargetMachine $ \tm -> do
        putStrLn "entered target machine layer"
        OJ.withObjectLinkingLayer $ \objectLayer -> do
          putStrLn "entered objectLayer"
          OJ.withIRCompileLayer objectLayer tm $ \compileLayer -> do
            putStrLn "entered compileLayer"
            OJ.withModule compileLayer mod (resolver compileLayer) $ \_ -> do
              putStrLn "entered module layer"
              mainSymbol <- OJ.mangleSymbol compileLayer $ packSBS "main"
              (OJ.JITSymbol mainFn _) <- OJ.findSymbol compileLayer mainSymbol True
              pure $ Left "whoops"

evalJIT :: AST.Module -> IO (Either String SIL.IExpr)
evalJIT amod = do
  b <- Linking.loadLibraryPermanently Nothing
  withContext $ \ctx ->
    withModuleFromAST ctx amod $ \mod ->
      Target.withHostTargetMachine $ \tm ->
        OJ.withObjectLinkingLayer $ \objectLayer ->
          OJ.withIRCompileLayer objectLayer tm $ \compileLayer ->
            OJ.withModule compileLayer mod (resolver compileLayer) $ \_ -> do
              mainSymbol <- OJ.mangleSymbol compileLayer $ packSBS "main"
              (OJ.JITSymbol mainFn _) <- OJ.findSymbol compileLayer mainSymbol True
              if mainFn == WordPtr 0
                then do
                putStrLn "Could not find main"
                pure $ error "Couldn't find main"
                else do
                  res <- run mainFn
                  pure . Right $ convertPairs res

-- name counter, block instruction list (reversed), block name, block list, definition list, definition counter
type FunctionState a = State (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word) a

startFunctionState :: (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word)
startFunctionState = (1, [], UnName 0, [], [], 0)

double :: Type
double = FloatingPointType DoubleFP

intT :: Type
intT = IntegerType 64

boolT :: Type
boolT = IntegerType 1

intPtrT :: Type
intPtrT = PointerType intT $ AddrSpace.AddrSpace 0

funT :: Type
funT = PointerType (FunctionType intT [intT] False) (AddrSpace.AddrSpace 0)

sName :: String -> Name
sName = Name . packSBS

pairTypeDef :: Definition
pairTypeDef = TypeDefinition (sName "pair_type") . Just
  $ StructureType False [intT, intT]

jumpBufType :: Type
jumpBufType = StructureType False [ArrayType 8 intT, IntegerType 32, StructureType False [ArrayType 16 intT]]

jumpBufTypeDef :: Definition
jumpBufTypeDef = TypeDefinition (sName "jump_buf_type") $ Just jumpBufType

pairT :: Type
pairT = StructureType False [intT, intT]

heapType :: Type
heapType = ArrayType heapSize pairT

heapPType :: Type
heapPType = PointerType heapType (AddrSpace.AddrSpace 0)

heapSize = 65535

emptyPair :: C.Constant
emptyPair = C.Struct Nothing False [C.Int 64 (-1), C.Int 64 (-1)]

heapN :: Name
heapN = sName "pair_heap"

pairHeap :: Definition
pairHeap = GlobalDefinition
  $ globalVariableDefaults
  { name = heapN
  , LLVM.AST.Global.type' = heapType
  , initializer = Just (C.Array pairT . take (fromIntegral heapSize) $ repeat emptyPair)
  }

jumpBufN :: Name
jumpBufN = sName "jumpBuf"

jumpBuf :: Definition
jumpBuf = GlobalDefinition
  $ globalVariableDefaults
  { name = jumpBufN
  , LLVM.AST.Global.type' = jumpBufType
  , linkage = Internal
  }

heapIndexN :: Name
heapIndexN = sName "heapIndex"

-- index of next free pair structure
heapIndex :: Definition
heapIndex = GlobalDefinition
  $ globalVariableDefaults
  { name = heapIndexN
  , LLVM.AST.Global.type' = intT
  , initializer = Just (C.Int 64 0)
  }

resultStructureN :: Name
resultStructureN = sName "resultStructure"

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
one32 :: Operand
one32 = ConstantOperand (C.Int 32 1)
two32 :: Operand
two32 = ConstantOperand (C.Int 32 2)
negOne :: Operand
negOne = ConstantOperand (C.Int 64 (-1))

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
      newName = sName ('f' : show defC2)
      newDef = (GlobalDefinition $ functionDefaults
                { name = newName
                , parameters = ([Parameter intT (sName "env") []], False)
                , returnType = intT
                , basicBlocks = reverse blks2
                })
  put (c, ins, n, blks, newDef : def2, defC2 + 1)
  doInst $ PtrToInt (ConstantOperand (C.GlobalReference funT newName)) intT []

heapC :: Operand
heapC = ConstantOperand (C.GlobalReference heapPType heapN)

pairOffC :: Operand
pairOffC = ConstantOperand (C.Int 64 16)

-- put "official" start of heap at index one for pointer arithmetic trick for left/right on zero
leftStartC :: Operand
leftStartC = ConstantOperand (C.Add False False (C.PtrToInt (C.GlobalReference heapPType heapN) intT) (C.Int 64 16))

rightStartC :: Operand
rightStartC = ConstantOperand (C.Add True True (C.PtrToInt (C.GlobalReference heapPType heapN) intT) (C.Int 64 24))

makePair :: Operand -> Operand -> FunctionState Operand
makePair a b = do
  heap <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
  l <- doInst $ AST.GetElementPtr False heapC [zero, heap, zero] []
  r <- doInst $ AST.GetElementPtr False heapC [zero, heap, one] []
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
envC = LocalReference intT $ sName "env"

lComment :: String -> (SBS.ShortByteString, MetadataNode)
lComment s = (packSBS s, MetadataNode [])

toLLVM :: SIL.IExpr -> FunctionState Operand
-- chunks of AST that can be translated to optimized instructions
toLLVM (SIL.SetEnv (SIL.Pair (SIL.Gate i) (SIL.Pair e t))) = do
  ip <- toLLVM i
  elseB <- getName
  thenB <- getName
  exitB <- getName
  brCond <- doTypedInst boolT $ ICmp IP.SLT ip zero [lComment "optimized_if_conditional"]
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
toLLVM SIL.Zero = pure negOne
toLLVM (SIL.Pair a b) = do
  oa <- toLLVM a
  ob <- toLLVM b
  makePair oa ob
toLLVM (SIL.Twiddle x) = do
  xp <- toLLVM x
  -- get values for current pairs
  ia <- doInst $ AST.GetElementPtr False heapC [zero, xp, zero] []
  ca <- doInst $ AST.GetElementPtr False heapC [zero, xp, one] []
  i <- doInst $ Load False ia Nothing 0 []
  c <- doInst $ Load False ca Nothing 0 []
  cla <- doInst $ AST.GetElementPtr False heapC [zero, c, zero] []
  cea <- doInst $ AST.GetElementPtr False heapC [zero, c, one] []
  cl <- doInst $ Load False cla Nothing 0 []
  ce <- doInst $ Load False cea Nothing 0 []
  -- create new pairs
  nenv <- makePair i ce
  makePair cl nenv
toLLVM (SIL.PLeft x) = toLLVM x >>= doLeft
toLLVM (SIL.PRight x) = toLLVM x >>= doRight
toLLVM SIL.Env = pure . LocalReference intT $ sName "env"
toLLVM (SIL.Defer x) = doFunction $ toLLVM x
toLLVM (SIL.SetEnv x) = do
  xp <- toLLVM x
  l <- doInst $ AST.GetElementPtr False heapC [zero, xp, zero] []
  r <- doInst $ AST.GetElementPtr False heapC [zero, xp, one] []
  clo <- doInst $ Load False l Nothing 0 []
  env <- doInst $ Load False r Nothing 0 []
  funPtr <- doInst $ IntToPtr clo funT []
  doInst $ Call (Just Tail) CC.Fast [] (Right funPtr) [(env, [])] [] []
toLLVM (SIL.Gate x) = do
  lx <- toLLVM x
  bool <- doInst $ ICmp IP.SGT lx negOne []
  doInst $ Select bool
    (ConstantOperand (C.GlobalReference intT (sName "goRight")))
    (ConstantOperand (C.GlobalReference intT (sName "goLeft")))
    []
-- TODO
toLLVM (SIL.Abort _) = pure negOne
toLLVM (SIL.Trace x) = toLLVM x

resultC :: Operand
resultC = ConstantOperand $ C.GlobalReference (PointerType resultStructureT (AddrSpace.AddrSpace 0)) resultStructureN

finishMain :: Operand -> FunctionState Name
finishMain result = do
  heapC <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
  numPairs <- doInst $ AST.GetElementPtr False resultC [zero, zero] []
  resultPair <- doInst $ AST.GetElementPtr False resultC [zero, one] []
  heapStart <- doInst $ AST.GetElementPtr False resultC [zero, two32] []
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
       { name = sName "main"
       , parameters = ([], False)
       , returnType = PointerType resultStructureT (AddrSpace.AddrSpace 0)
       , basicBlocks = reverse blocks
       }
     ) : definitions


--- TODO make always inlined
goLeft :: Definition
goLeft = GlobalDefinition $ functionDefaults
  { name = sName "goLeft"
  , parameters = ([Parameter intT (sName "x") []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (sName "gl1")
      [ UnName 0 := Mul False False (LocalReference intT (sName "x")) pairOffC []
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
  { name = sName "goRight"
  , parameters = ([Parameter intT (sName "x") []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (sName "gr1")
      [ UnName 0 := Mul False False (LocalReference intT (sName "x")) pairOffC []
      , UnName 1 := Add False False rightStartC (LocalReference intT (UnName 0)) []
      , UnName 2 := IntToPtr (LocalReference intT (UnName 1)) intPtrT []
      , UnName 3 := Load False (LocalReference intPtrT (UnName 2)) Nothing 0 []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 3))) [])
    ]
  }
