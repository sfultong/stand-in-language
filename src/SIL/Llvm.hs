module SIL.Llvm where

import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Int (Int64)
import Foreign.Ptr (FunPtr, castFunPtr, Ptr, plusPtr, castPtr)
import Foreign.Storable (peek)

import LLVM.AST
import LLVM.AST.Float
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.Context
import LLVM.Module as Mod
import LLVM.PassManager

import qualified LLVM.AST as AST
import qualified LLVM.AST.AddrSpace as AddrSpace
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.Linkage as Linkage
import qualified LLVM.AST.Visibility as Visibility
import qualified LLVM.ExecutionEngine as EE

import qualified SIL as SIL

-- TODO figure out if alignment will be an issue when reading LLVM result

{-
foreign import ccall "dynamic" haskFun :: FunPtr (IO Double) -> IO Double

run :: FunPtr a -> IO Double
run fn = haskFun (castFunPtr fn :: FunPtr (IO Double))
-}

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Int64)) -> IO (Ptr Int64)

run :: FunPtr a -> IO (Int64, [(Int64,Int64)])
run fn = do
  result <- haskFun (castFunPtr fn :: FunPtr (IO (Ptr Int64)))
  numPairs <- peek result
  resultPair <- peek (plusPtr result 8)
  startHeap <- peek (plusPtr result 16)
  {-
  print numPairs
  print resultPair
  print (startHeap :: Ptr Int64)
-}
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

makeModule :: SIL.IExpr -> AST.Module
makeModule iexpr = defaultModule
  { moduleDefinitions =
    [ pairTypeDef, pairHeap, functionHeap, heapIndex, functionHeapIndex, resultStructure, goLeft, goRight ]
    ++ (toLLVM' iexpr)
  , moduleName = "SILModule"
  }

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c optlevel model ptrelim fastins
  where
    optlevel = Just 0  -- optimization level
    model    = Nothing -- code model ( Default )
    ptrelim  = Nothing -- frame pointer elimination
    fastins  = Nothing -- fast instruction selection

passes :: PassSetSpec
passes = defaultCuratedPassSetSpec { optLevel = Just 3 }

runJIT :: AST.Module -> IO (Either String AST.Module)
runJIT mod = do
  withContext $ \context ->
    jit context $ \executionEngine ->
      runExceptT $ withModuleFromAST context mod $ \m ->
        withPassManager passes $ \pm -> do
          -- Optimization Pass
          {-runPassManager pm m-}
          optmod <- moduleAST m
          s <- moduleLLVMAssembly m
          let heapInitializerIgnoreCount = 6
          putStrLn . unlines . drop heapInitializerIgnoreCount . lines $ s

          EE.withModuleInEngine executionEngine m $ \ee -> do
            mainfn <- EE.getFunction ee (AST.Name "main")
            case mainfn of
              Just fn -> do
                print fn
                res <- run fn
                putStrLn $ "Evaluated to: " ++ show (convertPairs res)
              Nothing -> putStrLn "Couldn't find entry point"

          -- Return the optimized module
          return optmod

evalJIT :: AST.Module -> IO (Either String SIL.IExpr)
evalJIT mod = do
  withContext $ \context ->
    jit context $ \executionEngine ->
      runExceptT $ withModuleFromAST context mod $ \m ->
        withPassManager passes $ \pm -> do
          -- Optimization Pass
          {-runPassManager pm m-}
    {-
          optmod <- moduleAST m
          -- print optmod
          s <- moduleLLVMAssembly m
          let heapInitializerIgnoreCount = 6
          putStrLn . unlines . drop heapInitializerIgnoreCount . lines $ s
-}

          EE.withModuleInEngine executionEngine m $ \ee -> do
            mainfn <- EE.getFunction ee (AST.Name "main")
            case mainfn of
              Just fn -> do
                res <- run fn
                pure $ convertPairs res
              Nothing -> do
                putStrLn "Couldn't find entry point"
                pure SIL.Zero

define ::  Type -> String -> [(Type, Name)] -> [BasicBlock] -> Definition
define retty label argtys body =
  GlobalDefinition $ functionDefaults {
    name        = Name label
  , parameters  = ([Parameter ty nm [] | (ty, nm) <- argtys], False)
  , returnType  = retty
  , basicBlocks = body
}
-- block instruction list (reversed), instruction counter, definition list, definition counter
type FunctionState a = State ([Named Instruction], Word, [Definition], Word) a

startFunctionState :: ([Named Instruction], Word, [Definition], Word)
startFunctionState = ([], 0, [], 0)

double :: Type
double = FloatingPointType 64 IEEE

intT :: Type
intT = IntegerType 64

boolT :: Type
boolT = IntegerType 1

intPtrT :: Type
intPtrT = PointerType (IntegerType 64) $ AddrSpace.AddrSpace 0

funT :: Type
funT = PointerType (FunctionType intT [intT] False) (AddrSpace.AddrSpace 0)

blks = [testBlock]

mainDef = define double "main2" [] blks

testBlock :: BasicBlock
testBlock = BasicBlock (UnName 0) []
  (UnName 1 := Ret (Just . ConstantOperand . C.Float . Double $ 5.5) [])

pairTypeDef :: Definition
pairTypeDef = TypeDefinition (Name "pair_type") . Just
  $ StructureType False [intT, intT]

pairT :: Type
pairT = NamedTypeReference $ Name "pair_type"

heapType :: Type
heapType = ArrayType heapSize pairT

functionHeapType :: Type
functionHeapType = ArrayType functionHeapSize funT

heapSize = 65536
functionHeapSize = 70000

emptyPair :: C.Constant
emptyPair = C.Struct Nothing False [C.Int 64 (-1), C.Int 64 (-1)]

heapN :: Name
heapN = Name "heap"

pairHeap :: Definition
pairHeap = GlobalDefinition
  $ globalVariableDefaults
  { name = heapN
  , LLVM.AST.Global.type' = heapType
  , initializer = Just (C.Array (StructureType False [intT, intT])
                        . take (fromIntegral heapSize) $ repeat emptyPair)
  }

functionHeap ::Definition
functionHeap = GlobalDefinition
  $ globalVariableDefaults
  { name = functionHeapN
  , LLVM.AST.Global.type' = functionHeapType
  , initializer = Just (C.Array funT . take (fromIntegral functionHeapSize) $ repeat (C.Null funT))
  }

functionHeapN :: Name
functionHeapN = Name "functionHeap"

heapIndexN :: Name
heapIndexN = Name "heapIndex"

-- index of next free pair structure
heapIndex :: Definition
heapIndex = GlobalDefinition
  $ globalVariableDefaults
  { name = heapIndexN
  , LLVM.AST.Global.type' = intT
  , initializer = Just (C.Int 64 0)
  }

functionHeapIndexN :: Name
functionHeapIndexN = Name "functionHeapIndex"

functionHeapIndex :: Definition
functionHeapIndex = GlobalDefinition
 $ globalVariableDefaults
 { name = functionHeapIndexN
 , LLVM.AST.Global.type' = intT
 , initializer = Just (C.Int 64 0)
 }

resultStructureN :: Name
resultStructureN = Name "resultStructure"

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
zero32 :: Operand
zero32 = ConstantOperand (C.Int 32 0)
one :: Operand
one = ConstantOperand (C.Int 64 1)
one32 :: Operand
one32 = ConstantOperand (C.Int 32 1)
two32 :: Operand
two32 = ConstantOperand (C.Int 32 2)
negOne :: Operand
negOne = ConstantOperand (C.Int 64 (-1))

doInst :: Instruction -> FunctionState Operand
doInst inst = state $ \(l, c, d, dc) ->
  if c == maxBound
  then error "BasicBlock instruction limit reached"
  else (LocalReference intT $ UnName c, ((UnName c := inst) : l, c + 1, d, dc))

-- goLeft (0) and goRight (1) are added to beginning of function heap to facilitate gate functionality
startMain :: FunctionState ()
startMain = do
  funHeap <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT functionHeapIndexN)) Nothing 0 []
  funPtr <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference functionHeapType functionHeapN))
    [zero, funHeap] []
  _ <- doInst $ Store False funPtr (ConstantOperand (C.GlobalReference intT (Name "goLeft"))) Nothing 0 []
  h2 <- doInst $ AST.Add False False funHeap one []
  fp2 <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference functionHeapType functionHeapN))
    [zero, h2] []
  _ <- doInst $ Store False fp2 (ConstantOperand (C.GlobalReference intT (Name "goRight"))) Nothing 0 []
  h3 <- doInst $ AST.Add False False h2 one []
  _ <- doInst $ Store False (ConstantOperand (C.GlobalReference intT functionHeapIndexN)) h3 Nothing 0 []
  --TODO figure out why this dummy instruction is necessary
  _ <- doInst $ AST.Add False False zero zero []
  pure ()

toLLVM :: SIL.IExpr -> FunctionState Operand
toLLVM SIL.Zero = pure negOne
toLLVM (SIL.Pair a b) = do
  oa <- toLLVM a
  ob <- toLLVM b
  heap <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
  l <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, heap, zero32] []
  r <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, heap, one32] []
  _ <- doInst $ Store False l oa Nothing 0 []
  _ <- doInst $ Store False r ob Nothing 0 []
  nc <- doInst $ AST.Add False False heap one []
  _ <- doInst $ Store False (ConstantOperand (C.GlobalReference intT heapIndexN)) nc Nothing 0 []
  --TODO figure out why this dummy instruction is necessary
  _ <- doInst $ AST.Add False False zero zero []
  pure heap
toLLVM (SIL.Twiddle x) = do
  xp <- toLLVM x
  heap <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT heapIndexN)) Nothing 0 []
  -- get values for current pairs
  ia <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, xp, zero32] []
  ca <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, xp, one32] []
  i <- doInst $ Load False ia Nothing 0 []
  c <- doInst $ Load False ca Nothing 0 []
  cla <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, c, zero32] []
  cea <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, c, one32] []
  cl <- doInst $ Load False cla Nothing 0 []
  ce <- doInst $ Load False cea Nothing 0 []
  -- create new pairs
  nl <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, heap, zero32] []
  nr <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, heap, one32] []
  _ <- doInst $ Store False nl i Nothing 0 []
  _ <- doInst $ Store False nr ce Nothing 0 []
  p2 <- doInst $ AST.Add False False heap one []
  nl2 <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, p2, zero32] []
  nr2 <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, p2, one32] []
  _ <- doInst $ Store False nl2 cl Nothing 0 []
  _ <- doInst $ Store False nr2 heap Nothing 0 []
  nh <- doInst $ AST.Add False False p2 one []
  _ <- doInst $ Store False (ConstantOperand (C.GlobalReference intT heapIndexN)) nh Nothing 0 []
  --TODO figure out why this dummy instruction is necessary
  _ <- doInst $ AST.Add False False zero zero []
  pure p2
toLLVM (SIL.PLeft x) = do
  xp <- toLLVM x
  doInst $ AST.Call (Just Tail) CC.Fast [] (Right $ ConstantOperand (C.GlobalReference intT (Name "goLeft")))
    [(xp, [])] [] []
toLLVM (SIL.PRight x) = do
  xp <- toLLVM x
  doInst $ AST.Call (Just Tail) CC.Fast [] (Right $ ConstantOperand (C.GlobalReference intT (Name "goRight")))
    [(xp, [])] [] []
toLLVM SIL.Env = pure . LocalReference intT $ Name "env"
toLLVM (SIL.Defer x) = do
  (ins, insC, def, defC) <- get
  let (returnOp, (ins2, _, def2, defC2)) = runState (toLLVM x) ([], 0, def, defC)
      newName = Name ('f' : show defC2)
      newDef = (GlobalDefinition $ functionDefaults
                { name = newName
                , parameters = ([Parameter intT (Name "env") []], False)
                , returnType = intT
                , basicBlocks = [ BasicBlock (Name ('b' : show defC2)) (reverse ins2) (Do $ Ret (Just returnOp) [])]
                })
  put (ins, insC, newDef : def2, defC2 + 1)
  funHeap <- doInst $ Load False (ConstantOperand (C.GlobalReference intPtrT functionHeapIndexN)) Nothing 0 []
  funPtr <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference functionHeapType functionHeapN))
    [zero, funHeap] []
  _ <- doInst $ Store False funPtr (ConstantOperand (C.GlobalReference intT newName)) Nothing 0 []
  newFunHeap <- doInst $ AST.Add False False funHeap one []
  _ <- doInst $ Store False (ConstantOperand (C.GlobalReference intT functionHeapIndexN)) newFunHeap Nothing 0 []
  --TODO figure out why this dummy instruction is necessary
  _ <- doInst $ AST.Add False False zero zero []
  pure funHeap
toLLVM (SIL.SetEnv x) = do
  xp <- toLLVM x
  l <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, xp, zero32] []
  r <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, xp, one32] []
  clo <- doInst $ Load False l Nothing 0 []
  env <- doInst $ Load False r Nothing 0 []
  funPtr <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference functionHeapType functionHeapN))
    [zero, clo] []
  fun <- doInst $ Load False funPtr Nothing 0 []
  doInst $ Call (Just Tail) CC.Fast [] (Right fun) [(env, [])] [] []
toLLVM (SIL.Gate x) = do
  lx <- toLLVM x
  bool <- doInst $ ICmp IP.SGT lx negOne []
  doInst $ ZExt bool intT []
-- TODO
toLLVM (SIL.Abort _) = pure negOne
toLLVM (SIL.Trace x) = toLLVM x

finishMain :: Operand -> FunctionState Operand
finishMain result = do
  heapC <- doInst $ Load False (ConstantOperand (C.GlobalReference intT heapIndexN)) Nothing 0 []
  numPairs <- doInst $ AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN)) [zero, zero32] []
  resultPair <- doInst $ AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN)) [zero, one32] []
  heapStart <- doInst $ AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN)) [zero, two32] []
  _ <- doInst $ Store False numPairs heapC Nothing 0 []
  _ <- doInst $ Store False resultPair result Nothing 0 []
  _ <- doInst $ Store False heapStart (ConstantOperand (C.PtrToInt (C.GlobalReference heapType heapN) intT))
       Nothing 0 []
  pure $ ConstantOperand (C.GlobalReference resultStructureT resultStructureN)

toLLVM' :: SIL.IExpr -> [Definition]
toLLVM' iexpr =
  let (returnOp, (instructions, _, definitions, _)) =
        runState (startMain >> toLLVM iexpr >>= finishMain) startFunctionState
  in (GlobalDefinition $ functionDefaults
       { name = Name "main"
       , parameters = ([], False)
       , returnType = intT
       , basicBlocks = [ BasicBlock (Name "mainBlock") (reverse instructions)
                       (Do $ Ret (Just returnOp) [])
                       ]
       }
     ) : definitions

-- TODO make always inlined
goLeft :: Definition
goLeft = GlobalDefinition $ functionDefaults
  { name = Name "goLeft"
  , parameters = ([Parameter intT (Name "x") []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (Name "gl1")
      [ UnName 0 := ICmp IP.SLT (LocalReference intT (Name "x")) zero []
      ]
      (Do $ CondBr (LocalReference boolT (UnName 0)) (Name "true") (Name "false") [])
    , BasicBlock (Name "true") []
      (Do $ Br (Name "exit") [])
    , BasicBlock (Name "false")
      [ UnName 1 := AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN))
        [zero, LocalReference intT (Name "x"), zero32] []
      , UnName 2 := Load False (LocalReference intT (UnName 1)) Nothing 0 []
      ]
      (Do $ Br (Name "exit") [])
    , BasicBlock (Name "exit")
      [ UnName 3 := AST.Phi intT [(negOne, Name "true"), (LocalReference intT (UnName 2), Name "false")] []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 3))) [])
    ]
  }

-- TODO make always inlined
goRight :: Definition
goRight = GlobalDefinition $ functionDefaults
  { name = Name "goRight"
  , parameters = ([Parameter intT (Name "x") []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (Name "gr1")
      [ UnName 0 := ICmp IP.SLT (LocalReference intT (Name "x")) zero []
      ]
      (Do $ CondBr (LocalReference boolT (UnName 0)) (Name "true") (Name "false") [])
    , BasicBlock (Name "true") []
      (Do $ Br (Name "exit") [])
    , BasicBlock (Name "false")
      [ UnName 1 := AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN))
        [zero, LocalReference intT (Name "x"), one32] []
      , UnName 2 := Load False (LocalReference intT (UnName 1)) Nothing 0 []
      ]
      (Do $ Br (Name "exit") [])
    , BasicBlock (Name "exit")
      [ UnName 3 := AST.Phi intT [(negOne, Name "true"), (LocalReference intT (UnName 2), Name "false")] []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 3))) [])
    ]
  }
