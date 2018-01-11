module SIL.Llvm where

import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Int (Int64)
import Foreign.Ptr (FunPtr, castFunPtr, Ptr, plusPtr, castPtr)
import Foreign.Storable (peek)
import LLVM.AST
import qualified LLVM.AST.AddrSpace as AddrSpace
import LLVM.AST.Float
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.Context
import LLVM.PassManager
import LLVM.Module as Mod

import qualified SIL as SIL

import qualified LLVM.AST as AST
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as C
import qualified LLVM.ExecutionEngine as EE
import qualified LLVM.AST.Linkage as Linkage
import qualified LLVM.AST.Visibility as Visibility

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
  numPairs <- (min 10) <$> peek result
  resultPair <- (min (10 :: Int64)) <$> peek (plusPtr result 8)
  startHeap <- peek (plusPtr result 16)
  {-
  print numPairs
  print resultPair
  print (startHeap :: Ptr Word64)
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

emptyModule :: AST.Module
emptyModule = defaultModule { moduleName = "whatevs" }

testModule :: AST.Module
testModule = emptyModule
  { moduleDefinitions =
    [ mainDef
    , pairTypeDef
    , pairHeap, heapIndex, resultStructure
    -- , makePair, testPairs, genPairs
    ]
  }

makeModule :: SIL.IExpr -> AST.Module
makeModule iexpr = defaultModule
  { moduleDefinitions =
    [ pairTypeDef, pairHeap, heapIndex, resultStructure ] ++ (toLLVM' iexpr)
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

intPtrT :: Type
intPtrT = PointerType (IntegerType 64) $ AddrSpace.AddrSpace 0

funT :: Type
--funT = PointerType (FunctionType intT [intT] False) (AddrSpace.AddrSpace 0)
funT = PointerType (FunctionType intT [] False) (AddrSpace.AddrSpace 0)

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

heapSize = 65536
functionHeapSize = 1000

emptyPair :: C.Constant
emptyPair = C.Struct Nothing False [C.Int 64 (-1), C.Int 64 (-1)]

heapN :: Name
heapN = Name "heap"

pairHeap :: Definition
pairHeap = GlobalDefinition
  $ globalVariableDefaults
  { name = heapN
  , LLVM.AST.Global.type' = ArrayType heapSize pairT
  , initializer = Just (C.Array (StructureType False [intT, intT])
                        . take (fromIntegral heapSize) $ repeat emptyPair)
--  , unnamedAddr = Just LocalAddr
--  , linkage = Weak
  }

heapIndexN :: Name
heapIndexN = Name "heapIndex"

-- index of next free pair structure
heapIndex :: Definition
heapIndex = GlobalDefinition
  $ globalVariableDefaults
  { name = heapIndexN
  , LLVM.AST.Global.type' = intT
  , initializer = Just (C.Int 64 0)
--  , unnamedAddr = Just LocalAddr
--  , linkage = Weak
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
toLLVM _ = error "TODO toLLVM"

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
  let (returnOp, (instructions, _, definitions, _)) = runState (toLLVM iexpr >>= finishMain) startFunctionState
  in (GlobalDefinition $ functionDefaults
       { name = Name "main"
       , parameters = ([], False)
       , returnType = intT
       , basicBlocks = [ BasicBlock (Name "mainBlock") (reverse instructions)
                       (Do $ Ret (Just returnOp) [])
                       ]
       }
     ) : definitions

{-
makePair :: Definition
makePair = GlobalDefinition $ functionDefaults
  { name = Name "makePair"
  , parameters = ([Parameter intT (Name "l") []
                  ,Parameter intT (Name "r") []], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (Name "makePair1")
      [ UnName 0 := Load False
        (ConstantOperand (C.GlobalReference intT heapIndexN)) Nothing 0 []
      , UnName 1 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference heapType heapN))
        [zero, LocalReference intT (UnName 0), zero32] []
      , UnName 2 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference heapType heapN))
        [zero, LocalReference intT (UnName 0), one32] []
      , UnName 3 := Store False (LocalReference intT (UnName 1))
        (LocalReference intT (Name "l")) Nothing 0 []
      , UnName 4 := Store False (LocalReference intT (UnName 2))
        (LocalReference intT (Name "r")) Nothing 0 []
      , UnName 5 := AST.Add False False (LocalReference intT (UnName 0))
        one []
      , UnName 6 := Store False
        (ConstantOperand (C.GlobalReference intT heapIndexN))
        (LocalReference intT (UnName 5)) Nothing 0 []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 0))) [])
    ]
  }

genPairs :: Definition
genPairs = GlobalDefinition $ functionDefaults
  { name = Name "genPairs"
  , parameters = ([], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (Name "genPairs1")
      [ UnName 0 := Call (Just Tail) CC.Fast []
        (Right (ConstantOperand (C.GlobalReference intT (Name "makePair"))))
        [(negOne, []), (negOne, [])]
        [] []
      , UnName 1 := Call (Just Tail) CC.Fast []
        (Right (ConstantOperand (C.GlobalReference intT (Name "makePair"))))
        [(LocalReference intT (UnName 0), []), (negOne, [])]
        [] []
      , UnName 2 := Call (Just Tail) CC.Fast []
        (Right (ConstantOperand (C.GlobalReference intT (Name "makePair"))))
        [(LocalReference intT (UnName 1), []), (LocalReference intT (UnName 0), [])]
        [] []
      ]
      (Do $ Ret (Just (LocalReference intT (UnName 2))) [])
    ]
  }

-- test constructing pair structure to be read in Haskell land
testPairs :: Definition
testPairs = GlobalDefinition $ functionDefaults
  { name = Name "testPairs"
  , parameters = ([], False)
  , returnType = intT
  , basicBlocks =
    [ BasicBlock (Name "testPairs1")
      [ UnName 0 := Alloca funT Nothing 0 []
      , UnName 1 := Store False
        (LocalReference funT (UnName 0))
        (ConstantOperand (C.GlobalReference intT (Name "genPairs"))) Nothing 0 []
      , UnName 2 := Load False
        (LocalReference funT (UnName 0)) Nothing 0 []
      , UnName 3 := Call (Just Tail) CC.Fast []
        (Right (LocalReference funT (UnName 2)))
        [] [] []
      , UnName 4 := Load False
        (ConstantOperand (C.GlobalReference intT heapIndexN)) Nothing 0 []
      , UnName 5 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))
        [zero, zero32] []
      , UnName 6 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))
        [zero, one32] []
      , UnName 7 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))
        [zero, ConstantOperand $ C.Int 32 2] []
      , UnName 8 := Store False
        (LocalReference intT (UnName 5))
        (LocalReference intT (UnName 4)) Nothing 0 []
      , UnName 9 := Store False
        (LocalReference intT (UnName 6))
        (LocalReference intT (UnName 3)) Nothing 0 []
      , UnName 10 := Store False
        (LocalReference intT (UnName 7))
        (ConstantOperand (C.PtrToInt (C.GlobalReference heapType heapN) intT))
        Nothing 0 []
      ]
      (Do $
       Ret (Just (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))) [])
    ]
  }

-}
