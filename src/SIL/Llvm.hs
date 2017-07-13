module SIL.Llvm where

import GHC.Word (Word64, Word8)
import Control.Monad.Except
import Foreign.Ptr (FunPtr, castFunPtr, Ptr, plusPtr, castPtr)
import Foreign.Storable (peek)
import LLVM.AST
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

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Word64)) -> IO (Ptr Word64)

run :: FunPtr a -> IO (Word64, [(Word64,Word64)])
run fn = do
  result <- haskFun (castFunPtr fn :: FunPtr (IO (Ptr Word64)))
  numPairs <- (min 10) <$> peek result
  resultPair <- (min (10 :: Word64)) <$> peek (plusPtr result 8)
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

convertPairs :: (Word64, [(Word64,Word64)]) -> SIL.IExpr
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
    , makePair, testPairs, genPairs
    ]
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
            --mainfn <- EE.getFunction ee (AST.Name "main")
            mainfn <- EE.getFunction ee (AST.Name "testPairs")
            case mainfn of
              Just fn -> do
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

double :: Type
double = FloatingPointType 64 IEEE

intT :: Type
intT = IntegerType 64

blks = [testBlock]

mainDef = define double "main" [] blks

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
negOne :: Operand
negOne = ConstantOperand (C.Int 64 (-1))

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
      [ UnName 0 := Call (Just Tail) CC.Fast []
        (Right (ConstantOperand (C.GlobalReference intT (Name "genPairs"))))
        [] [] []
      , UnName 1 := Load False
        (ConstantOperand (C.GlobalReference intT heapIndexN)) Nothing 0 []
      , UnName 2 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))
        [zero, zero32] []
      , UnName 3 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))
        [zero, one32] []
      , UnName 4 := AST.GetElementPtr False
        (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))
        [zero, ConstantOperand $ C.Int 32 2] []
      , UnName 5 := Store False
        (LocalReference intT (UnName 2))
        (LocalReference intT (UnName 1)) Nothing 0 []
      , UnName 6 := Store False
        (LocalReference intT (UnName 3))
        (LocalReference intT (UnName 0)) Nothing 0 []
      , UnName 7 := Store False
        (LocalReference intT (UnName 4))
        (ConstantOperand (C.PtrToInt (C.GlobalReference heapType heapN) intT))
        Nothing 0 []
      ]
      (Do $
       Ret (Just (ConstantOperand (C.GlobalReference resultStructureT resultStructureN))) [])
    ]
  }
