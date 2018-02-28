module SIL.Llvm where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Int (Int64)
import Debug.Trace
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

foreign import ccall "dynamic" haskFun :: FunPtr (IO (Ptr Int64)) -> IO (Ptr Int64)

{-
-- TODO remove because probably unnecessary
data NExpr
  = NZero
  | NPair NExpr NExpr
  | NEnv
  | NAbort NExpr
  | NGate NExpr
  | NLeft NExpr
  | NRight NExpr
  | NTrace NExpr
  | NSetEnv NExpr
  | NDefer NExpr
  | NTwiddle NExpr
  | NITE NExpr NExpr NExpr
  deriving (Eq, Show, Ord)

instance SIL.EndoMapper NExpr where
  endoMap f NZero = f NZero
  endoMap f (NPair a b) = f $ NPair (SIL.endoMap f a) (SIL.endoMap f b)
  endoMap f NEnv = f NEnv
  endoMap f (NAbort x) = f . NAbort $ SIL.endoMap f x
  endoMap f (NGate x) = f . NGate $ SIL.endoMap f x
  endoMap f (NLeft x) = f . NLeft $ SIL.endoMap f x
  endoMap f (NRight x) = f . NRight $ SIL.endoMap f x
  endoMap f (NTrace x) = f . NTrace $ SIL.endoMap f x
  endoMap f (NSetEnv x) = f . NSetEnv $ SIL.endoMap f x
  endoMap f (NDefer x) = f . NDefer $ SIL.endoMap f x
  endoMap f (NTwiddle x) = f . NTwiddle $ SIL.endoMap f x
  endoMap f (NITE i t e) = f $ NITE (SIL.endoMap f i) (SIL.endoMap f t) (SIL.endoMap f e)

toNExpr :: SIL.IExpr -> NExpr
toNExpr SIL.Zero = NZero
toNExpr (SIL.Pair a b) = NPair (toNExpr a) (toNExpr b)
toNExpr SIL.Env = NEnv
toNExpr (SIL.Abort x) = NAbort $ toNExpr x
toNExpr (SIL.Gate x) = NGate $ toNExpr x
toNExpr (SIL.PLeft x) = NLeft $ toNExpr x
toNExpr (SIL.PRight x) = NRight $ toNExpr x
toNExpr (SIL.Trace x) = NTrace $ toNExpr x
toNExpr (SIL.SetEnv x) = NSetEnv $ toNExpr x
toNExpr (SIL.Defer x) = NDefer $ toNExpr x
toNExpr (SIL.Twiddle x) = NTwiddle $ toNExpr x
-}

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
    [ pairTypeDef, pairHeap, heapIndex, resultStructure, goLeft, goRight ]
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

-- name counter, block instruction list (reversed), block name, block list, definition list, definition counter
type FunctionState a = State (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word) a

startFunctionState :: (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word)
startFunctionState = (1, [], UnName 0, [], [], 0)

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

pairTypeDef :: Definition
pairTypeDef = TypeDefinition (Name "pair_type") . Just
  $ StructureType False [intT, intT]

pairT :: Type
pairT = NamedTypeReference $ Name "pair_type"

heapType :: Type
heapType = ArrayType heapSize pairT

heapSize = 655360

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

--startFunctionState :: (Word, [Named Instruction], Name, [BasicBlock], [Definition], Word)
doInst :: Instruction -> FunctionState Operand
doInst inst = state $ \(c, l, n, b, d, dc) ->
  if c == maxBound
  then error "BasicBlock instruction limit reached"
  else (LocalReference intT $ UnName c, (c + 1, (UnName c := inst) : l, n, b, d, dc))

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

doNamedBlock :: Name -> Terminator -> FunctionState ()
doNamedBlock name term = state $ \(c, l, n, b, d, dc) ->
  ((), (c, [], n, BasicBlock name (reverse l) (Do term) : b, d, dc))

getName :: FunctionState Name
getName = state $ \(c, l, n, b, d, dc) -> (UnName c, (c + 1, l, n, b, d, dc))

setBlockName :: Name -> FunctionState ()
setBlockName n = state $ \(c, l, _, b, d, dc) -> ((), (c, l, n, b, d, dc))

heapC = ConstantOperand (C.GlobalReference heapType heapN)

lComment :: String -> (String, MetadataNode)
lComment s = (s, MetadataNode [])

toLLVM :: SIL.IExpr -> FunctionState Operand
-- chunks of AST that can be translated to optimized instructions
toLLVM (SIL.SetEnv (SIL.Pair (SIL.Gate i) (SIL.Pair e t))) = do
  ip <- toLLVM i
  elseB <- getName
  thenB <- getName
  exitB <- getName
  -- trace ("ITE block labels: " ++ show (condB, elseB, thenB, exitB)) $ pure ()
  brCond <- doTypedInst boolT $ ICmp IP.SLT ip zero [("optimized_if_conditional", MetadataNode [])]
  _ <- doBlock (CondBr brCond elseB thenB [])

  setBlockName elseB
  ep <- toLLVM e
  endElseB <- doBlock (Br exitB [lComment "elseB"])

  setBlockName thenB
  tp <- toLLVM t
  endThenB <- doBlock (Br exitB [lComment "thenB"])

  setBlockName exitB
  result <- doInst $ Phi intT [(ep, endElseB), (tp, endThenB)] [("from_if_else", MetadataNode [])]
  -- doNamedBlock exitB (Br continueB [lComment "exitB"])
  pure result
-- single instruction translation
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
  trueB <- getName
  falseB <- getName
  exitB <- getName
  brCond <- doTypedInst boolT $ ICmp IP.SLT xp zero []
  _ <- doBlock (CondBr brCond trueB falseB [])
  doNamedBlock trueB (Br exitB [])
  setBlockName falseB
  la <- doInst $ GetElementPtr False heapC [zero, xp, zero32] []
  l <- doInst $ Load False la Nothing 0 []
  _ <- doBlock (Br exitB [])
  setBlockName exitB
  doInst $ Phi intT [(negOne, trueB), (l, falseB)] []
toLLVM (SIL.PRight x) = do
  xp <- toLLVM x
  trueB <- getName
  falseB <- getName
  exitB <- getName
  brCond <- doTypedInst boolT $ ICmp IP.SLT xp zero []
  _ <- doBlock (CondBr brCond trueB falseB [])
  doNamedBlock trueB (Br exitB [])
  setBlockName falseB
  ra <- doInst $ GetElementPtr False heapC [zero, xp, one32] []
  r <- doInst $ Load False ra Nothing 0 []
  _ <- doBlock (Br exitB [])
  setBlockName exitB
  doInst $ Phi intT [(negOne, trueB), (r, falseB)] []
toLLVM SIL.Env = pure . LocalReference intT $ Name "env"
toLLVM (SIL.Defer x) = do
  (c, ins, n, blks, def, defC) <- get
  let (_, (_, _, _, blks2, def2, defC2)) = runState (toLLVM x >>= \op -> doBlock (Ret (Just op) []))
        (1, [], UnName 0, [], def, defC)
      newName = Name ('f' : show defC2)
      newDef = (GlobalDefinition $ functionDefaults
                { name = newName
                , parameters = ([Parameter intT (Name "env") []], False)
                , returnType = intT
                , basicBlocks = reverse blks2
                })
  put (c, ins, n, blks, newDef : def2, defC2 + 1)
  doInst $ PtrToInt (ConstantOperand (C.GlobalReference intT newName)) intT []
toLLVM (SIL.SetEnv x) = do
  xp <- toLLVM x
  l <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, xp, zero32] []
  r <- doInst $ AST.GetElementPtr False (ConstantOperand (C.GlobalReference heapType heapN)) [zero, xp, one32] []
  clo <- doInst $ Load False l Nothing 0 []
  env <- doInst $ Load False r Nothing 0 []
  funPtr <- doInst $ IntToPtr clo funT []
  doInst $ Call (Just Tail) CC.Fast [] (Right funPtr) [(env, [])] [] []
toLLVM (SIL.Gate x) = do
  lx <- toLLVM x
  bool <- doInst $ ICmp IP.SGT lx negOne []
  doInst $ Select bool
    (ConstantOperand (C.GlobalReference intT (Name "goRight")))
    (ConstantOperand (C.GlobalReference intT (Name "goLeft")))
    []
-- TODO
toLLVM (SIL.Abort _) = pure negOne
toLLVM (SIL.Trace x) = toLLVM x

finishMain :: Operand -> FunctionState Name
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
  doBlock (Ret (Just $ ConstantOperand (C.GlobalReference resultStructureT resultStructureN)) [])

--getName = state $ \(c, l, n, b, d, dc) -> (UnName c, (c + 1, l, n, b, d, dc))
toLLVM' :: SIL.IExpr -> [Definition]
toLLVM' iexpr =
  let (_, (_, _, _, blocks, definitions, _)) =
        runState (toLLVM iexpr >>= finishMain) startFunctionState
  in (GlobalDefinition $ functionDefaults
       { name = Name "main"
       , parameters = ([], False)
       , returnType = intT
       , basicBlocks = reverse blocks
       }
     ) : definitions

--- TODO make always inlined
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
