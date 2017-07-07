module SIL.Llvm where

import Control.Monad.Except
import Foreign.Ptr (FunPtr, castFunPtr)
import LLVM.AST
import LLVM.AST.Constant (Constant(..))
import LLVM.AST.Float
import LLVM.AST.Global
--import LLVM.CodeModel
import LLVM.Context
import LLVM.PassManager
--import LLVM.Transforms
--import LLVM.Target
import LLVM.Module as Mod

import qualified LLVM.AST as AST
import qualified LLVM.ExecutionEngine as EE

foreign import ccall "dynamic" haskFun :: FunPtr (IO Double) -> IO Double

run :: FunPtr a -> IO Double
run fn = haskFun (castFunPtr fn :: FunPtr (IO Double))

emptyModule :: AST.Module
emptyModule = defaultModule { moduleName = "whatevs" }

testModule :: AST.Module
testModule = emptyModule { moduleDefinitions = [mainDef] }

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
          putStrLn s

          EE.withModuleInEngine executionEngine m $ \ee -> do
            mainfn <- EE.getFunction ee (AST.Name "main")
            case mainfn of
              Just fn -> do
                res <- run fn
                putStrLn $ "Evaluated to: " ++ show res
              Nothing -> return ()

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

blks = [testBlock]

mainDef = define double "main" [] blks

{-
makeBlock :: (Name, BlockState) -> BasicBlock
makeBlock (l, (BlockState _ s t)) = BasicBlock l (reverse s) (maketerm t)
  where
    maketerm (Just x) = x
maketerm Nothing = error $ "Block has no terminator: " ++ (show l)
-}
testBlock :: BasicBlock
testBlock = BasicBlock (UnName 0) []
  (UnName 1 := Ret (Just . ConstantOperand . Float . Double $ 5.5) [])
