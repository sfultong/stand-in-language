{-#LANGUAGE OverloadedStrings #-}
{-#LANGUAGE ScopedTypeVariables #-}
module MemoryBench.LLVMDive where

import LLVM.Module hiding (Module)
import LLVM.Context
import qualified LLVM.AST as AST
import LLVM.AST hiding (Module)
import LLVM.AST.DataLayout
import LLVM.AST.ThreadLocalStorage
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.Visibility
import LLVM.AST.DLL
import LLVM.AST.Type
import LLVM.AST.Constant
import LLVM.AST.AddrSpace
import LLVM.AST.Float
import LLVM.AST.IntegerPredicate
import LLVM.AST.FloatingPointPredicate hiding (True)
import LLVM.AST.ParameterAttribute
import LLVM.AST.RMWOperation
import LLVM.AST.InlineAssembly

import LLVM.AST.Operand
import LLVM.AST.FunctionAttribute
import LLVM.AST.COMDAT

import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as OJ
import qualified LLVM.OrcJIT.CompileLayer as OJ
import qualified LLVM.CodeGenOpt as CodeGenOpt
import qualified LLVM.CodeModel as CodeModel

import           LLVM.Internal.Context
import           LLVM.Internal.Coding
import           LLVM.Internal.Module
import qualified LLVM.Internal.FFI.Context as FFI
import qualified LLVM.Internal.FFI.Module  as FFI
import qualified LLVM.Internal.FFI.Target  as FFI
import qualified LLVM.Internal.FFI.ShortByteString  as FFI
import qualified LLVM.Internal.FFI.LLVMCTypes as FFI


import qualified LLVM.Internal.Target as Target
import qualified LLVM.Target as Target
import qualified LLVM.Relocation as Reloc

import Control.DeepSeq
import Control.Exception
import Control.Monad
import qualified Data.Map as Map
import Debug.Trace
import qualified Data.ByteString as B
import Foreign.Ptr
import Foreign.C.String

import           SIL
import qualified SIL.Llvm as LLVM

import Weigh


instance NFData DataLayout
instance NFData Endianness
instance NFData Mangling
instance NFData AddrSpace
instance NFData AlignmentInfo
instance NFData AlignType

instance NFData Definition
instance NFData Global
instance NFData Linkage
instance NFData Visibility
instance NFData StorageClass
instance NFData Model
instance NFData UnnamedAddr
instance NFData CallingConvention
instance NFData ParameterAttribute
instance NFData Parameter
instance NFData BasicBlock

instance NFData Constant
instance NFData SomeFloat
instance NFData IntegerPredicate
instance NFData FloatingPointPredicate

instance NFData Type
instance NFData FloatingPointType

instance NFData a => NFData (Named a)
instance NFData Instruction
instance NFData FastMathFlags
instance NFData SynchronizationScope
instance NFData Terminator
instance NFData MemoryOrdering
instance NFData RMWOperation
instance NFData InlineAssembly
instance NFData TailCallKind
instance NFData Dialect
instance NFData LandingPadClause

instance (NFData a) => NFData (MDRef a)
instance NFData MDNode
instance NFData DINode
instance NFData DIObjCProperty
instance NFData DIVariable
instance NFData DIMacroNode
instance NFData DIMacroInfo
instance NFData DILocation
instance NFData DILocalScope
instance NFData DILexicalBlockBase
instance NFData DIScope
instance NFData DINamespace
instance NFData DIModule
instance NFData DICompileUnit
instance NFData DIImportedEntity
instance NFData ImportedEntityTag
instance NFData DebugEmissionKind
instance NFData DIGlobalVariableExpression
instance NFData DIGlobalVariable
instance NFData ChecksumKind
instance NFData DIType
instance NFData DIDerivedType
instance NFData DerivedTypeTag
instance NFData DIBasicType
instance NFData BasicTypeTag
instance NFData DICompositeType
instance NFData DITemplateParameter
instance NFData DIEnumerator
instance NFData TemplateValueParameterTag
instance NFData DISubprogram
instance NFData DILocalVariable
instance NFData Virtuality
instance NFData DISubroutineType
instance NFData DIFlag
instance NFData DIAccessibility
instance NFData DIInheritance
instance NFData DISubrange
instance NFData Encoding
instance NFData DIFile
instance NFData DIExpression
instance NFData DWOp
instance NFData DWOpFragment

instance NFData Name
instance NFData MetadataNodeID
instance NFData Metadata
instance NFData Operand
instance NFData GroupID
instance NFData FunctionAttribute
instance NFData SelectionKind

instance NFData AST.Module



benchEval :: IExpr -> IO IExpr
benchEval iexpr = do
  let lmod = LLVM.makeModule iexpr
  result <- catch (myevalJIT lmod) $ \(e :: SomeException) -> pure . Left $ show e
  case result of
    Left s -> do
      fail s
    Right x -> do
      pure x

localEval :: IExpr -> IO IExpr
localEval iexpr = benchEval (SetEnv (Pair (Defer iexpr) Zero))

benchLLVMDetails :: IExpr -> Weigh ()
benchLLVMDetails iexpr = do
    let wrap_iexpr = SetEnv (Pair (Defer iexpr) Zero)
        lmod = LLVM.makeModule wrap_iexpr
    sequence_ [ io   "llvmDiveEval"    myevalJIT lmod       
              , func "---------------" id              ()
              , func "LLVM.makeModule" LLVM.makeModule wrap_iexpr
              , io   "LLVM.evalJIT"    LLVM.evalJIT    lmod
              , io   "myevalJIT"       myevalJIT    lmod
              , io   "loadLibraryPermanently" Linking.loadLibraryPermanently Nothing
              ]


-- OJ.addModule
-- removeModule
-- OJ.withModule
-- 
-- OJ.newObjectLinkingLayer
-- disposeLinkingLayer
-- OJ.newIRCompileLayer
-- disposeCompileLayer



myevalJIT :: AST.Module -> IO (Either String SIL.IExpr)
myevalJIT amod = do
  b' <- Linking.loadLibraryPermanently Nothing
  ctx' <- createContext
  mod' <- createModule ctx' amod
  tm' <- createHostTargetMachine
  objectLayer' <- OJ.newObjectLinkingLayer
  compileLayer' <- OJ.newIRCompileLayer objectLayer' tm'
  ojmod' <- OJ.addModule compileLayer' mod' (LLVM.resolver compileLayer')
  ----
  mainSymbol' <- OJ.mangleSymbol compileLayer' "main"
  print mainSymbol'
  jitSymbolOrError' <- OJ.findSymbol compileLayer' mainSymbol' True
  ret <-case jitSymbolOrError' of
          Left err -> return $ error $ show err
          Right (OJ.JITSymbol mainFn _) -> do
              res <- LLVM.run mainFn
              return $ Right $ LLVM.convertPairs res
  ----
  OJ.removeModule compileLayer' ojmod'
  OJ.disposeCompileLayer compileLayer'
  OJ.disposeLinkingLayer objectLayer'
  --removing host image
  -- disposeModule mod
  disposeContext ctx'
  return ret

-- evalJIT :: AST.Module -> IO (Either String SIL.IExpr)
-- evalJIT amod = do
--   b <- Linking.loadLibraryPermanently Nothing
--   withContext $ \ctx ->
--     withModuleFromAST ctx amod $ \mod -> do
--       when debug $ do
--         asm <- moduleLLVMAssembly mod
--         BSC.putStrLn asm
--       withTargetMachine $ \tm ->
--         OJ.withObjectLinkingLayer $ \objectLayer -> do
--           debugLog "in objectlinkinglayer"
--           OJ.withIRCompileLayer objectLayer tm $ \compileLayer -> do
--             debugLog "in compilelayer"
--             OJ.withModule compileLayer mod (resolver compileLayer) $ \_ -> do
--               debugLog "in modulelayer"
--               mainSymbol <- OJ.mangleSymbol compileLayer "main"
--               jitSymbolOrError <- OJ.findSymbol compileLayer mainSymbol True
--               case jitSymbolOrError of
--                 Left err -> do
--                   debugLog ("Could not find main: " <> show err)
--                   pure $ error "Couldn't find main"
--                 Right (OJ.JITSymbol mainFn _) -> do
--                   debugLog "running main"
--                   res <- run mainFn
--                   trace (concat [show mainFn, " and ", show res]) $ pure . Right $ convertPairs res



createContext :: IO Context
createContext = Context <$> FFI.contextCreate 

disposeContext :: Context -> IO ()
disposeContext (Context ptr) = FFI.contextDispose ptr

createModule :: Context -> AST.Module -> IO Module
createModule (Context c) (AST.Module m_id _ _ _ _) = do 
    FFI.useAsCString m_id (\cstr -> newModule =<< FFI.moduleCreateWithNameInContext cstr c)

disposeModule :: Module -> IO ()
disposeModule mod = FFI.disposeModule =<< readModule mod

--Lil helper
encodeFeatures = B.intercalate "," . map (\(Target.CPUFeature f, enabled) -> (if enabled then "+" else "-") <> f) . Map.toList 

createHostTargetMachine :: IO Target.TargetMachine
createHostTargetMachine = do
  Target.initializeAllTargets
  triple <- Target.getProcessTargetTriple
  cpu <- Target.getHostCPUName
  features <- encodeFeatures <$> Target.getHostCPUFeatures
  -- features <- encodeM features'
  -- features <- encodeM $ Target.getHostCPUFeatures
  ((Target.Target target), _) <- Target.lookupTarget Nothing triple
  (Target.TargetOptions options) <- createTargetOptions 
  reloc <- encodeM $ Reloc.Default
  codemodel <- encodeM $ CodeModel.JITDefault
  genopt <- encodeM $ CodeGenOpt.Default
  FFI.useAsCString triple (\ctriple -> 
    B.useAsCString  cpu (\ccpu ->
      B.useAsCString features (\cfeatures -> 
        Target.TargetMachine <$> FFI.createTargetMachine
            target
            ctriple
            ccpu
            cfeatures 
            options  
            reloc -- 
            codemodel -- 
            genopt -- 
    ) ) ) 
  
      

createTargetOptions :: IO Target.TargetOptions
createTargetOptions = Target.TargetOptions <$> FFI.createTargetOptions

-- OJ.withObjectLinkingLayer
-- OJ.withIRCompileLayer



--      LLVM.withTargetMachine $ \tm ->
--        OJ.withObjectLinkingLayer $ \objectLayer -> do
--          LLVM.debugLog "in objectlinkinglayer"
--          OJ.withIRCompileLayer objectLayer tm $ \compileLayer -> do
--            LLVM.debugLog "in compilelayer"
--            OJ.withModule compileLayer mod (LLVM.resolver compileLayer) $ \_ -> do
--              LLVM.debugLog "in modulelayer"
--              mainSymbol <- OJ.mangleSymbol compileLayer "main"
--              jitSymbolOrError <- OJ.findSymbol compileLayer mainSymbol True
--              case jitSymbolOrError of
--                Left err -> do
--                  LLVM.debugLog ("Could not find main: " <> show err)
--                  pure $ error "Couldn't find main"
--                Right (OJ.JITSymbol mainFn _) -> do
--                  LLVM.debugLog "running main"
--                  res <- LLVM.run mainFn
--                  trace (concat [show mainFn, " and ", show res]) $ pure . Right $ LLVM.convertPairs res
