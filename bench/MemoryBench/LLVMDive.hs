{-#LANGUAGE OverloadedStrings #-}
{-#LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE TupleSections #-}
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
import LLVM.AST.Type hiding (void)
import LLVM.AST.Constant
import LLVM.AST.AddrSpace
import LLVM.AST.Float
import LLVM.AST.IntegerPredicate
import LLVM.AST.FloatingPointPredicate hiding (True)
import LLVM.AST.ParameterAttribute
import LLVM.AST.RMWOperation
import LLVM.AST.InlineAssembly

import LLVM.AST.Operand hiding (Module)
import qualified LLVM.AST.Operand as AST
import LLVM.AST.FunctionAttribute
import LLVM.AST.COMDAT

import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as OJ
import qualified LLVM.OrcJIT.CompileLayer as OJ
import qualified LLVM.Internal.OrcJIT.LinkingLayer as OJ.I
import qualified LLVM.Internal.FFI.OrcJIT.CompileLayer as OJ.I
import qualified LLVM.Internal.OrcJIT.IRCompileLayer as OJ.I

import qualified LLVM.CodeGenOpt as CodeGenOpt
import qualified LLVM.CodeModel as CodeModel

import           LLVM.Internal.Context
import           LLVM.Internal.Coding
import           LLVM.Internal.Module
import           LLVM.Internal.EncodeAST
import           LLVM.Internal.Global
import           LLVM.Internal.Function
import           LLVM.Internal.Attribute
import           LLVM.Internal.Type
import qualified LLVM.Internal.FFI.Context as FFI
import qualified LLVM.Internal.FFI.Module  as FFI
import qualified LLVM.Internal.FFI.Target  as FFI
import qualified LLVM.Internal.FFI.ShortByteString  as FFI
import qualified LLVM.Internal.FFI.LLVMCTypes as FFI
import qualified LLVM.Internal.FFI.PtrHierarchy as FFI
import qualified LLVM.Internal.FFI.GlobalValue as FFI
import qualified LLVM.Internal.FFI.GlobalVariable as FFI
import qualified LLVM.Internal.FFI.Builder as FFI
import qualified LLVM.Internal.FFI.Value as FFI
import qualified LLVM.Internal.FFI.Function as FFI
import qualified LLVM.Internal.FFI.GlobalAlias as FFI
import qualified LLVM.Internal.FFI.Metadata as FFI

import qualified LLVM.Internal.Target as Target
import qualified LLVM.Target as Target
import qualified LLVM.Relocation as Reloc

import qualified LLVM.AST as A
import qualified LLVM.AST.DataLayout as A
import qualified LLVM.AST.AddrSpace as A
import qualified LLVM.AST.Global as A.G

import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.State.Class
import Control.Monad.IO.Class
import qualified Data.Map as Map
import Debug.Trace
import qualified Data.ByteString as B
import Data.Foldable
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

instance NFData Context where
    rnf (Context ptr) = rnf ptr

instance NFData Module where
    rnf (Module ioref) = rnf ioref

instance NFData Target.TargetMachine where
    rnf (Target.TargetMachine ptr) = rnf ptr

instance NFData OJ.ObjectLinkingLayer where
    rnf (OJ.I.ObjectLinkingLayer ptr ioref) = rnf ptr `seq` rnf ioref 

instance NFData OJ.ModuleHandle where
    rnf (OJ.I.ModuleHandle w) = rnf w

instance NFData (OJ.IRCompileLayer a) where
    rnf (OJ.I.IRCompileLayer ptr1 ptr2 ioref) = rnf ptr1 `seq` rnf ptr2 `seq` rnf ioref

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

benchLLVMDetails :: IExpr -> IO (Weigh ())
benchLLVMDetails iexpr = do
    let wrap_iexpr = SetEnv (Pair (Defer iexpr) Zero)
        lmod = LLVM.makeModule wrap_iexpr
    bench_jit <- benchJIT lmod
    bench_OJModuleCreation <- benchOJModuleCreation lmod
    return $ sequence_ [ func "---------------" id              ()
             -- , func "LLVM.makeModule" LLVM.makeModule wrap_iexpr
              --, io   "LLVM.evalJIT"    LLVM.evalJIT    lmod
              -- , io   "myevalJIT"       myevalJIT    lmod
              , bench_jit
              , bench_OJModuleCreation
              -- , io   "loadLibraryPermanently" Linking.loadLibraryPermanently Nothing
              ]


benchOJModuleCreation :: AST.Module -> IO (Weigh ())
benchOJModuleCreation amod = do
  b' <- Linking.loadLibraryPermanently Nothing
  ctx' <- createContext
  -- withModuleFromAST ctx' amod (\mod' ->  do
  mod' <- createModule ctx' amod
  tm' <- createHostTargetMachine
  objectLayer' <- OJ.newObjectLinkingLayer
  compileLayer' <- OJ.newIRCompileLayer objectLayer' tm'
  ojmod' <- OJ.addModule compileLayer' mod' (LLVM.resolver compileLayer')

  let fn m = OJ.addModule compileLayer' m (LLVM.resolver compileLayer')

  return $ action "OJ.addModule + createModule" (fn =<< createModule ctx' amod )

benchJIT :: AST.Module -> IO (Weigh ())
benchJIT amod = do
  b' <- Linking.loadLibraryPermanently Nothing
  ctx' <- createContext
  -- withModuleFromAST ctx' amod (\mod' ->  do
  mod' <- createModule ctx' amod
  tm' <- createHostTargetMachine
  objectLayer' <- OJ.newObjectLinkingLayer
  compileLayer' <- OJ.newIRCompileLayer objectLayer' tm'
  ojmod' <- OJ.addModule compileLayer' mod' (LLVM.resolver compileLayer')
  ----
  mainSymbol' <- OJ.mangleSymbol compileLayer' "main"
  jitSymbolOrError' <- OJ.findSymbol compileLayer' mainSymbol' True
  (res, main_fn) <- case jitSymbolOrError' of
          Left err -> return $ error $ show err
          Right (OJ.JITSymbol mainFn _) -> (,mainFn) <$> LLVM.run mainFn
  ----
  -- OJ.removeModule compileLayer' ojmod'
  -- OJ.disposeCompileLayer compileLayer'
  -- OJ.disposeLinkingLayer objectLayer'
  --removing host image
  -- disposeModule mod
  -- disposeContext ctx' 
  -- return $ Right $ LLVM.convertPairs res

  let benchs = [ action "createContext" createContext 
               , action "createModule" (createModule ctx' amod)
               , action "createHostTargetMachine"  createHostTargetMachine
               , action "OJ.newObjectLinkingLayer" OJ.newObjectLinkingLayer
               , action "OJ.newIRCompileLayer" (OJ.newIRCompileLayer objectLayer' tm')
               , io   "LLVM.run" LLVM.run main_fn
               , func "LLVM.convertPairs" LLVM.convertPairs res
               ]

  return $ sequence_ benchs


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
  -- withModuleFromAST ctx' amod (\mod' ->  do
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
  -- )

-- myevalJIT :: AST.Module -> IO (Either String SIL.IExpr)
-- myevalJIT amod = do
--   b <- Linking.loadLibraryPermanently Nothing
--   withContext $ \ctx ->
--     withModuleFromAST ctx amod $ \mod -> do
--       LLVM.withTargetMachine $ \tm ->
--         OJ.withObjectLinkingLayer $ \objectLayer -> do
--           OJ.withIRCompileLayer objectLayer tm $ \compileLayer -> do
--             OJ.withModule compileLayer mod (LLVM.resolver compileLayer) $ \_ -> do
--               mainSymbol <- OJ.mangleSymbol compileLayer "main"
--               jitSymbolOrError <- OJ.findSymbol compileLayer mainSymbol True
--               case jitSymbolOrError of
--                 Left err -> do
--                   pure $ error "Couldn't find main"
--                 Right (OJ.JITSymbol mainFn _) -> do
--                   res <- LLVM.run mainFn
--                   trace (concat [show mainFn, " and ", show res]) $ pure . Right $ LLVM.convertPairs res



createContext :: IO Context
createContext = Context <$> FFI.contextCreate 

disposeContext :: Context -> IO ()
disposeContext (Context ptr) = FFI.contextDispose ptr

createModule :: Context -> AST.Module -> IO Module
createModule c amod = tmpwithModuleFromAST c amod
--createModule (Context c) (AST.Module m_id _ _ _ _) = do 
--    FFI.useAsCString m_id (\cstr -> newModule =<< FFI.moduleCreateWithNameInContext cstr c)

tmpwithModuleFromAST :: Context -> A.Module -> IO Module
tmpwithModuleFromAST context@(Context c) (A.Module moduleId sourceFileName dataLayout triple definitions) = runEncodeAST context $ do
  moduleId <- encodeM moduleId
  m <- liftIO $ (newModule =<< FFI.moduleCreateWithNameInContext moduleId c) 
  ffiMod <- readModule m
  sourceFileName' <- encodeM sourceFileName
  liftIO $ FFI.setSourceFileName ffiMod sourceFileName'
  Context context <- gets encodeStateContext
  traverse_ (setDataLayout ffiMod) dataLayout
  traverse_ (setTargetTriple ffiMod) triple
  let sequencePhases :: EncodeAST [EncodeAST (EncodeAST (EncodeAST (EncodeAST ())))] -> EncodeAST ()
      sequencePhases l = (l >>= (sequence >=> sequence >=> sequence >=> sequence)) >> (return ())
  sequencePhases $ forM definitions $ \d -> case d of
   A.TypeDefinition n t -> do
     (t', n') <- createNamedType n
     defineType n n' t'
     return $ do
       traverse_ (setNamedType t') t
       return . return . return . return $ ()

   A.COMDAT n csk -> do
     n' <- encodeM n
     csk <- encodeM csk
     cd <- liftIO $ FFI.getOrInsertCOMDAT ffiMod n'
     liftIO $ FFI.setCOMDATSelectionKind cd csk
     defineCOMDAT n cd
     return . return . return . return . return $ ()

   A.MetadataNodeDefinition i md -> return . return $ do
     t <- liftIO $ FFI.createTemporaryMDNodeInContext context
     defineMDNode i t
     return $ do
       n <- encodeM md
       liftIO $ FFI.metadataReplaceAllUsesWith (FFI.upCast t) (FFI.upCast n)
       defineMDNode i n
       return $ return ()

   A.NamedMetadataDefinition n ids -> return . return . return . return $ do
     n <- encodeM n
     ids <- encodeM (map A.MDRef ids :: [A.MDRef A.MDNode])
     nm <- liftIO $ FFI.getOrAddNamedMetadata ffiMod n
     liftIO $ FFI.namedMetadataAddOperands nm ids
     return ()

   A.ModuleInlineAssembly s -> do
     s <- encodeM s
     liftIO $ FFI.moduleAppendInlineAsm ffiMod (FFI.ModuleAsm s)
     return . return . return . return . return $ ()

   A.FunctionAttributes gid attrs -> do
     attrs <- encodeM attrs
     defineAttributeGroup gid attrs
     return . return . return . return . return $ ()

   A.GlobalDefinition g -> return . phase $ do
     eg' :: EncodeAST (Ptr FFI.GlobalValue) <- case g of
       g@(A.GlobalVariable { A.G.name = n }) -> do
         typ <- encodeM (A.G.type' g)
         g' <- liftIO $ withName n $ \gName ->
                   FFI.addGlobalInAddressSpace ffiMod typ gName
                          (fromIntegral ((\(A.AddrSpace a) -> a) $ A.G.addrSpace g))
         defineGlobal n g'
         setThreadLocalMode g' (A.G.threadLocalMode g)
         liftIO $ do
           hua <- encodeM (A.G.unnamedAddr g)
           FFI.setUnnamedAddr (FFI.upCast g') hua
           ic <- encodeM (A.G.isConstant g)
           FFI.setGlobalConstant g' ic
         return $ do
           traverse_ ((liftIO . FFI.setInitializer g') <=< encodeM) (A.G.initializer g)
           setSection g' (A.G.section g)
           setCOMDAT g' (A.G.comdat g)
           setAlignment g' (A.G.alignment g)
           setMetadata (FFI.upCast g') (A.G.metadata g)
           return (FFI.upCast g')
       (a@A.G.GlobalAlias { A.G.name = n }) -> do
         typ <- encodeM (A.G.type' a)
         as <- encodeM (A.G.addrSpace a)
         a' <- liftIO $ withName n $ \name -> FFI.justAddAlias ffiMod typ as name
         defineGlobal n a'
         liftIO $ do
           hua <- encodeM (A.G.unnamedAddr a)
           FFI.setUnnamedAddr (FFI.upCast a') hua
         return $ do
           setThreadLocalMode a' (A.G.threadLocalMode a)
           (liftIO . FFI.setAliasee a') =<< encodeM (A.G.aliasee a)
           return (FFI.upCast a')
       (A.Function _ _ _ cc rAttrs resultType fName (args, isVarArgs) attrs _ _ _ gc prefix blocks personality metadata) -> do
         typ <- encodeM $ A.FunctionType resultType [t | A.Parameter t _ _ <- args] isVarArgs
         f <- liftIO . withName fName $ \fName -> FFI.addFunction ffiMod fName typ
         defineGlobal fName f
         cc <- encodeM cc
         liftIO $ FFI.setFunctionCallingConvention f cc
         setFunctionAttributes f (AttributeList attrs rAttrs [pa | A.Parameter _ _ pa <- args])
         setPrefixData f prefix
         setSection f (A.G.section g)
         setCOMDAT f (A.G.comdat g)
         setAlignment f (A.G.alignment g)
         setGC f gc
         setPersonalityFn f personality
         forM_ blocks $ \(A.BasicBlock bName _ _) -> do
           b <- liftIO $ withName bName $ \bName -> FFI.appendBasicBlockInContext context f bName
           defineBasicBlock fName bName b
         phase $ do
           let nParams = length args
           ps <- allocaArray nParams
           liftIO $ FFI.getParams f ps
           params <- peekArray nParams ps
           forM_ (zip args params) $ \(A.Parameter _ n _, p) -> do
             defineLocal n p
             n <- encodeM n
             liftIO $ FFI.setValueName (FFI.upCast p) n
           finishInstrs <- forM blocks $ \(A.BasicBlock bName namedInstrs term) -> do
             b <- encodeM bName
             (do
               builder <- gets encodeStateBuilder
               liftIO $ FFI.positionBuilderAtEnd builder b)
             finishes <- mapM encodeM namedInstrs :: EncodeAST [EncodeAST ()]
             void (encodeM term :: EncodeAST (Ptr FFI.Instruction))
             return (sequence_ finishes)
           sequence_ finishInstrs
           locals <- gets $ Map.toList . encodeStateLocals
           forM_ [ n | (n, ForwardValue _) <- locals ] $ \n -> undefinedReference "local" n
           setMetadata (FFI.upCast f) metadata
           return (FFI.upCast f)
     return $ do
       g' <- eg'
       setLinkage g' (A.G.linkage g)
       setVisibility g' (A.G.visibility g)
       setDLLStorageClass g' (A.G.dllStorageClass g)
       return $ return ()
  return m

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
