{-#LANGUAGE OverloadedStrings #-}
{-#LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE TupleSections #-}
module MemoryBench.LLVM where

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
import           Naturals

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


benchLLVMDetails :: IExpr -> Weigh ()
benchLLVMDetails iexpr = do
    let wrap_iexpr = SetEnv (Pair (Defer iexpr) Zero)
        lmod = LLVM.makeModule $ toNExpr wrap_iexpr
    sequence_ [ func "---------------" id ()
              , benchModule lmod
              ]



benchModule :: AST.Module -> Weigh ()
benchModule amod = do
  let moduleFromAST = do
          b <- Linking.loadLibraryPermanently Nothing
          withContext $ \ctx ->
            withModuleFromAST ctx amod $ \mod -> return ()
  action "withModuleFromAST" moduleFromAST




