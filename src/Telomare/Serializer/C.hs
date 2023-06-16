{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE ForeignFunctionInterface #-}
--{-# OPTIONS_GHC -fplugin=Foreign.Storable.Generic.Plugin #-}
--{-# OPTIONS_GHC -fplugin-opt=Foreign.Storable.Generic.Plugin:-v0 #-}
module Telomare.Serializer.C (
    -- Types
      CTypeId
    , zero_type
    , pair_type
    , env_type
    , setenv_type
    , defer_type
    , gate_type
    , pleft_type
    , pright_type
    , trace_type
    , typeId
    -- C structs
    , CRoot(..)
    , CZero(..)
    , CPair(..)
    , CEnv(..)
    , CSetEnv(..)
    , CDefer(..)
    , CGate(..)
    , CPLeft(..)
    , CPRight(..)
    , CTrace(..)
    -- Serialization and deserialization to dynamic rep
    , CRep
    , fromC
    , toC
    -- Serialization and deserialization to serialized rep
    , CSerialized
    , serializedFromC
    , serializedToC
    -- C calls
    , telomare_serialize
    , telomare_deserialize
    , telomare_free
) where

import Telomare (IExpr (..))

import Data.Vector.Storable (Vector, fromList, (!))
import qualified Data.Vector.Storable as S
import Data.Word

import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable.Generic

import GHC.Generics (Generic)

-- | Type alias for expression tag for C
type CTypeId = CUChar

zero_type    = 0
pair_type    = 1
env_type     = 2
setenv_type  = 3
defer_type   = 4
gate_type    = 5
pleft_type   = 6
pright_type  = 7
trace_type   = 8


typeId :: IExpr -> CTypeId
typeId  Zero       = zero_type
typeId (Pair  _ _) = pair_type
typeId  Env        = env_type
typeId (SetEnv  _) = setenv_type
typeId (Defer   _) = defer_type
typeId (Gate _ _ ) = gate_type
typeId (PLeft   _) = pleft_type
typeId (PRight  _) = pright_type
typeId  Trace      = trace_type

data CRep

-- | Root node, contains the whole tree.
data CRoot = CRoot CTypeId (Ptr CRep) deriving(Show, Generic, GStorable)

-- Telomare nodes. Correspond to C structs from Telomare.h files.
-- General philosophy is: Contain the tag and pointer to next node in the tree. If the node is a leaf, set pointer to null.

data CZero = CZero deriving(Show, Generic)
data CPair = CPair
    { left_type   :: CTypeId
    , right_type  :: CTypeId
    , left_value  :: Ptr CRep
    , right_value :: Ptr CRep
    } deriving(Show, Generic, GStorable)
data CGate = CGate
  { leftg_type   :: CTypeId
  , rightg_type  :: CTypeId
  , leftg_value  :: Ptr CRep
  , rightg_value :: Ptr CRep
  } deriving (Show, Generic, GStorable)
data CEnv     = CEnv deriving(Show, Generic)
data CSetEnv  = CSetEnv  CTypeId (Ptr CRep) deriving(Show, Generic, GStorable)
data CDefer   = CDefer   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable)
data CPLeft   = CPLeft   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable)
data CPRight  = CPRight  CTypeId (Ptr CRep) deriving(Show, Generic, GStorable)
data CTrace   = CTrace   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable)


-- | Obtains (hopefully valid) IExpr from C representation.
fromC :: Ptr CRoot -> IO IExpr
fromC ptr = do
    (CRoot t v) <- peek ptr
    fromC' t v

fromC' :: CTypeId -> Ptr CRep -> IO IExpr
fromC' type_id ptr = case type_id of
    x | x == zero_type    -> return Zero
    x | x == pair_type    -> do
        (CPair l_type r_type l_val r_val) <- peek $ castPtr ptr
        Pair <$> fromC' l_type l_val <*> fromC' r_type r_val
    x | x == env_type -> return Env
    x | x == setenv_type    -> do
        (CSetEnv t v) <- peek $ castPtr ptr
        SetEnv <$> fromC' t v
    x | x == defer_type   -> do
        (CDefer t v) <- peek $ castPtr ptr
        Defer <$> fromC' t v
    x | x == gate_type -> do
        (CGate l_type r_type l_val r_val) <- peek $ castPtr ptr
        Gate <$> fromC' l_type l_val <*> fromC' r_type r_val
    x | x == pleft_type    -> do
        (CPLeft t v) <- peek $ castPtr ptr
        PLeft <$> fromC' t v
    x | x == pright_type    -> do
        (CPRight t v) <- peek $ castPtr ptr
        PRight <$> fromC' t v
    x | x == trace_type    -> return Trace
    _ -> error "Telomare.Serializer.fromC': Invalid type id - possibly corrupted data."



-- | Saves the IExpr as a C representation.
toC :: IExpr -> IO (Ptr CRoot)
toC iexpr = do
    croot <- malloc
    let ptr_type  = castPtr croot
        ptr_value = castPtr $ croot `plusPtr` alignment (undefined :: CRoot)
    toC' iexpr ptr_type ptr_value
    return croot

-- Later on if derive-storable will implement handling offsets - get them from there.



toC' :: IExpr          -- ^ IExpr to traverse
             -> Ptr CTypeId    -- ^ Previous expression id
             -> Ptr (Ptr CRep) -- ^ Previous pointer to a value
             -> IO ()
toC' Zero ptr_type ptr_value = poke ptr_type zero_type >> poke ptr_value nullPtr
toC' (Pair e1 e2) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CPair)
    let align = alignment (undefined :: CPair)
        ptr_left_type   = castPtr value
        ptr_right_type  = castPtr $ value `plusPtr`        1
        ptr_left_value  = castPtr $ value `plusPtr`    align
        ptr_right_value = castPtr $ value `plusPtr` (2*align)
    poke ptr_type pair_type
    poke ptr_value $ castPtr value
    toC' e1 ptr_left_type ptr_left_value
    toC' e2 ptr_right_type ptr_right_value
toC' Env  ptr_type ptr_value = poke ptr_type env_type >> poke ptr_value nullPtr
toC' (SetEnv e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CSetEnv)
    let align      = alignment (undefined :: CSetEnv)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (Defer e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CDefer)
    let align      = alignment (undefined :: CDefer)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type defer_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (Gate e1 e2) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CPair)
    let align = alignment (undefined :: CGate)
        ptr_left_type   = castPtr value
        ptr_right_type  = castPtr $ value `plusPtr`        1
        ptr_left_value  = castPtr $ value `plusPtr`    align
        ptr_right_value = castPtr $ value `plusPtr` (2*align)
    poke ptr_type gate_type
    poke ptr_value $ castPtr value
    toC' e1 ptr_left_type ptr_left_value
    toC' e2 ptr_right_type ptr_right_value
toC' (PLeft e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CPLeft)
    let align      = alignment (undefined :: CPLeft)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type pleft_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (PRight e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CPRight)
    let align      = alignment (undefined :: CPRight)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type pright_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' Trace ptr_type ptr_value = poke ptr_type trace_type >> poke ptr_value nullPtr

-- | Tag for CSerialized structs
data CSerialized

-- | Convert serialized version to Telomare_Serialized
-- Copies the memory underneath.
serializedToC :: Vector Word8 -> IO (Ptr CSerialized)
serializedToC vec = do
    let len       = S.length vec
        max_align = max (alignment (undefined :: CULong)) (alignment (undefined :: CTypeId))
        size      = max_align + S.length vec
    ptr <- mallocBytes size
    poke (castPtr ptr) (fromIntegral len :: CULong)
    S.unsafeWith vec (\ptr_vec -> copyArray (ptr `plusPtr` max_align) ptr_vec len)
    return $ castPtr ptr

-- | Convert Telomare_Serialized version to Vector of Word8.
-- Copies the memory underneath.
serializedFromC :: Ptr CSerialized -> IO (Vector Word8)
serializedFromC ptr = do
   clen <- peek $ castPtr ptr :: IO CULong
   let len = fromIntegral clen
       max_align = max (alignment (undefined :: CULong)) (alignment (undefined :: CTypeId))
   fptr_vec <- mallocForeignPtrBytes len
   withForeignPtr fptr_vec (\ptr_vec -> copyArray ptr_vec (ptr `plusPtr` max_align) len)
   return $ S.unsafeFromForeignPtr0 fptr_vec len

-- Foreign calls from C code

foreign import ccall telomare_serialize   :: Ptr CRoot       -> IO (Ptr CSerialized)
foreign import ccall telomare_deserialize :: Ptr CSerialized -> IO (Ptr CRoot)
-- | Free the memory reserved for C dynamic representation
foreign import ccall telomare_free        :: Ptr CRoot
                                     -> IO ()

