{-#LANGUAGE DeriveGeneric  #-}
{-#LANGUAGE DeriveAnyClass #-}
module SIL.Serializer where

import SIL (IExpr(..))

import Foreign.Ptr
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Storable.Generic

import GHC.Generics (Generic)

-- | Type alias for expression tag for C
type CTypeId = CUChar

zero_type    = 0
pair_type    = 1
env_type     = 2
setenv_type  = 3
defer_type   = 4
twiddle_type = 5
abort_type   = 6
gate_type    = 7
pleft_type   = 8
pright_type  = 9
trace_type   = 10

data CRep 

-- | Root node, contains the whole tree.
data CRoot = CRoot CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 

-- SIL nodes. Correspond to C structs from SIL.h files.
-- General philosophy is: Contain the tag and pointer to next node in the tree. If the node is a leaf, set pointer to null.

data CZero = CZero deriving(Show, Generic) 
data CPair = CPair  
    { left_type   :: CTypeId
    , right_type  :: CTypeId
    , left_value  :: Ptr CRep
    , right_value :: Ptr CRep
    } deriving(Show, Generic, GStorable) 
data CEnv     = CEnv deriving(Show, Generic) 
data CSetEnv  = CSetEnv  CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CDefer   = CDefer   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CTwiddle = CTwiddle CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CAbort   = CAbort   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CGate    = CGate    CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CPLeft   = CPLeft   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CPRight  = CPRight  CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 
data CTrace   = CTrace   CTypeId (Ptr CRep) deriving(Show, Generic, GStorable) 

-- | Obtains (hopefully valid) IExpr from C representation.
--fromC :: Ptr CRoot -> IO IExpr
--fromC ptr = do


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
toC' (Zero) ptr_type ptr_value = poke ptr_type zero_type >> poke ptr_value nullPtr
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
toC' (Env)  ptr_type ptr_value = poke ptr_type zero_type >> poke ptr_value nullPtr
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
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (Twiddle e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CTwiddle)
    let align      = alignment (undefined :: CTwiddle)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (Abort e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CAbort)
    let align      = alignment (undefined :: CAbort)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (Gate e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CGate)
    let align      = alignment (undefined :: CGate)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (PLeft e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CPLeft)
    let align      = alignment (undefined :: CPLeft)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (PRight e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CPRight)
    let align      = alignment (undefined :: CPRight)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
toC' (Trace e) ptr_type ptr_value = do
    value <- malloc :: IO (Ptr CTrace)
    let align      = alignment (undefined :: CTrace)
        next_type  = castPtr value
        next_value = castPtr $ value `plusPtr` align
    poke ptr_type setenv_type
    poke ptr_value $ castPtr value
    toC' e next_type next_value
