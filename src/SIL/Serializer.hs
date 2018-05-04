module SIL.Serializer (
    serialize
  , deserialize
  , unsafeDeserialize
) where

import Data.Word

import           Data.Vector.Storable (Vector, fromList, (!))
import qualified Data.Vector.Storable         as S
import qualified Data.Vector.Storable.Mutable as SM

import SIL.Serializer.C
import SIL (IExpr(..))


serialize :: IExpr -> Vector Word8
serialize iexpr = S.create $ do 
    vec <- SM.new $ silSize iexpr
    serialize_loop 0 vec iexpr
    return vec

silSize :: IExpr -> Int
silSize iexpr = silSize' iexpr 0

silSize' :: IExpr -> Int -> Int
silSize' Zero         acc = acc + 1
silSize' (Pair e1 e2) acc = silSize' e1 (silSize' e2 (acc + 1)) 
silSize' Env          acc = acc + 1
silSize' (SetEnv  e)  acc = silSize' e (acc + 1)
silSize' (Defer   e)  acc = silSize' e (acc + 1)
silSize' (Twiddle e)  acc = silSize' e (acc + 1)
silSize' (Abort   e)  acc = silSize' e (acc + 1)
silSize' (Gate    e)  acc = silSize' e (acc + 1)
silSize' (PLeft   e)  acc = silSize' e (acc + 1)
silSize' (PRight  e)  acc = silSize' e (acc + 1)
silSize' (Trace   e)  acc = silSize' e (acc + 1)


serialize_loop ix vec ie@Zero = SM.write vec ix (fromIntegral $ typeId ie) >> return ix
serialize_loop ix vec ie@(Pair e1 e2) = do
    SM.write vec ix (fromIntegral $ typeId ie)
    end_ix <- serialize_loop (ix+1) vec e1
    serialize_loop (end_ix+1) vec e2
serialize_loop ix vec ie@Env        = SM.write vec ix (fromIntegral $ typeId ie) >> return ix
serialize_loop ix vec ie@(SetEnv e) = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(Defer e)  = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(Twiddle e)= SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(Abort e)  = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(Gate e)   = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(PLeft e)  = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(PRight e) = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e
serialize_loop ix vec ie@(Trace e)  = SM.write vec ix (fromIntegral $ typeId ie) >> serialize_loop (ix+1) vec e

deserialize :: Vector Word8 -> Maybe IExpr
deserialize arr = if S.length arr == 0
    then Nothing
    else Just $ unsafeDeserialize arr

-- | Unsafe version of deserialize - works only with arrays of size 1 or more.
-- Undefined behaviour otherwise.
unsafeDeserialize :: Vector Word8 -> IExpr
unsafeDeserialize arr = deserializer_inside (len-2) arr [] init_expr
  where len       = S.length arr
        init_expr = case arr ! (len-1) of
          0         -> Zero
          2         -> Env
          otherwise -> error "SIL.Serializer.unsafeDeserialize: The last serialized element is not a leaf."

deserializer_inside :: Int          -- ^ Ix
                    -> Vector Word8 -- ^ Array 
                    -> [IExpr]      -- ^ Stack (for pairs)
                    -> IExpr        -- ^ Accumulator
                    -> IExpr
deserializer_inside ix arr stack acc = to_recurse_or_not
  where to_recurse_or_not   = if ix >= 0 
          then deserializer_inside (ix-1) arr new_stack new_acc  
          else acc
        (new_acc,new_stack) = case arr ! ix of
          0  -> (Zero, acc:stack)
          1  -> (Pair acc (head stack), tail stack) 
          2  -> (Env,   acc:stack)
          3  -> (SetEnv  acc, stack) 
          4  -> (Defer   acc, stack)
          5  -> (Twiddle acc, stack)
          6  -> (Abort   acc, stack)
          7  -> (Gate    acc, stack)
          8  -> (PLeft   acc, stack)
          9  -> (PRight  acc, stack)
          10 -> (Trace   acc, stack)
          err -> error $ error_msg err
        error_msg err = concat ["SIL.Serializer.deserializer_inside: Received unknown identifier ", show err, " at position ", show ix]

