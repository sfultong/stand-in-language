module SIL.Serializer (
    serialize
  , deserialize
  , unsafeDeserialize
) where

import Data.Word

import           Data.Vector.Storable (Vector, fromList, (!))
import qualified Data.Vector.Storable as S

import SIL.Serializer.C (typeId)
import SIL (IExpr(..), monoidFold)


serialize :: IExpr -> Vector Word8
serialize iexpr = fromList bytes
    where bytes = monoidFold (\e -> [fromIntegral $ typeId e]) iexpr
          len   = length bytes

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

