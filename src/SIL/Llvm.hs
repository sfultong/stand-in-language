module SIL.Llvm where

import Control.Monad.Except
import Control.Monad.State.Strict
import Crypto.Hash.SHA256 (hashlazy)
import Data.Binary (encode)
import Data.ByteString (ByteString)
import Data.ByteString.Short (toShort)
import Data.Int (Int64)
import Data.Map.Strict (Map)
import Data.String (fromString)
import Foreign.Ptr (FunPtr, castPtrToFunPtr, wordPtrToPtr, Ptr, WordPtr(..), plusPtr, IntPtr(..), intPtrToPtr)
import Foreign.Storable (peek)
import System.Clock
import System.IO (hPutStrLn, stderr)
import Text.Printf
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map

import Naturals
import SIL (FragIndex)

