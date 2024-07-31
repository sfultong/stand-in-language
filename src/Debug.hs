module Debug where

import Data.IORef
import System.IO.Unsafe

outputLimit :: Int
outputLimit = 10000
{-
useFile :: Bool
useFile = True

data DebugState = DebugState Handle Int

file <- openFile "debug.txt" WriteMode
hPutStrLn file "test"
-- hFlush file
hClose file
-}
data DebugState = DebugState Int

debugState :: IORef DebugState
{-# NOINLINE debugState #-}
debugState = unsafePerformIO . newIORef $ DebugState 0

-- TODO looks like debugState result isn't run once and cached, so this doesn't work :(
debugTrace' :: String -> a -> a
debugTrace' s x = unsafePerformIO $ do
  DebugState numChars <- readIORef debugState
  putStrLn s
  let newNumChars = numChars + length s
  if newNumChars > outputLimit
    then error "debug output limit reached, aborting"
    else pure x



