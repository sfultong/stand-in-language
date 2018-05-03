module Main where

import SIL.BadLLVM

main = do
  result <- evalJIT testModule
  print result
