module Naturals where

data NaturalType
  = NZeroType
  | NArrType NaturalType NaturalType
  | NPairType NaturalType NaturalType
  | NNatural

data NExpr
  = NZero
  | NPair NExpr NExpr
  | NEnv
  | NSetEnv NExpr
  | NDefer NExpr
  | NAbort NExpr
  | NGate NExpr
  | NLeft NExpr
  | NRight NExpr
  | NTrace NExpr
  | NChurch
  | NAdd NExpr NExpr
  | NMult NExpr NExpr
  | NPow NExpr NExpr
  | NITE NExpr NExpr NExpr
  deriving (Eq, Show, Ord)
