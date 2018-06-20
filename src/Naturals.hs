module Naturals where

import Data.Int (Int64)

import SIL

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
  | NChurch Int64
  | NAdd NExpr NExpr
  | NMult NExpr NExpr
  | NPow NExpr NExpr
  | NITE NExpr NExpr NExpr
  deriving (Eq, Show, Ord)

toNExpr :: IExpr -> NExpr
toNExpr x = case x of
  Zero -> NZero
  (Pair a b) -> NPair (toNExpr a) (toNExpr b)
  Env -> NEnv
  (SetEnv x) -> NSetEnv (toNExpr x)
  (Defer x) -> NDefer (toNExpr x)
  (Twiddle x) -> toNExpr $ twiddle x -- temporary hack while Twiddle exists
  (Abort x) -> NAbort (toNExpr x)
  (Gate x) -> NGate (toNExpr x)
  (PLeft x) -> NLeft (toNExpr x)
  (PRight x) -> NRight (toNExpr x)
  (Trace x) -> NTrace (toNExpr x)
  -- TODO Church numerals and natural ops

fromNExpr :: NExpr -> IExpr
fromNExpr x = case x of
  NZero -> Zero
  (NPair a b) -> Pair (fromNExpr a) (fromNExpr b)
  NEnv -> Env
  (NSetEnv x) -> SetEnv (fromNExpr x)
  (NDefer x) -> Defer (fromNExpr x)
  (NAbort x) -> Abort (fromNExpr x)
  (NGate x) -> Gate (fromNExpr x)
  (NLeft x) -> PLeft (fromNExpr x)
  (NRight x) -> PRight (fromNExpr x)
  (NTrace x) -> Trace (fromNExpr x)
  _ -> error "TODO"
