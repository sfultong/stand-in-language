{-#LANGUAGE DeriveGeneric#-}
{-#LANGUAGE DeriveAnyClass#-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE EmptyDataDecls #-}
module Naturals where

import Data.Binary
import Data.Int (Int64)
import Control.DeepSeq
import GHC.Generics

import SIL

data NaturalType
  = Unnatural
  | NArrType NaturalType NaturalType
  | NPairType NaturalType NaturalType
  | NNatural Int

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
  deriving (Eq, Show, Ord, Generic, NFData)

instance Binary NExpr

{-
data NZeroType
data NArrType a b
data NPairType a b
data NNatural = NNatural Int

data NExpr a where
  NZero :: NExpr NZeroType
  NPair :: NExpr a -> NExpr b -> NExpr (NPairType a b)

      modR c@(RPair (RDefer (RPair (RDefer (apps)) RVar)) RVar) = let appCount = countApps 0 apps in
        if appCount > 0
        then RChurch appCount Nothing
        else c
      modR x = x
      countApps x (RLeft RVar) = x
      countApps x (RSetEnv (RTwiddle (RPair ia (RLeft (RRight RVar))))) = countApps (x + 1) ia
      countApps _ _ = 0
-}

toNExpr :: IExpr -> NExpr
toNExpr x = case x of
  Zero -> NZero
  (Pair a b) -> NPair (toNExpr a) (toNExpr b)
  Env -> NEnv
  (SetEnv x) -> NSetEnv (toNExpr x)
  (Defer x) -> NDefer (toNExpr x)
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
