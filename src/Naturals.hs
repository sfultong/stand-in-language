{-#LANGUAGE DeriveGeneric#-}
{-#LANGUAGE DeriveAnyClass#-}
{-#LANGUAGE GeneralizedNewtypeDeriving#-}
{-#LANGUAGE PatternSynonyms#-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE EmptyDataDecls #-}
module Naturals where

import Control.Applicative
import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.State.Lazy
import Data.Binary
import Data.Functor
import Data.Int (Int64)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import Debug.Trace
import Control.DeepSeq
import GHC.Generics

import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL

debug :: Bool
debug = True

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

data NaturalType
  = ZeroTypeN
  | PairTypeN NaturalType NaturalType
  | ArrTypeN FragIndex
  | GateTypeN
  | ChurchType
  | UnknownN
  deriving (Eq, Ord, Show)

newtype FragIndex = FragIndex { unFragIndex :: Int } deriving (Eq, Show, Ord, Enum, NFData, Generic)
newtype TypeIndex = TypeIndex { unTypeIndex :: Int } deriving (Eq, Show, Ord, Enum)

instance Binary FragIndex

data ExprFrag
  = FZero
  | FPair ExprFrag ExprFrag
  | FEnv
  | FSetEnv ExprFrag
  | FDefer FragIndex
  | FAbort ExprFrag
  | FGate ExprFrag
  | FLeft ExprFrag
  | FRight ExprFrag
  | FTrace ExprFrag
  -- complex instructions
  | FITE ExprFrag ExprFrag ExprFrag
  | FApp ExprFrag ExprFrag
  | FNum Int64
  | FToNum
  deriving (Eq, Show, Ord)

traceSet inds ft x = if elem (FragIndex 8) inds
                  then debugTrace ("env at apply index: " ++ show (ft x)) x
                  else x
-- traceSet _ x = x

data NExpr
  = NZero
  | NPair NExpr NExpr
  | NEnv
  | NSetEnv NExpr
  | NDefer FragIndex
  | NAbort NExpr
  | NGate NExpr
  | NLeft NExpr
  | NRight NExpr
  | NTrace NExpr
  | NNum Int64
  | NAdd NExpr NExpr
  | NMult NExpr NExpr
  | NPow NExpr NExpr
  {-
  | NForLoop Int64 NExpr -- for runtime, function and number of times to apply it
-}
  | NApp NExpr NExpr
  | NITE NExpr NExpr NExpr
  | NOldDefer NExpr -- can probably delete
  | NToChurch NExpr NExpr
  | NTwiddle NExpr
  | NToNum
  deriving (Eq, Show, Ord, Generic, NFData)

instance Binary NExpr

pattern NLamNum :: Int64 -> NExpr -> NExpr
pattern NLamNum x e <- NPair (NPair (NNum x) NEnv) e

pattern NPartialNum :: Int64 -> NExpr -> NExpr
pattern NPartialNum i f <- (NPair (NNum i) f)

nlam :: NExpr -> NExpr
nlam x = NPair (NOldDefer x) NEnv

type NResult = NExpr

newtype NExprs = NExprs (Map FragIndex NResult) deriving Eq

instance Show NExprs where
  show (NExprs m) =
    let showInner frag = case frag of
          NZero -> "NZero"
          (NPair a b) -> concat ["{ ", showInner a, ", ", showInner b, " }"]
          NEnv -> "NEnv"
          (NSetEnv x) -> concat ["NSetEnv (", showInner x, ")"]
          (NDefer ind) -> case Map.lookup ind m of
            Just x -> concat ["NDefer (", showInner x, ")"]
            Nothing -> concat ["ERROR undefined index in showing NExprs: ", show ind]
          (NAbort x) -> concat ["NAbort (", showInner x, ")"]
          (NGate x) -> concat ["NGate (", showInner x, ")"]
          (NLeft x) -> concat ["NLeft (", showInner x, ")"]
          (NRight x) -> concat ["NRight (", showInner x, ")"]
          (NTrace x) -> concat ["NTrace (", showInner x, ")"]
          (NAdd a b) -> concat ["NAdd (", showInner a, " ", showInner b, " )"]
          (NMult a b) -> concat ["NMult (", showInner a, " ", showInner b, " )"]
          (NPow a b) -> concat ["NPow (", showInner a, " ", showInner b, " )"]
          (NITE i t e) -> concat ["if (", showInner i, ") then (", showInner t, ") else (", showInner e, ")"]
          (NOldDefer x) -> "NOldDefer (" <> showInner x <> ")"
          x -> show x
    in case Map.minView m of
      Just (x, _) -> showInner x
      _ -> "ERROR no root to NExprs tree"

type FragState = State (FragIndex, Map FragIndex ExprFrag)

toFrag :: IExpr -> FragState ExprFrag
-- complex instructions
toFrag ToChurch = pure FToNum
toFrag (ITE i t e) = FITE <$> toFrag i <*> toFrag t <*> toFrag e
toFrag (ChurchNum x) = pure . FNum $ fromIntegral x
toFrag (App f x) = FApp <$> toFrag f <*> toFrag x
-- simple instructions
toFrag Zero = pure FZero
toFrag (Pair a b) = FPair <$> toFrag a <*> toFrag b
toFrag Env = pure FEnv
toFrag (SetEnv x) = FSetEnv <$> toFrag x
toFrag (Defer x) = do
  nx <- toFrag x
  (ei@(FragIndex i), fragMap) <- State.get
  let td = id -- trace ("adding defer " ++ show i ++ " - " ++ show nx)
  State.put (FragIndex (i + 1), td Map.insert ei nx fragMap)
  pure $ FDefer ei
toFrag (Abort x) = FAbort <$> toFrag x
toFrag (Gate x) = FGate <$> toFrag x
toFrag (PLeft x) = FLeft <$> toFrag x
toFrag (PRight x) = FRight <$> toFrag x
toFrag (Trace x) = FTrace <$> toFrag x

fromFrag :: Map FragIndex ExprFrag -> ExprFrag -> IExpr
fromFrag fragMap frag = let recur = fromFrag fragMap in case frag of
  FZero -> Zero
  (FPair a b) -> Pair (recur a) (recur b)
  FEnv -> Env
  (FSetEnv x) -> SetEnv $ recur x
  (FDefer fi) -> case Map.lookup fi fragMap of
    Nothing -> error ("fromFrag bad index " ++ show fi)
    Just subFrag -> Defer $ recur subFrag
  (FAbort x) -> Abort $ recur x
  (FGate x) -> Gate $ recur x
  (FLeft x) -> PLeft $ recur x
  (FRight x) -> PRight $ recur x
  (FTrace x) -> Trace $ recur x
  z -> error ("fromFrag TODO convert " ++ show z)

matchChurchPlus :: Map FragIndex ExprFrag -> ExprFrag -> Maybe (ExprFrag, ExprFrag)
matchChurchPlus fragMap frag =
  let lam (FPair (FDefer ind) FEnv) = Map.lookup ind fragMap
      lam _ = Nothing
      def (FDefer ind) = Map.lookup ind fragMap
      def _ = Nothing
      firstArg (FLeft FEnv) = Just ()
      firstArg _ = Nothing
      secondArg (FLeft (FRight FEnv)) = Just ()
      secondArg _ = Nothing
      app = matchApp
  in lam frag >>= lam >>= app >>= (\(a, b) -> (,) <$> (app a >>= (\(m, sa) -> secondArg sa >> pure m))
                                              <*> (app b >>= (\(c, fa) -> firstArg fa >> app c
                                                               >>= (\(n, sa) -> secondArg sa >> pure n)))
                                  )

matchChurchMult :: Map FragIndex ExprFrag -> ExprFrag -> Maybe (ExprFrag, ExprFrag)
matchChurchMult fragMap frag =
  let lam (FPair (FDefer ind) FEnv) = Map.lookup ind fragMap
      lam _ = Nothing
      def (FDefer ind) = Map.lookup ind fragMap
      def _ = Nothing
      firstArg (FLeft FEnv) = Just ()
      firstArg _ = Nothing
  in lam frag >>= matchApp >>= (\(m, a) -> (,) <$> pure m <*> (matchApp a >>= (\(n, fa) -> firstArg fa >> pure n)))

matchApp :: ExprFrag -> Maybe (ExprFrag, ExprFrag)
matchApp (FApp c i) = Just (c, i)
matchApp _ = Nothing

matchITE :: ExprFrag -> Maybe (ExprFrag, ExprFrag, ExprFrag)
matchITE (FSetEnv (FPair (FGate i) (FPair e t))) = Just (i, t, e)
matchITE _ = Nothing

fragmentExpr :: IExpr -> Map FragIndex ExprFrag
fragmentExpr iexpr = let (expr, (li, m)) = State.runState (toFrag iexpr) ((FragIndex 1), Map.empty)
                         fragMap = Map.insert (FragIndex 0) expr m
                         -- tt x = trace (show x) x
                     in fragMap

fragToNExpr :: Map FragIndex ExprFrag -> ExprFrag -> NExpr
fragToNExpr fragMap frag =
        let recur = fragToNExpr fragMap
        in case frag of
            FZero -> NZero
            FEnv -> NEnv
            (FPair a b) -> NPair (recur a) (recur b)
            (FSetEnv x) -> NSetEnv $ recur x
            (FGate x) -> NGate $ recur x
            (FLeft x) -> NLeft $ recur x
            (FRight x) -> NRight $ recur x
            (FTrace x) -> NTrace $ recur x
            (FAbort x) -> NAbort $ recur x
            (FDefer ind) -> NDefer ind
            (FNum x) -> NPair (NOldDefer (NPair (NNum x) NEnv)) NEnv
            FToNum -> NToNum
            (FITE i t e) -> NITE (recur i) (recur t) (recur e)
            (FApp c i) -> NApp (recur c) (recur i)

fragsToNExpr :: Map FragIndex ExprFrag -> Map FragIndex NResult
fragsToNExpr fragMap = Map.map (fragToNExpr fragMap) fragMap

debugShow x = x -- trace ("toNExpr\n" ++ show x) x
