{-# LANGUAGE LambdaCase #-}
module SIL.Possible where

import Control.Monad.State (State)
import Data.Foldable
import Data.Map (Map)
import Data.Set (Set)
import GHC.Exts (fromList)

import SIL

import qualified Data.DList as DList
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad.State as State

data PExpr
  = PPair PExpr PExpr
  | PDefer PExpr
  | PSetEnv PExpr
  | PEnv
  | PPLeft PExpr
  | PPRight PExpr
  | PZero
  | PGate PExpr PExpr
  | PAbort
  | PAny
  | PEither PExpr PExpr
  deriving (Eq, Show, Ord)

instance SILLike PExpr where
  fromSIL = \case
    Zero -> PZero
    Pair a b -> PPair (fromSIL a) (fromSIL b)
    Gate l r -> PGate (fromSIL l) (fromSIL r)
    Defer x -> PDefer $ fromSIL x
    SetEnv x -> PSetEnv $ fromSIL x
    Env -> PEnv
    PLeft x -> PPLeft $ fromSIL x
    PRight x -> PPRight $ fromSIL x
    Abort -> PAbort
    Trace -> PEnv
  toSIL = \case
    PZero -> pure Zero
    PPair a b -> Pair <$> toSIL a <*> toSIL b
    PGate l r -> Gate <$> toSIL l <*> toSIL r
    PDefer x -> Defer <$> toSIL x
    PSetEnv x -> SetEnv <$> toSIL x
    PEnv -> pure Env
    PPLeft x -> PLeft <$> toSIL x
    PPRight x -> PRight <$> toSIL x
    PAbort -> pure Abort
    PAny -> Nothing
    PEither _ _ -> Nothing

data ZExpr
  = ZZero
  | ZPair ZExpr ZExpr
  | ZEmbed (FragExpr BreakExtras)
  | ZAny
  | ZID -- hack for Abort function
  | ZEither ZExpr ZExpr
  deriving (Eq, Ord, Show)

zCombine :: ZExpr -> ZExpr -> ZExpr
zCombine a b = case (a,b) of
  (ZZero, ZZero) -> ZZero
  (ZEmbed a, ZEmbed b) | a == b -> ZEmbed a
  (ZID, ZID) -> ZID
  (ZAny, _) -> ZAny
  (_, ZAny) -> ZAny
  (ZPair a b, ZPair c d) | a == c -> ZPair a (zCombine b d)
  (ZPair a b, ZPair c d) | b == d -> ZPair (zCombine a c) b
  (ZEither a b, ZEither c d) -> ZEither (zCombine a c) (zCombine b d) --TODO .. maybe optimize more?
  _ -> ZEither a b

zToP :: Term3 -> Int -> ZExpr -> PExpr
zToP tm@(Term3 termMap) churchSize = let recur = zToP tm churchSize in \case
  ZZero -> PZero
  ZPair a b -> PPair (recur a) (recur b)
  ZAny -> PAny
  ZID -> error "zToP hit ZID, gonna have to thinkkkkk"
  ZEither a b -> PEither (recur a) (recur b)
  ZEmbed x -> tr x where
    tr = \case
      ZeroF -> PZero
      PairF a b -> PPair (tr a) (tr b)
      GateF l r -> PGate (tr l) (tr r)
      DeferF ind -> case Map.lookup ind termMap of
        Just x -> PDefer $ tr x
        _ -> error "zToP deferF index not found"
      SetEnvF x -> PSetEnv $ tr x
      EnvF -> PEnv
      LeftF x -> PPLeft $ tr x
      RightF x -> PPRight $ tr x
      AbortF -> PAbort
      TraceF -> error "zToP traceF not supported"
      AuxF _ -> let lamp x = PPair (PDefer x) PEnv
                    clamp x = PPair (PDefer x) PZero
                    v0 = PPLeft PEnv
                    v1 = PPLeft $ PPRight PEnv
                    twiddleP = PDefer $ PPair (PPLeft (PPRight PEnv)) (PPair (PPLeft PEnv) (PPRight (PPRight PEnv)))
                    appP c i = PSetEnv (PSetEnv (PPair twiddleP (PPair i c)))
                    toC 0 = v0
                    toC n = appP v1 (toC (n - 1))
                in clamp (lamp (toC churchSize))

type ZBuilder = State (Map FragIndex ZExpr)

zEval :: (FragIndex -> FragExpr BreakExtras) -> ZExpr -> FragExpr BreakExtras -> ZBuilder ZExpr
zEval fragLookup env =
  let recur = zEval fragLookup env
  in \case
  ZeroF -> pure ZZero
  PairF a b -> ZPair <$> recur a <*> recur b
  EnvF -> pure env
  LeftF x -> doLeft <$> recur x where
    doLeft = \case
      ZPair l _ -> l
      ZAny -> ZEither ZZero (ZPair ZAny ZAny)
      ZZero -> ZZero
      z -> error $ "zEval leftF: unexpected " <> show z
  RightF x -> doRight <$> recur x where
    doRight = \case
      ZPair _ r -> r
      ZAny -> ZEither ZZero (ZPair ZAny ZAny)
      ZZero -> ZZero
      z -> error $ "zEval rightF: unexpected " <> show z
  GateF l r -> pure . ZEmbed $ GateF l r
  SetEnvF x ->
    let setEval :: ZExpr -> ZBuilder ZExpr
        setEval = \case
                     xr@(ZPair (ZEmbed x) nenv) -> case x of
                       (GateF l r) -> case nenv of
                         ZZero -> recur l
                         ZPair _ _ -> recur r
                         ZEither a b -> do
                           nl <- setEval (ZPair (ZEmbed (GateF l r)) a)
                           nr <- setEval (ZPair (ZEmbed (GateF l r)) b)
                           pure $ zCombine nl nr
                         ZAny -> zCombine <$> recur l <*> recur r
                         -- z -> error $ "zEval setenv gate: unexpected " <> show z
                         -- just freeze computations we can't handle as-is
                         _ -> pure xr
                       AbortF -> pure ZID
                       DeferF ind -> State.modify (Map.insertWith zCombine ind env)
                                        *> zEval fragLookup nenv (fragLookup ind)
                       -- evaluate later
                       AuxF _ -> pure xr
                       -- z -> error $ "zEval setenv embed: unexpected " <> show z
                       -- just freeze computations we can't handle as-is
                       _ -> pure xr
                     ZPair (ZEither a b) nenv -> do
                       na <- setEval (ZPair a nenv)
                       nb <- setEval (ZPair b nenv)
                       pure $ zCombine na nb
                     ZPair ZID nenv -> pure nenv
                     --z -> error $ "zEval setenv: unexpected " <> show z
                     -- just freeze computations we can't handle as-is
                     xr -> pure xr
    in recur x >>= setEval
  d@(DeferF _) -> pure . ZEmbed $ d
  AbortF -> pure . ZEmbed $ AbortF
  a@(AuxF _) -> pure . ZEmbed $ a
  TraceF -> pure env

buildZInputMap :: Term3 -> Map FragIndex ZExpr
buildZInputMap (Term3 termMap) = State.execState (zEval (termMap Map.!) ZAny (rootFrag termMap)) mempty


{-
data PType
  = ZeroTypeS
  | AnyTypeS
  | TypeVariableS Int
  | EitherTypeS PType PType
  | ArrTypeS (Maybe FragIndex) (PType -> PType)
  | PairTypeS PType PType

instance Eq PType where
  (==) a b = case (a,b) of
    (ZeroTypeS, ZeroTypeS) -> True
    (AnyTypeS, AnyTypeS) -> True
    (TypeVariable x, TypeVariable y) -> x == y
    (EitherTypeS a b) -> a == b
    (ArrTypeS x _, ArrTypeS y) -> x == y
    (PairTypeS a b, PairTypeS c d) -> a == c && b == d

instance Ord PType where
  compare = let intify = \case
                  ZeroTypeS -> pure 0
                  AnyTypeS -> pure 1
                  TypeVariable x -> pure 2 <> pure x
                  ArrTypeS Nothing _ -> pure 3
                  ArrTypeS (Just x) _ -> pure 4 <> pure (fromEnum x)
                  EitherTypeS a b -> pure 5 <> intify a <> intify b
                  PairTypeS a b -> pure 6 <> intify a <> intify b
            in \a b -> compare (fmap intify a) (fmap intify b)
-}


{-
newtype PResult = PResult (Set PExpr, Bool)

instance Semigroup PResult where
  (<>) (PResult (sa, ba)) (PResult (sb, bb)) = PResult (sa <> sb, ba || bb)
instance Monoid PResult where
  mempty = PResult (Set.empty, False)
instance Eq PResult where
  (==) (PResult (sa, ba)) (PResult (sb, bb)) = sa == sb && ba == bb
instance Ord PResult where
  compare (PResult (sa, ba)) (PResult (sb, bb)) = let sr = compare sa sb
                                                  in if sr == EQ then compare ba bb else sr
-}

pEval :: (PExpr -> PExpr -> (Bool, PExpr)) -> PExpr -> PExpr -> (Bool, PExpr)
pEval f env g =
  let f' = f env
      innerMap x = flip fmap (f' x)
      pBind x pf = let (nb, nx) = f' x
                       (fb, fx) = pf nx
                   in (nb || fb, fx)
  in case g of
    PPair a b -> let (ba, na) = f' a
                     (bb, nb) = f' b
                 in (ba || bb, PPair na nb)
    PEnv -> (False, env)
    PPLeft x -> innerMap x $ \case
      PPair a _ -> a
      PAny -> PEither PZero (PPair PAny PAny)
      _ -> PZero
    PPRight x -> innerMap x $ \case
      PPair _ b -> b
      PAny -> PEither PZero (PPair PAny PAny)
      _ -> PZero
    PSetEnv x -> pBind x $ \case
      PPair cf nenv -> case cf of
        PDefer c -> f nenv c
        PGate l r -> case nenv of
          PZero -> f' l
          PAny -> let (bl, lb) = f' l
                      (br, rb) = f' r
                  in (bl || br, PEither lb rb)
          _ -> f' r
        PAbort -> case nenv of
          PZero -> (False, PDefer PEnv)
          _ -> (True, PDefer PEnv)
        _ -> error "should not be here in pEval setenv (bad cf)"
      _ -> error "should not be here in pEval setenv non pair"
    x -> (False, x)
