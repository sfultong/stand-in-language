{-# LANGUAGE LambdaCase #-}
module SIL.Possible where

import Data.Foldable
import Data.Set (Set)
import GHC.Exts (fromList)

import SIL

import qualified Data.Set as Set

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
