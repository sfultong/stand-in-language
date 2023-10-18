{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE InstanceSigs #-}
module Telomare.Possible where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader      (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader      as Reader
import           Control.Monad.State       (State, StateT)
import qualified Control.Monad.State       as State
import           Control.Monad.Trans.Class
import           Data.Bifunctor
import           Data.DList                (DList)
import qualified Data.DList                as DList
import           Data.Fix                  (Fix(..), hoistFix')
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.Kind
import           Data.List                 (sortBy)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Monoid
import           Data.SBV ((.<), (.>))
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Void
import           Debug.Trace
import           PrettyPrint
import           Telomare                  (FragExpr (..), FragExprUR (..), i2g, g2i,
                                            BreakState' (..),
                                            FragIndex, IExpr (..),
                                            PartialType (..),
                                            RecursionPieceFrag,
                                            RecursionSimulationPieces (..),
                                            TelomareLike (fromTelomare, toTelomare),
                                            Term3 (..), Term4 (..),
                                            UnsizedRecursionToken (UnsizedRecursionToken),
                                            buildFragMap, deferF,
                                            indentWithOneChild,
                                            indentWithOneChild',
                                            indentWithTwoChildren,
                                            indentWithTwoChildren',
                                            pattern AbortAny,
                                            pattern AbortRecursion, rootFrag,
                                            sindent, pattern AbortUnsizeable, IExprF (SetEnvF), indentWithChildren')
-- import           Telomare.TypeChecker
import Telomare.RunTime (hvmEval)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

anaM' :: (Monad m, Corecursive t, x ~ Base t, Traversable x) => (a -> m (Base t a)) -> a -> m t
anaM' f = c where c = join . fmap (fmap embed . sequence . fmap c) . f

testSBV :: SBV.Symbolic SBV.Word8
testSBV = do
  b <- SBV.sBool "b"
  a <- SBV.sWord8 "a"
  SBV.constrain $ a + 5 .< 10
  SBV.constrain $ a .> 2
  SBV.constrain b
  SBVC.query $ SBVC.checkSat >>= \case
      SBVC.Unk   -> undefined -- error "Solver returned unknown!"
      SBVC.Unsat -> undefined -- error "Solver couldn't solve constraints"
      SBVC.Sat   -> SBVC.getValue a

testSBV' :: IO Int
testSBV' = fromIntegral <$> SBV.runSMT testSBV

data PartExprF f
  = ZeroSF
  | PairSF f f
  | EnvSF
  | SetEnvSF f
  | GateSF f f
  | LeftSF f
  | RightSF f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 PartExprF where
  liftEq test a b = case (a,b) of
    (ZeroSF, ZeroSF)         -> True
    (EnvSF, EnvSF)           -> True
    (PairSF a b, PairSF c d) -> test a c && test b d
    (SetEnvSF x, SetEnvSF y) -> test x y
    (GateSF a b, GateSF c d) -> test a c && test b d
    (LeftSF x, LeftSF y)     -> test x y
    (RightSF x, RightSF y)   -> test x y
    _                        -> False

instance Show1 PartExprF where
  liftShowsPrec showsPrec showList prec = \case
    ZeroSF -> shows "ZeroSF"
    PairSF a b -> shows "PairSF (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
    EnvSF -> shows "EnvSF"
    SetEnvSF x -> shows "SetEnvSF (" . showsPrec 0 x . shows ")"
    GateSF l r -> shows "GateSF (" . showsPrec 0 l . shows ", " . showsPrec 0 r . shows ")"
    LeftSF x -> shows "LeftSF (" . showsPrec 0 x . shows ")"
    RightSF x -> shows "RightSF (" . showsPrec  0 x . shows ")"

newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show)

instance PrettyPrintable FunctionIndex where
  showP = pure . ("f" <>) . show . fromEnum

class Functor g => BasicBase g where
  embedB :: PartExprF x -> g x
  extractB :: g x -> Maybe (PartExprF x)

class Functor g => StuckBase g where
  type StuckData g
  embedS :: (FunctionIndex, StuckData g) -> g x
  extractS :: g x -> Maybe (FunctionIndex, StuckData g)

class SuperBase g where
  embedP :: SuperPositionF x -> g x
  extractP :: g x -> Maybe (SuperPositionF x)

class AbortBase g where
  embedA :: AbortableF x -> g x
  extractA :: g x -> Maybe (AbortableF x)

class UnsizedBase g where
  embedU :: UnsizedRecursionF x -> g x
  extractU :: g x -> Maybe (UnsizedRecursionF x)

pattern BasicFW :: BasicBase g => PartExprF x -> g x
pattern BasicFW x <- (extractB -> Just x)
pattern BasicEE :: (Base g ~ f, BasicBase f, Recursive g) => PartExprF g -> g
pattern BasicEE x <- (project -> BasicFW x)
pattern StuckFW :: (StuckBase g) => FunctionIndex -> StuckData g -> g x
pattern StuckFW fi x <- (extractS -> Just (fi, x))
pattern StuckEE :: (Base g ~ f, StuckData f ~ g, StuckBase f, Recursive g) => FunctionIndex -> g -> g
pattern StuckEE fi x <- (project -> StuckFW fi x)
pattern SuperFW :: SuperBase g => SuperPositionF x -> g x
pattern SuperFW x <- (extractP -> Just x)
pattern SuperEE :: (Base g ~ f, SuperBase f, Recursive g) => SuperPositionF g -> g
pattern SuperEE x <- (project -> (SuperFW x))
pattern AbortFW :: AbortBase g => AbortableF x -> g x
pattern AbortFW x <- (extractA -> Just x)
pattern AbortEE :: (Base g ~ f, AbortBase f, Recursive g) => AbortableF g -> g
pattern AbortEE x <- (project -> (AbortFW x))
pattern UnsizedFW :: UnsizedBase g => UnsizedRecursionF x -> g x
pattern UnsizedFW x <- (extractU -> Just x)
pattern UnsizedEE :: (Base g ~ f, UnsizedBase f, Recursive g) => UnsizedRecursionF g -> g
pattern UnsizedEE x <- (project -> (UnsizedFW x))
basicEE :: (Base g ~ f, BasicBase f, Corecursive g) => PartExprF g -> g
basicEE = embed . embedB
stuckEE :: (Base g ~ f, StuckData f ~ g, StuckBase f, Corecursive g) => FunctionIndex -> g -> g
stuckEE fi x = embed $ embedS (fi, x)
superEE :: (Base g ~ f, SuperBase f, Corecursive g) => SuperPositionF g -> g
superEE = embed . embedP
abortEE :: (Base g ~ f, AbortBase f, Corecursive g) => AbortableF g -> g
abortEE = embed . embedA
unsizedEE :: (Base g ~ f, UnsizedBase f, Corecursive g) => UnsizedRecursionF g -> g
unsizedEE = embed . embedU

pattern FillFunction :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> f g
pattern FillFunction c e <- BasicFW (SetEnvSF (BasicEE (PairSF c e)))
pattern GateSwitch :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> g -> f g
pattern GateSwitch l r s <- FillFunction (BasicEE (GateSF l r)) s

fillFunction :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> f g
fillFunction c e = embedB (SetEnvSF (basicEE (PairSF c e)))

gateSwitch :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g -> f g
gateSwitch  l r s = fillFunction (basicEE (GateSF l r)) s

basicStep :: (Base g ~ f, BasicBase f, Corecursive g, Recursive g) => (f g -> g) -> f g -> g
basicStep handleOther = \case
  BasicFW (LeftSF z@(BasicEE ZeroSF)) -> z
  BasicFW (LeftSF (BasicEE (PairSF l _))) -> l
  BasicFW (RightSF z@(BasicEE ZeroSF)) -> z
  BasicFW (RightSF (BasicEE (PairSF _ r))) -> r
  GateSwitch l _ (BasicEE ZeroSF) -> l
  GateSwitch _ r (BasicEE (PairSF _ _)) -> r
  -- stuck values
  x@(BasicFW ZeroSF) -> embed x
  x@(BasicFW (PairSF _ _)) -> embed x
  x@(BasicFW (GateSF _ _)) -> embed x
  x -> handleOther x

basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, Monad m) => (f (m g) -> m g) -> f (m g) -> m g
basicStepM handleOther x = sequence x >>= f where
  f = \case
    BasicFW (LeftSF z@(BasicEE ZeroSF)) -> pure z
    BasicFW (LeftSF (BasicEE (PairSF l _))) -> pure l
    BasicFW (RightSF z@(BasicEE ZeroSF)) -> pure z
    BasicFW (RightSF (BasicEE (PairSF _ r))) -> pure r
    GateSwitch l _ (BasicEE ZeroSF) -> pure l
    GateSwitch _ r (BasicEE (PairSF _ _)) -> pure r
    -- stuck values
    x@(BasicFW ZeroSF) -> pure $ embed x
    x@(BasicFW (PairSF _ _)) -> pure $ embed x
    x@(BasicFW (GateSF _ _)) -> pure $ embed x
    _ -> handleOther x

transformStuck :: (Base g ~ f, Base h ~ f, StuckData f ~ h, StuckBase f, Recursive g, Recursive h, Corecursive h)
  => (f h -> h) -> g -> h
transformStuck f = cata f' where
  f' = \case
    StuckFW fid x -> stuckEE fid $ cata f' x
    -- OneFW (StuckF x) -> f' . OneFW . StuckF $ cata f' x
    x -> f x

transformStuckM :: (Base g ~ f, Base h ~ f, StuckData f ~ h, StuckBase f, Recursive g, Recursive h, Corecursive h, Monad m)
  => (f (m h) -> m h) -> g -> m h
transformStuckM f = cata f' where
  f' = \case
    StuckFW fid x -> stuckEE fid <$> cata f' x
    x -> f x

stuckStep :: (Base a ~ f, StuckData f ~ a, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  FillFunction (StuckEE fid d) e -> db $ cata (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db x = if fid == toEnum 5
      then debugTrace ("stuckstep dumping output at 6:\n" <> prettyPrint e) x
      else x
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x -> x
  -- stuck value
  x@(StuckFW _ _) -> embed x
  x -> handleOther x

stuckStepM :: (Base a ~ f, StuckData f ~ a, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f (m a) -> m a) -> f (m a) -> m a
stuckStepM handleOther x = sequence x >>= f where
  f = \case
    FillFunction (StuckEE fid d) e -> cata runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = pure <$> project e
      replaceEnv = \case
        BasicFW EnvSF -> e'
        x -> x
    -- stuck value
    x@(StuckFW _ _) -> pure $ embed x
    _ -> handleOther x

evalBottomUp :: (Base t ~ f, BasicBase f, Corecursive t, Recursive t, Recursive t) => (Base t t -> t) -> t -> t
evalBottomUp handleOther = cata (basicStep handleOther)

superStep :: (Base a ~ f, BasicBase f, SuperBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> a -> a) -> (f a -> a) -> (f a -> a) -> f a -> a
superStep mergeSuper step handleOther = \case
    BasicFW (LeftSF (SuperEE AnyPF)) -> superEE AnyPF
    BasicFW (LeftSF (SuperEE (EitherPF a b))) -> mergeSuper (step . embedB . LeftSF $ a) (step . embedB . LeftSF $ b)
    BasicFW (RightSF (SuperEE AnyPF)) -> superEE AnyPF
    BasicFW (RightSF (SuperEE (EitherPF a b))) -> mergeSuper (step . embedB . RightSF $ a) (step . embedB . RightSF $ b)
    BasicFW (SetEnvSF (SuperEE (EitherPF a b))) -> mergeSuper (step . embedB . SetEnvSF $ a) (step . embedB . SetEnvSF $ b)
    (GateSwitch l r (SuperEE AnyPF)) -> mergeSuper l r
    (FillFunction (SuperEE (EitherPF sca scb)) e) -> mergeSuper
      (step . embedB . SetEnvSF . basicEE $ PairSF sca e)
      (step . embedB . SetEnvSF . basicEE $ PairSF scb e)
    -- stuck values
    x@(SuperFW AnyPF) -> embed x
    x@(SuperFW (EitherPF _ _)) -> embed x
    x -> handleOther x

superStepM :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (a -> a -> a) -> (f (m a) -> m a) -> (f (m a) -> m a) -> f (m a) -> m a
superStepM mergeSuper step handleOther x = sequence x >>= f where
  pbStep bf = step . fmap pure . embedB . bf
  f = \case
    BasicFW (LeftSF (SuperEE AnyPF)) -> pure $ superEE AnyPF
    BasicFW (LeftSF (SuperEE (EitherPF a b))) -> liftM2 mergeSuper (pbStep LeftSF a) (pbStep LeftSF b)
    BasicFW (RightSF (SuperEE AnyPF)) -> pure $ superEE AnyPF
    BasicFW (RightSF (SuperEE (EitherPF a b))) -> liftM2 mergeSuper (pbStep RightSF a) (pbStep RightSF b)
    BasicFW (SetEnvSF (SuperEE (EitherPF a b))) -> liftM2 mergeSuper (pbStep SetEnvSF a) (pbStep SetEnvSF b)
    GateSwitch l r (SuperEE AnyPF) -> pure $ mergeSuper l r
    FillFunction (SuperEE (EitherPF sca scb)) e -> liftM2 mergeSuper
      (pbStep SetEnvSF . basicEE $ PairSF sca e)
      (pbStep SetEnvSF . basicEE $ PairSF scb e)
    -- stuck values
    x@(SuperFW AnyPF) -> pure $ embed x
    x@(SuperFW (EitherPF _ _)) -> pure $ embed x
    _ -> handleOther x

abortStep :: (Base a ~ f, StuckData f ~ a, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> a
    FillFunction a@(AbortEE (AbortedF _)) _ -> a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> stuckEE i . basicEE $ EnvSF where
      i = toEnum (-1)
    -- BasicFW (FillFunction (AbortEE AbortF) (TwoEE AnyPF)) -> embed . ThreeFW . AbortedF $ AbortAny
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> abortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF        -> Zero
        BasicFW (PairSF a b)  -> Pair a b
        _ -> Zero -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> embed x
    x@(AbortFW AbortF) -> embed x
    x -> handleOther x

abortStepM :: (Base a ~ f, StuckData f ~ a, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f (m a) -> m a) -> f (m a) -> m a
abortStepM handleOther x = sequence x >>= f where
  f = \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> pure a
    FillFunction a@(AbortEE (AbortedF _)) _ -> pure a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> pure . stuckEE i . basicEE $ EnvSF where
      i = toEnum (-1)
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> pure . abortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF        -> Zero
        BasicFW (PairSF a b)  -> Pair a b
        _ -> Zero -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> pure $ embed x
    x@(AbortFW AbortF) -> pure $ embed x
    _ -> handleOther x

anyFunctionStep :: (Base a ~ f, BasicBase f, SuperBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
anyFunctionStep handleOther =
  \case
    FillFunction a@(SuperEE AnyPF) _ -> a
    x -> handleOther x

anyFunctionStepM :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, Recursive a, Corecursive a, Monad m)
  => (f (m a) -> m a) -> f (m a) -> m a
anyFunctionStepM handleOther x = sequence x >>= f where
  f = \case
    FillFunction a@(SuperEE AnyPF) _ -> pure a
    _ -> handleOther x

unsizedStep :: (Base a ~ f, BasicBase f, SuperBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => (a -> a -> a) -> (f a -> a) -> (f a -> a) -> f a -> a
unsizedStep unsizedMerge fullStep handleOther =
  let recurStep = fullStep . embedB . SetEnvSF
  in \case
    FillFunction (UnsizedEE (SizingResultsF cts crl)) (UnsizedEE (SizingResultsF ets erl)) ->
      unsizedEE . SizingResultsF (cts <> ets) . map fullStep $ zipWith fillFunction crl erl
    BasicFW (LeftSF (UnsizedEE sr@(SizingResultsF _ _))) -> unsizedEE $ fmap (fullStep . embedB . LeftSF) sr
    BasicFW (RightSF (UnsizedEE sr@(SizingResultsF _ _))) -> unsizedEE $ fmap (fullStep . embedB . RightSF) sr
    BasicFW (SetEnvSF (UnsizedEE sr@(SizingResultsF _ _))) -> unsizedEE $ fmap (fullStep . embedB . SetEnvSF) sr
    FillFunction (UnsizedEE sr@(SizingResultsF _ _)) e -> unsizedEE $ fmap (fullStep . (\c -> fillFunction c e)) sr
    GateSwitch l r (UnsizedEE sr@(SizingResultsF _ _)) -> unsizedEE $ fmap (fullStep . gateSwitch l r) sr
    UnsizedFW (UnsizedStubF t e) -> unsizedEE . SizingResultsF (Set.singleton t) $ iterate recurStep e
    UnsizedFW (RecursionTestF ri x) ->
      let test = \case
            z@(BasicEE ZeroSF) -> z
            p@(BasicEE (PairSF _ _)) -> p
            SuperEE AnyPF -> abortEE . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
            SuperEE (EitherPF a b) -> superEE $ EitherPF (test a) (test b)
            a@(AbortEE (AbortedF _)) -> a
            UnsizedEE sr@(SizingResultsF _ _) -> unsizedEE $ fmap test sr
            z -> error ("evalRecursionTest checkTest unexpected\n" <> prettyPrint z)
      in test x
    -- stuck values
    x@(UnsizedFW (SizingResultsF _ _)) -> embed x
    x -> handleOther x

newtype SizedRecursion = SizedRecursion { unSizedRecursion :: Map UnsizedRecursionToken (Maybe Int)}

instance Semigroup SizedRecursion where
  (<>) (SizedRecursion a) (SizedRecursion b) = SizedRecursion $ Map.unionWith f a b where
    f a b = case (a,b) of
      (Just a', Just b') -> pure $ max a' b'
      _ -> Nothing

instance Monoid SizedRecursion where
  mempty = SizedRecursion Map.empty

instance PrettyPrintable1 ((,) SizedRecursion) where
  showP1 (_,x) = showP x

unsizedStepM :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => (a -> a -> a)
  -> (f (SizedRecursion, a) -> (SizedRecursion, a)) -> (f (SizedRecursion, a) -> (SizedRecursion, a)) -> f (SizedRecursion, a) -> (SizedRecursion, a)
unsizedStepM unsizedMerge fullStep handleOther x = sequence x >>= f where
  f = \case
    FillFunction (UnsizedEE (RecursionTestF ri d)) e -> second test . fullStep . fmap pure $ fillFunction d e where
      test = \case
        z@(BasicEE ZeroSF) -> z
        p@(BasicEE (PairSF _ _)) -> p
        SuperEE AnyPF -> abortEE . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
        SuperEE (EitherPF a b) -> superEE $ EitherPF (test a) (test b)
        a@(AbortEE (AbortedF _)) -> a
        UnsizedEE sr@(SizingResultsF _ _) -> unsizedEE $ fmap test sr
        z -> error ("evalRecursionTest checkTest unexpected\n" <> prettyPrint z)
    UnsizedFW (UnsizedStubF t e) -> capResult . head . filter sized $ iterate g (0, Just AbortedSR, pure e) where
      g (n, a, e) = let e'@(_, er) = fullStep . embedB $ SetEnvSF e in (n + 1, cata findR er, td e')
      td x = trace ("sizing step result is now:\n" <> prettyPrint x) x
      findR = \case
        AbortFW (AbortedF AbortRecursion) -> Just AbortedSR
        AbortFW (AbortedF (AbortUnsizeable t)) -> Just . UnsizableSR . toEnum $ g2i t
        x -> Data.Foldable.fold x
      sized = \case
        (_, Just (UnsizableSR _), _) -> True
        (_, Nothing, _) -> True
        (255, _, _) -> True -- TODO change 255
        _ -> False
      capResult (n, a, (srs, _)) = (srs <> sr, superEE AnyPF) where
        sr = case a of
          Nothing -> trace ("found limit at " <> show n) SizedRecursion $ Map.singleton t (Just (n - 1))
          _ -> SizedRecursion $ Map.singleton t Nothing
    -- stuck value
    t@(UnsizedFW (RecursionTestF _ _)) -> pure $ embed t
    _ -> handleOther x

data VoidF f
  deriving (Functor, Foldable, Traversable)

instance Eq1 VoidF where
  liftEq test a b = undefined

instance Show1 VoidF where
  liftShowsPrec showsPrec showList prec x = undefined

data SuperPositionF f
  = EitherPF f f
  | AnyPF
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 SuperPositionF where
  liftEq test a b = case (a,b) of
    (AnyPF, AnyPF)               -> True
    (EitherPF a b, EitherPF c d) -> test a c && test b d
    _                            -> False

instance Show1 SuperPositionF where
  liftShowsPrec showsPrec showList prec = \case
    EitherPF a b -> shows "EitherPF (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
    AnyPF -> shows "AnyPF"

-- TODO we can simplify abort semantics to (defer env), and then could do gate x (abort [message] x) for conditional abort
data AbortableF f
  = AbortF
  | AbortedF IExpr
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 AbortableF  where
  liftEq test a b = case (a,b) of
    (AbortF, AbortF)                  -> True
    (AbortedF a, AbortedF b) | a == b -> True
    _                                 -> False

instance Show1 AbortableF where
  liftShowsPrec showsPrec showList prec = \case
    AbortF     -> shows "AbortF"
    AbortedF x -> shows "(AbortedF " . shows x . shows ")"

mergeBasic :: (Base x ~ f, BasicBase f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeBasic mergeOther a b =
  let reMerge = mergeBasic mergeOther
  in case (a,b) of
    (BasicEE (PairSF a b), BasicEE (PairSF c d)) | a == c -> basicEE $ PairSF a (reMerge b d)
    (BasicEE (PairSF a b), BasicEE (PairSF c d)) | b == d -> basicEE $ PairSF (reMerge a c) b
    (BasicEE (GateSF a b), BasicEE (GateSF c d)) | a == c -> basicEE $ GateSF a (reMerge b d)
    (BasicEE (GateSF a b), BasicEE (GateSF c d)) | b == d -> basicEE $ GateSF (reMerge a c) b
    (BasicEE (LeftSF x), BasicEE (LeftSF y)) -> basicEE . LeftSF $ reMerge x y
    (BasicEE (RightSF x), BasicEE (RightSF y)) -> basicEE . RightSF $ reMerge x y
    _ -> mergeOther a b

mergeStuck :: (Base x ~ f, StuckData f ~ x, StuckBase f, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeStuck mergeOther a b =
  case (a,b) of
    -- should we try merging within functions? Probably not
    (s@(StuckEE fida _), StuckEE fidb _) | fida == fidb -> s
    _ -> mergeOther a b

mergeSuper :: (Base x ~ f, SuperBase f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> (x -> x -> x) -> x -> x -> x
mergeSuper reMerge mergeOther a b = case (a,b) of
  (s@(SuperEE AnyPF), _) -> s
  (_, s@(SuperEE AnyPF)) -> s
  (SuperEE (EitherPF a b), c) -> superEE $ EitherPF (reMerge a c) (reMerge b c)
  (a, SuperEE (EitherPF b c)) -> superEE $ EitherPF (reMerge a b) (reMerge a c)
  _ -> mergeOther a b

mergeAbort :: (Base x ~ f, AbortBase f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeAbort mergeOther a b =
  case (a,b) of
    (a@(AbortEE (AbortedF x)), AbortEE (AbortedF y)) | x == y -> a
    (a@(AbortEE AbortF), AbortEE AbortF) -> a
    _ -> mergeOther a b

mergeUnsized :: (Base x ~ f, UnsizedBase f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> (x -> x -> x) -> x -> x -> x
mergeUnsized mergeDown mergeOther a b = case (a,b) of
  (UnsizedEE aa, UnsizedEE bb) -> case (aa,bb) of
    (RecursionTestF ta x, RecursionTestF tb y) | ta == tb -> unsizedEE . RecursionTestF ta $ mergeDown x y
    (SizingResultsF ta x, SizingResultsF tb y) | ta == tb -> unsizedEE . SizingResultsF ta $ zipWith mergeDown x y
  _ -> mergeOther a b

mergeUnknown :: (Base x ~ f, SuperBase f, Eq x, Corecursive x, Recursive x) => x -> x -> x
mergeUnknown a b = if a == b
  then a
  else superEE $ EitherPF a b

data UnsizedRecursionF f
  = RecursionTestF UnsizedRecursionToken f
  | UnsizedStubF UnsizedRecursionToken f
  | SizingWrapperF UnsizedRecursionToken f
  | SizingResultsF (Set UnsizedRecursionToken) [f]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    (SizingResultsF ta (a:_), SizingResultsF tb (b:_)) -> ta == tb && test a b
    _                                          -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec showList prec x = case x of
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec 0 x . shows ")"
    SizingResultsF t x -> shows "SizingResultsF (" . shows t . shows " " . showList x . shows ")"

instance PrettyPrintable1 PartExprF where
  showP1 = \case
    ZeroSF     -> pure "Z"
    PairSF a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    EnvSF      -> pure "E"
    SetEnvSF x -> indentWithOneChild' "S" $ showP x
    GateSF l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    LeftSF x   -> indentWithOneChild' "L" $ showP x
    RightSF x  -> indentWithOneChild' "R" $ showP x

instance PrettyPrintable1 SuperPositionF where
  showP1 = \case
    AnyPF        -> pure "A"
    EitherPF a b -> indentWithTwoChildren' "%" (showP a) (showP b)

instance PrettyPrintable1 AbortableF where
  showP1 = \case
    AbortF      -> pure "!"
    AbortedF am -> pure $ "(aborted) " <> show am

instance PrettyPrintable1 UnsizedRecursionF where
  showP1 = \case
    RecursionTestF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("T(" <> show ind <> ")") $ showP x
    SizingWrapperF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("&(" <> show ind <> ")") $ showP x
    UnsizedStubF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("%" <> show ind) $ showP x
    SizingResultsF _ rl -> do
      i <- State.get
      start <- indentWithChildren' "[" . map showP $ take 2 rl
      pure $ start <> "]"

instance PrettyPrintable1 VoidF where
  showP1 _ = error "VoidF should never be inhabited, so should not be PrettyPrintable1"

{-
instance PrettyPrintable1 BitsExprF where
  showP1 = \case
    ZeroB -> pure "Z"
    PairB a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    FunctionB vi x -> indentWithOneChild' ("F" <> show (fromEnum vi)) (showP x)
    SetEnvB x -> indentWithOneChild' "S" $ showP x
    GateB l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    VarB vi -> pure $ "V" <> (show $ fromEnum vi)
    AbortB -> pure "A"
    UnsizedChurchNumeralB -> pure "?"

instance PrettyPrintable BitsExpr where
  showP = showP . project

instance PrettyPrintable BitsExprWMap where
  showP (BitsExprWMap expr m) = pure x where
    x = prettyPrint expr <> vs
    showV = show . fromEnum
    vs = cata getF expr where
      getF = \case
        FunctionB v ix -> (("\n" <>) . flip State.evalState 0 . indentWithOneChild' (showV v <> " -") $ lf (embed $ VarB v)) <> ix where
          lf x = case project x of
            VarB vi -> case Map.lookup vi m of
              Nothing -> pure $ "V" <> showV vi
              Just (Fix (PairB a b)) -> indentWithTwoChildren' "P" (lf a) (lf b)
            x' -> showP x'
        x -> Data.Foldable.fold x
-}

data StuckExprF g f
  = StuckExprB (PartExprF f)
  | StuckExprS FunctionIndex g
  deriving (Functor, Foldable, Traversable)
instance BasicBase (StuckExprF g) where
  embedB = StuckExprB
  extractB = \case
    StuckExprB x -> Just x
    _ -> Nothing
instance StuckBase (StuckExprF g) where
  type StuckData (StuckExprF g) = g
  embedS = uncurry StuckExprS
  extractS = \case
    StuckExprS fid x -> Just (fid, x)
    _ -> Nothing
instance (PrettyPrintable g) => PrettyPrintable1 (StuckExprF g) where
  showP1 = \case
    StuckExprB x -> showP1 x
    StuckExprS fi x -> liftM2 (<>) (showP fi) (showP x)

newtype StuckExpr = StuckExpr {unStuckExpr :: StuckExprF StuckExpr StuckExpr}
type instance Base StuckExpr = StuckExprF StuckExpr
instance Recursive StuckExpr where
  project = unStuckExpr
instance Corecursive StuckExpr where
  embed = StuckExpr
instance PrettyPrintable StuckExpr where
  showP = showP1 . project

data UnsizedExprF g f
  = UnsizedExprB (PartExprF f)
  | UnsizedExprS FunctionIndex g
  | UnsizedExprP (SuperPositionF f)
  | UnsizedExprA (AbortableF f)
  | UnsizedExprU (UnsizedRecursionF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase (UnsizedExprF g) where
  embedB = UnsizedExprB
  extractB = \case
    UnsizedExprB x -> Just x
    _ -> Nothing
instance StuckBase (UnsizedExprF g) where
  type StuckData (UnsizedExprF g) = g
  embedS = uncurry UnsizedExprS
  extractS = \case
    UnsizedExprS fid x -> Just (fid, x)
    _ -> Nothing
instance SuperBase (UnsizedExprF g) where
  embedP = UnsizedExprP
  extractP = \case
    UnsizedExprP x -> Just x
    _ -> Nothing
instance AbortBase (UnsizedExprF g) where
  embedA = UnsizedExprA
  extractA = \case
    UnsizedExprA x -> Just x
    _ -> Nothing
instance UnsizedBase (UnsizedExprF g) where
  embedU = UnsizedExprU
  extractU = \case
    UnsizedExprU x -> Just x
    _ -> Nothing
instance (Eq g) => Eq1 (UnsizedExprF g) where
  liftEq test a b = case (a,b) of
    (UnsizedExprB x, UnsizedExprB y) -> liftEq test x y
    (UnsizedExprS fa _, UnsizedExprS fb _) -> fa == fb
    (UnsizedExprP x, UnsizedExprP y) -> liftEq test x y
    (UnsizedExprA x, UnsizedExprA y) -> liftEq test x y
    (UnsizedExprU x, UnsizedExprU y) -> liftEq test x y
    _ -> False
instance (PrettyPrintable g) => PrettyPrintable1 (UnsizedExprF g) where
  showP1 = \case
    UnsizedExprB x -> showP1 x
    UnsizedExprS fid x -> liftM2 (<>) (showP fid) (showP x)
    UnsizedExprP x -> showP1 x
    UnsizedExprA x -> showP1 x
    UnsizedExprU x -> showP1 x

newtype UnsizedExpr = UnsizedExpr {unUnsizedExpr :: UnsizedExprF UnsizedExpr UnsizedExpr}
type instance Base UnsizedExpr = UnsizedExprF UnsizedExpr
instance Recursive UnsizedExpr where
  project = unUnsizedExpr
instance Corecursive UnsizedExpr where
  embed = UnsizedExpr
instance Eq UnsizedExpr where
  (==) a b = eq1 (project a) (project b)
instance PrettyPrintable UnsizedExpr where
  showP = showP1 . project

data SuperExprF g f
  = SuperExprB (PartExprF f)
  | SuperExprS FunctionIndex g
  | SuperExprA (AbortableF f)
  | SuperExprP (SuperPositionF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase (SuperExprF g) where
  embedB = SuperExprB
  extractB = \case
    SuperExprB x -> Just x
    _ -> Nothing
instance StuckBase (SuperExprF g) where
  type StuckData (SuperExprF g) = g
  embedS = uncurry SuperExprS
  extractS = \case
    SuperExprS fid x -> Just (fid, x)
    _ -> Nothing
instance AbortBase (SuperExprF g) where
  embedA = SuperExprA
  extractA = \case
    SuperExprA x -> Just x
    _ -> Nothing
instance SuperBase (SuperExprF g) where
  embedP = SuperExprP
  extractP = \case
    SuperExprP x -> Just x
    _ -> Nothing
instance (Eq g) => Eq1 (SuperExprF g) where
  liftEq test a b = case (a,b) of
    (SuperExprB x, SuperExprB y) -> liftEq test x y
    (SuperExprS fa _, SuperExprS fb _) -> fa == fb
    (SuperExprA x, SuperExprA y) -> liftEq test x y
    (SuperExprP x, SuperExprP y) -> liftEq test x y
    _ -> False
instance (PrettyPrintable g) => PrettyPrintable1 (SuperExprF g) where
  showP1 = \case
    SuperExprB x -> showP1 x
    SuperExprS fid x -> liftM2 (<>) (showP fid) (showP x)
    SuperExprA x -> showP1 x
    SuperExprP x -> showP1 x

newtype SuperExpr = SuperExpr {unSuperExpr :: SuperExprF SuperExpr SuperExpr}
type instance Base SuperExpr = SuperExprF SuperExpr
instance Recursive SuperExpr where
  project = unSuperExpr
instance Corecursive SuperExpr where
  embed = SuperExpr
instance Eq SuperExpr where
  (==) a b = eq1 (project a) (project b)
instance PrettyPrintable SuperExpr where
  showP = showP . project

data AbortExprF g f
  = AbortExprB (PartExprF f)
  | AbortExprS FunctionIndex g
  | AbortExprA (AbortableF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase (AbortExprF g) where
  embedB = AbortExprB
  extractB = \case
    AbortExprB x -> Just x
    _ -> Nothing
instance StuckBase (AbortExprF g) where
  type StuckData (AbortExprF g) = g
  embedS = uncurry AbortExprS
  extractS = \case
    AbortExprS fid x -> Just (fid, x)
    _ -> Nothing
instance AbortBase (AbortExprF g) where
  embedA = AbortExprA
  extractA = \case
    AbortExprA x -> Just x
    _ -> Nothing
instance (Eq g) => Eq1 (AbortExprF g) where
  liftEq test a b = case (a,b) of
    (AbortExprB x, AbortExprB y) -> liftEq test x y
    (AbortExprS fa _, AbortExprS fb _) -> fa == fb
    (AbortExprA x, AbortExprA y) -> liftEq test x y
    _ -> False
instance (PrettyPrintable g) => PrettyPrintable1 (AbortExprF g) where
  showP1 = \case
    AbortExprB x -> showP1 x
    AbortExprS fid x -> liftM2 (<>) (showP fid) (showP x)
    AbortExprA x -> showP1 x

newtype AbortExpr = AbortExpr {unAbortExpr :: AbortExprF AbortExpr AbortExpr}
type instance Base AbortExpr = AbortExprF AbortExpr
instance Recursive AbortExpr where
  project = unAbortExpr
instance Corecursive AbortExpr where
  embed = AbortExpr
instance Eq AbortExpr where
  (==) a b = eq1 (project a) (project b)
instance PrettyPrintable AbortExpr where
  showP = showP . project

unsized2abortExpr :: UnsizedExpr -> AbortExpr
unsized2abortExpr = f where
  f = embed . f' . fmap f . project -- use hoist?
  f' = \case
    UnsizedExprB x -> AbortExprB x
    UnsizedExprS fid x -> AbortExprS fid $ f x
    -- UnsizedExprP x -> AbortExprP x
    UnsizedExprA x -> AbortExprA x
    x -> error $ "unsized2abortExpr unexpected unsized bit: " <> prettyPrint x

term3ToUnsizedExpr :: Int -> Term3 -> UnsizedExpr
term3ToUnsizedExpr maxSize (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag -> embedB ZeroSF
        PairFrag a b -> embedB $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag -> embedB EnvSF
        SetEnvFrag x -> embedB . SetEnvSF $ convertFrag' x
        DeferFrag ind -> (\x -> embedS (toEnum $ fromEnum ind, x)) . convertFrag' . unFragExprUR $ fragLookup ind
        AbortFrag -> embedA AbortF
        GateFrag l r -> embedB $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x -> embedB . LeftSF $ convertFrag' x
        RightFrag x -> embedB . RightSF $ convertFrag' x
        TraceFrag -> embedB EnvSF
        AuxFrag (SizingWrapper tok (FragExprUR x)) -> embedU . SizingWrapperF tok $ convertFrag' x
        AuxFrag (NestedSetEnvs t) -> embedU . UnsizedStubF t . embed $ embedB EnvSF
  in convertFrag' . unFragExprUR $ rootFrag termMap

newtype UnsizedAggregate = UnsizedAggregate { unUnAgg :: Map UnsizedRecursionToken Bool }

instance Semigroup UnsizedAggregate where
  (<>) (UnsizedAggregate a) (UnsizedAggregate b) = UnsizedAggregate $ Map.unionWith (||) a b

instance Monoid UnsizedAggregate where
  mempty = UnsizedAggregate $ Map.empty

aggWrapper x = UnsizedAggregate $ Map.singleton x True

readyForSizing :: UnsizedAggregate -> Bool
readyForSizing (UnsizedAggregate m) = not (null m) && and m

data SizedResult = AbortedSR | UnsizableSR UnsizedRecursionToken

instance Semigroup SizedResult where
  (<>) a b = case (a,b) of
    (u@(UnsizableSR _), _) -> u
    (_, u@(UnsizableSR _)) -> u
    _ -> a

newtype MonoidList a = MonoidList { unMonoidList :: [a] }

instance Semigroup a => Semigroup (MonoidList a) where
  (<>) (MonoidList a) (MonoidList b) = MonoidList $ zipWith (<>) a b

instance Semigroup a => Monoid (MonoidList a) where
  mempty = MonoidList []

capMain :: (Base g ~ f, StuckData f ~ g, BasicBase f, StuckBase f, SuperBase f, Recursive g, Corecursive g) => g -> g
capMain = \case  -- make sure main functions are fully applied with Any data
  BasicEE (PairSF d@(StuckEE _ _) _) -> basicEE . SetEnvSF . basicEE . PairSF d $ superEE AnyPF
  x -> x

sizeTerm :: Int -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
sizeTerm maxSize = findSizes 0 where
  addSizingTest :: UnsizedExpr -> UnsizedExpr
  addSizingTest = transformStuck f where
    f = \case
      UnsizedFW (SizingWrapperF tok (BasicEE (PairSF d (BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF t (BasicEE ZeroSF))))))))))
        -> case t of
             BasicEE (PairSF s@(StuckEE _ _) te) ->
               let nt = basicEE $ PairSF (unsizedEE $ RecursionTestF tok s) te
               in basicEE . PairSF d . basicEE . PairSF b . basicEE . PairSF r . basicEE . PairSF nt $ basicEE ZeroSF
      x -> embed x
  findSizes :: Int -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
  findSizes n g = let sizeMap = Map.mapMaybe id $ unSizedRecursion sr
                      sr = fst . cata evalStep . capMain $ addSizingTest g
                      td x = trace (prettyPrint x) x
                      ng = setSizes sizeMap g
                  in case getAnUnsized ng of
                       Just uid -> if null sizeMap
                                   then Left uid
                                   else if n > maxSize
                                        then Left uid
                                        else findSizes (succ n) ng
                       _ -> pure $ clean ng
  clean = unsized2abortExpr
  setSizes :: Map UnsizedRecursionToken Int -> UnsizedExpr -> UnsizedExpr
  setSizes m = transformStuck $ \case
    UnsizedFW (UnsizedStubF tok _) | Map.member tok m -> case Map.lookup tok m of
                                       Just n -> iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
    -- UnsizedFW (RecursionTestF tok x) | Map.member tok m -> x
    UnsizedFW (SizingWrapperF _ x) -> x
    x -> embed x
  getAnUnsized :: UnsizedExpr -> Maybe UnsizedRecursionToken
  getAnUnsized = f where
    f = cata f'
    f' = \case
      UnsizedFW (SizingWrapperF uid _) -> Just uid
      StuckFW _ x -> f x
      x -> foldr (<|>) Nothing x
  unsizedMerge = mergeBasic (mergeStuck (mergeAbort (mergeSuper unsizedMerge (mergeUnsized unsizedMerge mergeUnknown))))
  evalStep :: UnsizedExprF UnsizedExpr (SizedRecursion, UnsizedExpr) -> (SizedRecursion, UnsizedExpr)
  evalStep = basicStepM (stuckStepM (abortStepM (superStepM unsizedMerge evalStep (unsizedStepM unsizedMerge evalStep (anyFunctionStepM unhandledError)))))
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)

convertToF :: (Base g ~ f, StuckData f ~ g, BasicBase f, StuckBase f, Traversable f, Corecursive g) => IExpr -> g
convertToF = flip State.evalState (toEnum 0) . anaM' f where
  f :: (Base g ~ f, StuckData f ~ g, BasicBase f, StuckBase f, Traversable f, Corecursive g) =>  IExpr -> State FunctionIndex (f IExpr)
  f = \case
    Zero -> pure $ embedB ZeroSF
    Pair a b -> pure . embedB $ PairSF a b
    Env -> pure $ embedB EnvSF
    SetEnv x -> pure . embedB $ SetEnvSF x
    Defer x -> curry embedS <$> nextVar <*> anaM' f x
    Gate l r -> pure . embedB $ GateSF l r
    PLeft x -> pure . embedB $ LeftSF x
    PRight x -> pure . embedB $ RightSF x
    Trace    -> error "EnhancedExpr trace"
  nextVar :: State FunctionIndex FunctionIndex
  nextVar = do
    i <- State.get
    State.put $ succ i
    pure i

convertFromF :: (Base g ~ f, StuckData f ~ g, TelomareLike g, BasicBase f, StuckBase f, Traversable f, Recursive g) => g -> Maybe IExpr
convertFromF = \case
  BasicEE x -> case x of
    ZeroSF     -> pure Zero
    PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
    EnvSF      -> pure Env
    SetEnvSF p -> SetEnv <$> toTelomare p
    GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
    LeftSF x   -> PLeft <$> toTelomare x
    RightSF x  -> PRight <$> toTelomare x
  StuckEE _ x -> Defer <$> toTelomare x
  _ -> Nothing

instance TelomareLike StuckExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

instance TelomareLike UnsizedExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

evalBU :: IExpr -> Maybe IExpr
evalBU = toIExpr . ebu . fromTelomare where
  toIExpr = toTelomare
  ebu :: StuckExpr -> StuckExpr
  ebu = evalBottomUp (stuckStep undefined) . (\x -> debugTrace ("evalBU starting expr:\n" <> prettyPrint x) x)

evalBU' :: IExpr -> IO IExpr
evalBU' = f . evalBU where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x

-- term4toAbortExpr :: Term4 -> AbortExpr
term4toAbortExpr :: (Base g ~ f, StuckData f ~ g, BasicBase f, StuckBase f, AbortBase f, Corecursive g) => Term4 -> g
term4toAbortExpr (Term4 termMap) =
  let convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag      -> embedB ZeroSF
        PairFrag a b  -> embedB $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag       -> embedB EnvSF
        SetEnvFrag x  -> embedB . SetEnvSF $ convertFrag' x
        DeferFrag ind -> curry embedS (toEnum . fromEnum $ ind) . convertFrag' $ termMap Map.! ind
        AbortFrag     -> embedA AbortF
        GateFrag l r  -> embedB $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x    -> embedB . LeftSF $ convertFrag' x
        RightFrag x   -> embedB . RightSF $ convertFrag' x
        TraceFrag     -> embedB EnvSF
        z             -> error ("term4toAbortExpr'' unexpected " <> show z)
  in convertFrag' (rootFrag termMap)

abortExprToTerm4 :: (Base g ~ f, StuckData f ~ g, BasicBase f, StuckBase f, AbortBase f, Foldable f, Recursive g) => g -> Either IExpr Term4
abortExprToTerm4 x =
  let
    findAborted = cata $ \case
      AbortFW (AbortedF e) -> Just e
      x                    -> foldr (<|>) empty x
    convert :: (Base g ~ f, StuckData f ~ g, BasicBase f, StuckBase f, AbortBase f, Recursive g) => f (BreakState' Void Void) -> BreakState' Void Void
    convert = \case
      BasicFW ZeroSF       -> pure ZeroFrag
      BasicFW (PairSF a b) -> PairFrag <$> a <*> b
      BasicFW EnvSF        -> pure EnvFrag
      BasicFW (SetEnvSF x) -> SetEnvFrag <$> x
      StuckFW _ x    -> deferF $ cata convert x
      AbortFW AbortF      -> pure AbortFrag
      BasicFW (GateSF l r) -> GateFrag <$> l <*> r
      BasicFW (LeftSF x)   -> LeftFrag <$> x
      BasicFW (RightSF x)  -> RightFrag <$> x
      z                   -> error ("abortExprToTerm4 unexpected thing " )
  in case findAborted x of
    Just e -> Left e
    _      -> pure . Term4 . buildFragMap . cata convert $ x

evalA :: (Maybe IExpr -> Maybe IExpr -> Maybe IExpr) -> Maybe IExpr -> Term4 -> Maybe IExpr
evalA combine base t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: SuperExprF SuperExpr SuperExpr -> SuperExpr
                      aStep = stuckStep (superStep aMerge aStep (abortStep unhandledError))
                      aMerge = mergeSuper aMerge (mergeAbort mergeUnknown)
                      eval' :: SuperExpr -> SuperExpr
                      eval' = evalBottomUp aStep
                  in eval' . capMain $ term4toAbortExpr t
      getAborted = \case
        AbortFW (AbortedF e) -> Just e
        SuperFW (EitherPF a b) -> combine a b
        x                    -> foldr (<|>) Nothing x
  in flip combine base . cata getAborted $ runResult
