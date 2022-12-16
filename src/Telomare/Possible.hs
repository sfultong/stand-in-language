{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE LambdaCase                 #-}
-- {-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE PatternSynonyms            #-}
-- {-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
module Telomare.Possible where

import           Control.Applicative
-- import           Control.Lens.Plated
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader      (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader      as Reader
import           Control.Monad.State       (State, StateT)
import qualified Control.Monad.State       as State
import           Control.Monad.Trans.Class
import           Data.DList                (DList)
import qualified Data.DList                as DList
import           Data.Fix                  (Fix(..))
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.Kind
import           Data.List                 (sortBy)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Monoid
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Void
import           Debug.Trace
import           PrettyPrint
import           Telomare                  (FragExpr (..), FragExprUR (..), i2g, g2i,
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
                                            sindent, pattern AbortUnsizeable, IExprF (SetEnvF))
import           Telomare.TypeChecker

data PartExprF f
  = ZeroSF
  | PairSF f f
  | EnvSF
  | SetEnvSF f
  --  | DeferSF f
  | GateSF f f
  | LeftSF f
  | RightSF f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

{-
instance Functor PartExprF where
  fmap f = \case
    ZeroSF -> ZeroSF
    PairSF a b -> PairSF (f a) (f b)
    EnvSF -> EnvSF
    SetEnvSF x -> SetEnvSF $ f x
    DeferSF x -> DeferSF x -- Don't apply f for Defer, because Defer is "stuck"
    GateSF l r -> GateSF (f l) (f r)
    LeftSF x -> LeftSF $ f x
    RightSF x -> RightSF $ f x

instance Foldable PartExprF where
  foldr f d = \casr
    ZeroSF -> d
    PairSF a b -> f a $ f b d
    EnvSF -> d
    SetEnvSF x -> f x d
    DeferSF x -> d -- Don't fold over Defer, because Defer is stuck
    GateSF l r -> f l $ f r d
    LeftSF x -> f x d
    RightSF x -> f x d

-- traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
instance Traversable PartExprF where
  traverse f = \case
    ZeroSF -> pure ZeroSF
    PairSF a b -> PairSF <$> f a <*> f b
    EnvSF -> pure EnvSF
    SetEnvSF x -> SetEnvSF <$> f x
    DeferSF x -> pure $ DeferSF x -- don't traverse Defer, because it's stuck
    GateSF l r -> GateSF <$> f l <*> f r
    LeftSF x -> LeftSF <$> f x
    RightSF x -> RightSF <$> f x
-}

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


{-
newtype EnhancedExpr f = EnhancedExpr {unEnhanceExpr :: SplitFunctor f PartExprF (EnhancedExpr f)} -- deriving (Eq, Show)
  deriving newtype (PrettyPrintable)

type instance Base (EnhancedExpr f) = SplitFunctor f PartExprF

instance Functor f => Recursive (EnhancedExpr f) where
  project = unEnhanceExpr

instance Functor f => Corecursive (EnhancedExpr f) where
  embed = EnhancedExpr

instance Eq1 f => Eq (EnhancedExpr f) where
  (EnhancedExpr (SplitFunctor a)) == (EnhancedExpr (SplitFunctor b)) = case (a,b) of
    (Left la, Left lb)   -> eq1 la lb
    (Right ra, Right rb) -> eq1 ra rb
    _                    -> False

instance Show1 f => Show (EnhancedExpr f) where
  show (EnhancedExpr (SplitFunctor x)) = case x of
    Left l  -> "EnhancedExprL (" <> showsPrec1 0 l ")"
    Right r -> "EnhancedExprR (" <> showsPrec1 0 r ")"
-}

type BasicBase f = SplitFunctor f PartExprF
type StuckBase g f = BasicBase (SplitFunctor f (StuckF g))
-- type UnStuckBase f = BasicBase (SplitFunctor f UnStuckF)
type SuperBase g f = StuckBase g (SplitFunctor f SuperPositionF)
type AbortBase g f = SuperBase g (SplitFunctor f AbortableF)
type UnsizedBase g f = AbortBase g (SplitFunctor f UnsizedRecursionF)

type StuckBase' f x = StuckBase x f x
type SuperBase' f x = SuperBase x f x
type AbortBase' f x = AbortBase x f x
type UnsizedBase' f x = UnsizedBase x f x
{-
type StuckBase r g f = BasicBase (SplitFunctor f (StuckF r g))
type SuperBase r g f = StuckBase r g (SplitFunctor f SuperPositionF)
type AbortBase r g f = SuperBase r g (SplitFunctor f AbortableF)
type UnsizedBase r g f = AbortBase r g (SplitFunctor f UnsizedRecursionF)
-}

type EnhancedExpr f = Fix (BasicBase f)

pattern ZeroFW :: f x -> SplitFunctor g f x
pattern ZeroFW x = SplitFunctor (Right x)
pattern OneFW :: f x -> SplitFunctor (SplitFunctor g f) h x
pattern OneFW x = SplitFunctor (Left (ZeroFW x))
pattern TwoFW :: f x -> SplitFunctor (SplitFunctor (SplitFunctor g f) h) i x
pattern TwoFW x = SplitFunctor (Left (OneFW x))
pattern ThreeFW :: f x -> SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor g f) h) i) j x
pattern ThreeFW x = SplitFunctor (Left (TwoFW x))
pattern FourFW :: f x -> SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor g f) h) i) j) k x
pattern FourFW x = SplitFunctor (Left (ThreeFW x))
{-
pattern ZeroEE :: PartExprF (EnhancedExpr f) -> EnhancedExpr f
pattern ZeroEE g = Fix (ZeroFW g)
pattern OneEE :: g (EnhancedExpr (SplitFunctor f g)) -> EnhancedExpr (SplitFunctor f g)
pattern OneEE g = Fix (OneFW g)
pattern TwoEE :: g (EnhancedExpr (SplitFunctor (SplitFunctor f g) h)) -> EnhancedExpr (SplitFunctor (SplitFunctor f g) h)
pattern TwoEE g = Fix (TwoFW g)
pattern ThreeEE :: g (EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i))
  -> EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i)
pattern ThreeEE g = Fix (ThreeFW g)
pattern FourEE :: g (EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i) j))
  -> EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i) j)
pattern FourEE g = Fix (FourFW g)
-}
pattern ZeroEE :: (Base x ~ SplitFunctor g f, Recursive x) => f x -> x
pattern ZeroEE g <- (project -> ZeroFW g)
pattern OneEE :: (Base x ~ SplitFunctor (SplitFunctor g f) h, Recursive x) => f x -> x
pattern OneEE g <- (project -> OneFW g)
pattern TwoEE :: (Base x ~ SplitFunctor (SplitFunctor (SplitFunctor g f) h) i, Recursive x) => f x -> x
pattern TwoEE g <- (project -> TwoFW g)
pattern ThreeEE :: (Base x ~ SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor g f) h) i) j, Recursive x) => f x -> x
pattern ThreeEE g <- (project -> ThreeFW g)
pattern FourEE :: (Base x ~ SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor g f) h) i) j) k, Recursive x) => f x -> x
pattern FourEE g <- (project -> FourFW g)

{-
bareEnv :: (Functor f, Foldable f) => EnhancedExpr f -> Bool
bareEnv = cata bareF where
  bareF = \case
    ZeroFW EnvSF       -> True
    ZeroFW (DeferSF _) -> False
    x                  -> getAny $ foldMap Any x
-}

data StuckF g f
  = StuckF g
  deriving (Functor, Foldable, Traversable)

-- type StuckF' f = StuckF f f -- I wish this worked!
{-
newtype StuckF' f = StuckF'' (StuckF f f)
  deriving Functor via (StuckF f)
pattern StuckF' :: x -> StuckF' x
pattern StuckF' x = StuckF'' (StuckF x)
-}

instance (Show g) => Show1 (StuckF g) where
  liftShowsPrec showsPrec showList prec (StuckF x) = shows "StuckF (" . shows x . shows " )"

instance (Eq g) => Eq1 (StuckF g) where
  liftEq test (StuckF ga) (StuckF gb) = ga == gb

{-
data UnStuckF f = UnStuckF f
  deriving (Functor, Foldable, Traversable)

type UnStuckExpr f = Fix (UnStuckBase f)
-}

--stick :: UnStuckExpr f -> StuckExpr f
{-
stick = cata $ \case
  OneFW (UnStuckF x) -> OneEE (StuckF' x)
  x -> embed x
-}
  {-
stick = hoist $ \case
  OneFW (UnStuckF x) -> OneFW (StuckF' x)
  
-}


-- pattern FillFunction :: Functor f => EnhancedExpr f -> EnhancedExpr f -> PartExprF (EnhancedExpr f)
pattern FillFunction :: (Base x ~ BasicBase f, Recursive x) => x -> x -> PartExprF x
pattern FillFunction c e <- SetEnvSF (ZeroEE (PairSF c e))
-- pattern GateSwitch :: Functor f => EnhancedExpr f -> EnhancedExpr f -> EnhancedExpr f -> PartExprF (EnhancedExpr f)
pattern GateSwitch :: (Base x ~ BasicBase f, Recursive x) => x -> x -> x -> PartExprF x
pattern GateSwitch l r s <- FillFunction (ZeroEE (GateSF l r)) s


fillFunction :: (Base f ~ BasicBase g, Corecursive f) => f -> f -> PartExprF f
fillFunction c e = SetEnvSF (embed $ ZeroFW (PairSF c e))

gateSwitch :: (Base f ~ BasicBase g, Corecursive f) => f -> f -> f -> PartExprF f
gateSwitch  l r s = fillFunction (embed $ ZeroFW (GateSF l r)) s

{-
basicStep :: (BasicBase f (EnhancedExpr f) -> EnhancedExpr f)
  -> BasicBase f (EnhancedExpr f) -> EnhancedExpr f
-}
basicStep :: (Base b ~ BasicBase f, Corecursive b, Recursive b) => (Base b b -> b) -> Base b b -> b
basicStep handleOther = \case
  ZeroFW (LeftSF (ZeroEE ZeroSF)) -> embed $ ZeroFW ZeroSF
  ZeroFW (LeftSF (ZeroEE (PairSF l _))) -> l
  ZeroFW (RightSF (ZeroEE ZeroSF)) -> embed $ ZeroFW ZeroSF
  ZeroFW (RightSF (ZeroEE (PairSF _ r))) -> r
  ZeroFW (GateSwitch l _ (ZeroEE ZeroSF)) -> l
  ZeroFW (GateSwitch _ r (ZeroEE (PairSF _ _))) -> r
  {-
  ZeroFW (FillFunction (ZeroEE (DeferSF d)) e) -> cata (evalF . replaceEnv) d where
    replaceEnv = \case
      ZeroFW EnvSF -> e
      x -> x
-}
  -- stuck values
  x@(ZeroFW ZeroSF) -> embed x
  x@(ZeroFW (PairSF _ _)) -> embed x
  x@(ZeroFW (GateSF _ _)) -> embed x
  x -> handleOther x

{-
type DualFix :: (Type -> (Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type
newtype DualFix b f = DualFix {unDualFix :: b (DualFix b f) f (DualFix b f)}
type instance Base (DualFix b f) = b (DualFix b f) f
-- instance (Functor f) => Recursive (DualFix b f) where
instance Recursive (DualFix b f) where
  project = unDualFix
-- instance (Functor f) => Corecursive (DualFix b f) where
instance Corecursive (DualFix b f) where
  embed = DualFix
-}

newtype StuckExpr f = StuckExpr {unStuckExpr :: StuckBase (StuckExpr f) f (StuckExpr f)}
--   deriving Show via (Show1 f => StuckBase (StuckExpr f) f (StuckExpr f))
-- type StuckExpr = DualFix StuckBase
-- type StuckExpr f = Fix (StuckBase' f)
type instance Base (StuckExpr f) = StuckBase (StuckExpr f) f
instance Functor f => Recursive (StuckExpr f) where
  project = unStuckExpr
instance Functor f => Corecursive (StuckExpr f) where
  embed = StuckExpr
instance Show1 f => Show (StuckExpr f) where
  show = ($ "") . showsPrec1 0 . unStuckExpr
instance Eq1 f => Eq (StuckExpr f) where
  (==) (StuckExpr a) (StuckExpr b) = eq1 a b

{-
transformStuck :: (Functor f, Functor g) => (StuckBase (StuckExpr f) f (StuckExpr g) -> StuckExpr g)
  -> StuckExpr f -> StuckExpr g
-}
transformStuck f = cata f' where
  f' = \case
    OneFW (StuckF x) -> embed . OneFW . StuckF $ cata f' x
    -- OneFW (StuckF x) -> f' . OneFW . StuckF $ cata f' x
    x -> f x

{-
transformStuckM :: (Functor f, Functor g, Monad m) => (StuckBase (StuckExpr f) f (m (StuckExpr g)) -> m (StuckExpr g))
  -> StuckExpr f -> m (StuckExpr g)
-}
transformStuckM f = cata f' where
  f' = \case
    OneFW (StuckF x) -> embed . OneFW . StuckF <$> cata f' x
    x -> f x

-- stuckStep :: (StuckBase (StuckExpr f) f (StuckExpr f) -> StuckExpr f) -> StuckBase (StuckExpr f) f (StuckExpr f) -> StuckExpr f
stuckStep handleOther = \case
  ZeroFW (FillFunction (OneEE (StuckF d)) e) -> cata (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    replaceEnv = \case
      ZeroFW EnvSF -> e'
      x -> x
  -- stuck value
  x@(OneFW (StuckF _)) -> embed x
  x -> handleOther x

{-
evalBottomUp :: (PrettyPrintable1 f, Functor f) =>
  (BasicBase f (EnhancedExpr f) -> EnhancedExpr f)
  -> EnhancedExpr f -> EnhancedExpr f
-}
evalBottomUp :: (Base t ~ BasicBase f, Corecursive t, Recursive t, Recursive t) => (Base t t -> t) -> t -> t
evalBottomUp handleOther = cata (basicStep handleOther)

-- type SuperExpr f = Fix (SuperBase' f)
-- type SuperExpr = DualFix SuperBase
newtype SuperExpr f = SuperExpr {unSuperExpr :: SuperBase (SuperExpr f) f (SuperExpr f)}
type instance Base (SuperExpr f) = SuperBase (SuperExpr f) f
instance Functor f => Recursive (SuperExpr f) where
  project = unSuperExpr
instance Functor f => Corecursive (SuperExpr f) where
  embed = SuperExpr
instance Show1 f => Show (SuperExpr f) where
  show = ($ "") . showsPrec1 0 . unSuperExpr
instance Eq1 f => Eq (SuperExpr f) where
  (==) (SuperExpr a) (SuperExpr b) = eq1 a b

{-
superStep :: Functor f => (SuperExpr f -> SuperExpr f -> SuperExpr f)
  -> (SuperBase (SuperExpr f) f (SuperExpr f) -> SuperExpr f)
  -> SuperBase (SuperExpr f) f (SuperExpr f) -> SuperExpr f
-}
superStep mergeSuper handleOther =
  let step = basicStep (stuckStep (superStep mergeSuper handleOther))
  in \case
    ZeroFW (LeftSF (TwoEE AnyPF)) -> embed $ TwoFW AnyPF
    ZeroFW (LeftSF (TwoEE (EitherPF a b))) -> mergeSuper (step . ZeroFW . LeftSF $ a) (step . ZeroFW . LeftSF $ b)
    ZeroFW (RightSF (TwoEE AnyPF)) -> embed $ TwoFW AnyPF
    ZeroFW (RightSF (TwoEE (EitherPF a b))) -> mergeSuper (step . ZeroFW . RightSF $ a) (step . ZeroFW . RightSF $ b)
    ZeroFW (SetEnvSF (TwoEE (EitherPF a b))) -> mergeSuper (step . ZeroFW . SetEnvSF $ a) (step . ZeroFW . SetEnvSF $ b)
    ZeroFW (GateSwitch l r (TwoEE AnyPF)) -> mergeSuper l r
    ZeroFW (FillFunction (TwoEE (EitherPF sca scb)) e) -> mergeSuper
      (step . ZeroFW . SetEnvSF . embed . ZeroFW $ PairSF sca e)
      (step . ZeroFW . SetEnvSF . embed . ZeroFW $ PairSF scb e)
    -- stuck values
    x@(TwoFW AnyPF) -> embed x
    x@(TwoFW (EitherPF _ _)) -> embed x
    x -> handleOther x

-- type AbortExpr f = Fix (AbortBase' f)
-- type AbortExpr = DualFix AbortBase
newtype AbortExpr f = AbortExpr {unAbortExpr :: AbortBase (AbortExpr f) f (AbortExpr f)}
type instance Base (AbortExpr f) = AbortBase (AbortExpr f) f
instance Functor f => Recursive (AbortExpr f) where
  project = unAbortExpr
instance Functor f => Corecursive (AbortExpr f) where
  embed = AbortExpr
instance Show1 f => Show (AbortExpr f) where
  show = ($ "") . showsPrec1 0 . unAbortExpr
instance Eq1 f => Eq (AbortExpr f) where
  (==) (AbortExpr a) (AbortExpr b) = eq1 a b
instance (Functor f, PrettyPrintable1 f) => PrettyPrintable (AbortExpr f) where
  showP = showP . project

{-
abortStep :: (AbortBase (AbortExpr f) f (AbortExpr f) -> AbortExpr f)
  -> AbortBase (AbortExpr f) f (AbortExpr f) -> AbortExpr f
-}
abortStep handleOther =
  \case
    ZeroFW (LeftSF a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (RightSF a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (SetEnvSF a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (FillFunction a@(ThreeEE (AbortedF _)) _) -> a
    ZeroFW (GateSwitch _ _ a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (FillFunction (ThreeEE AbortF) (ZeroEE ZeroSF)) -> embed . OneFW . StuckF . embed . ZeroFW $ EnvSF
    ZeroFW (FillFunction (ThreeEE AbortF) (TwoEE AnyPF)) -> embed . ThreeFW . AbortedF $ AbortAny
    ZeroFW (FillFunction (ThreeEE AbortF) e@(ZeroEE (PairSF _ _))) -> embed . ThreeFW $ AbortedF m where
      m = cata truncF e
      truncF = \case
        ZeroFW ZeroSF        -> Zero
        ZeroFW (PairSF a b)  -> Pair a b
        TwoFW (EitherPF a _) -> a
        TwoFW AnyPF -> Zero
        z                    -> error ("evalAbort truncF unexpected thing")
    -- stuck values
    x@(ThreeFW (AbortedF _)) -> embed x
    x@(ThreeFW AbortF) -> embed x
    x -> handleOther x

{-
anyFunctionStep :: (SuperBase (SuperExpr f) f (SuperExpr f) -> SuperExpr f)
  -> SuperBase (SuperExpr f) f (SuperExpr f) -> SuperExpr f
-}
anyFunctionStep handleOther =
  \case
    ZeroFW (FillFunction (TwoEE AnyPF) _) -> embed $ TwoFW AnyPF
    x -> handleOther x

-- type UnsizedExpr f = Fix (UnsizedBase' f)
-- type UnsizedExpr = DualFix UnsizedBase
newtype UnsizedExpr f = UnsizedExpr { unUnsizeExpr :: UnsizedBase (UnsizedExpr f) f (UnsizedExpr f)}
type instance Base (UnsizedExpr f) = UnsizedBase (UnsizedExpr f) f
instance Functor f => Recursive (UnsizedExpr f) where
  project = unUnsizeExpr
instance Functor f => Corecursive (UnsizedExpr f) where
  embed = UnsizedExpr
instance (Functor f, Show1 f) => Show (UnsizedExpr f) where
  show = ($ "") . showsPrec1 0 . project
instance (Functor f, Eq1 f) => Eq (UnsizedExpr f) where
  (==) a b = eq1 (project a) (project b)
instance (Functor f, PrettyPrintable1 f) => PrettyPrintable (UnsizedExpr f) where
  showP = showP . project

{-
type UnsizedUnstuckBase f = UnStuckBase (SplitFunctor (SplitFunctor (SplitFunctor f UnsizedRecursionF) AbortableF) SuperPositionF)
-- newtype UnsizedUnstuckExpr = UnsizedUnstuckExpr { unUnsizedUnstuckExpr :: UnsizedUnstuckBase UnsizedUnstuckExpr}
type UnsizedUnstuckExpr f = Fix (UnsizedUnstuckBase f)
-}

{-
unsizedStep :: (UnsizedBase (UnsizedExpr f) f (UnsizedExpr f) -> UnsizedExpr f)
  -> UnsizedBase (UnsizedExpr f) f (UnsizedExpr f) -> UnsizedExpr f
-}
unsizedStep handleOther =
  let recur = unsizedStep handleOther
      unsizedMerge = mergeSuper (mergeAbort (mergeUnsized mergeUnknown))
      fullStep = basicStep (stuckStep (superStep unsizedMerge (abortStep (unsizedStep handleOther))))
      -- recurStep = (\x -> trace ("recurStep:\n" <> prettyPrint x) x) . fullStep . ZeroFW . SetEnvSF
      recurStep = fullStep . ZeroFW . SetEnvSF
  in \case
    ZeroFW (LeftSF (FourEE sr@(SizingResultsF _ _))) -> trace "-ul" embed . FourFW $ fmap (fullStep . ZeroFW . LeftSF) sr
    ZeroFW (RightSF (FourEE sr@(SizingResultsF _ _))) -> trace "-ur" embed . FourFW $ fmap (fullStep . ZeroFW . RightSF) sr
    ZeroFW (SetEnvSF (FourEE sr@(SizingResultsF _ _))) -> trace "-us" embed . FourFW $ fmap (fullStep . ZeroFW . SetEnvSF) sr
    ZeroFW (FillFunction (FourEE sr@(SizingResultsF _ _)) e) -> trace "-uffc" embed . FourFW $ fmap (fullStep . ZeroFW . (\c -> fillFunction c e)) sr
    -- ZeroFW (FillFunction c (FourEE sr@(SizingResultsF _ _))) -> trace "-uffe" embed . FourFW $ fmap (fullStep . ZeroFW . fillFunction c) sr
    ZeroFW (FillFunction c (FourEE sr@(SizingResultsF _ _))) -> (\x -> trace ("-uffe before:\n" <> prettyPrint sr <> "\nuffe after:\n" <> prettyPrint x) x) . embed . FourFW $ fmap (fullStep . ZeroFW . fillFunction c) sr
    FourFW (RecursionTestF ri x) -> case x of
      z@(ZeroEE ZeroSF) -> z
      p@(ZeroEE (PairSF _ _)) -> p
      TwoEE AnyPF -> embed . ThreeFW . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
      TwoEE (EitherPF a b) -> embed . TwoFW $ EitherPF (recur $ FourFW (RecursionTestF ri a)) (recur $ FourFW (RecursionTestF ri b))
      a@(ThreeEE (AbortedF _)) -> a
      -- FourEE sr@(SizingResultsF _ _) -> 
      z -> error ("evalRecursionTest checkTest unexpected " <> show z)
    FourFW (NestedSetEnvsF t x) -> embed . FourFW . SizingResultsF t $ [x, (iterate recurStep x) !! 2] -- works-ish
    -- FourFW (NestedSetEnvsF t x) -> trace ("in nested setenvs:\n" <> prettyPrint x) embed . FourFW . SizingResultsF t . take 3 . iterate (fullStep . ZeroFW . SetEnvSF) $ x
    -- FourFW (NestedSetEnvsF t x) ->  (iterate (fullStep . ZeroFW . SetEnvSF) $ x) !! 5 -- works-ish
    -- FourFW (NestedSetEnvsF t x) -> x
    -- FourFW (NestedSetEnvsF t x) -> fullStep . ZeroFW . SetEnvSF $ x -- ok
    -- FourFW (NestedSetEnvsF t x) -> fullStep . ZeroFW . SetEnvSF . fullStep . ZeroFW . SetEnvSF $ x -- ok
    -- FourFW (NestedSetEnvsF t x) -> fullStep . ZeroFW . SetEnvSF . fullStep . ZeroFW . SetEnvSF . fullStep . ZeroFW . SetEnvSF . fullStep . ZeroFW . SetEnvSF $ x -- ok
    -- FourFW (NestedSetEnvsF t x) -> embed . FourFW . SizingResultsF t . map fullStep . iterate (ZeroFW . SetEnvSF . embed) $ project x
    -- stuck values
    x@(FourFW (SizingResultsF _ _)) -> embed x
    x -> handleOther x

{-
testPair :: (Base b ~ BasicBase f, Corecursive b) => b
testPair = embed . ZeroFW $ PairSF (embed $ ZeroFW ZeroSF) (embed $ ZeroFW ZeroSF)
-}

testReplace :: UnsizedExpr VoidF
testReplace =
  let testPair = embed . ZeroFW $ PairSF (embed $ ZeroFW ZeroSF) (embed $ ZeroFW ZeroSF)
      srs = embed $ FourFW (SizingResultsF (toEnum 0) [embed $ ZeroFW EnvSF, embed $ ZeroFW EnvSF])
      expr :: UnsizedExpr VoidF
      expr = embed $ ZeroFW (fillFunction (embed $ OneFW (StuckF srs)) testPair)
      unsizedMerge = mergeSuper (mergeAbort (mergeUnsized mergeUnknown))
      evalPossible = evalBottomUp (stuckStep (superStep unsizedMerge (abortStep (unsizedStep unhandledError))))
      unhandledError x = error ("unhandled case\n" <> prettyPrint x)
  in evalPossible expr


-- >>> show testReplace
-- "\"(SplitFunctorL \"\"(SplitFunctorL \"\"(SplitFunctorL \"\"(SplitFunctorL \"\"(SplitFunctorR \"\"SizingResultsF (\"UnsizedRecursionToken {unUnsizedRecursionToken = 0}\" \"[\"(SplitFunctorR \"\"PairSF (\"\"(SplitFunctorR \"\"ZeroSF\"\")\"\", \"\"(SplitFunctorR \"\"ZeroSF\"\")\"\")\"\")\"]\")\"\")\"\")\"\")\"\")\"\")\""

data VoidF f
  deriving (Functor, Foldable, Traversable)

instance Eq1 VoidF where
  liftEq test a b = undefined

instance Show1 VoidF where
  liftShowsPrec showsPrec showList prec x = undefined

data SuperPositionF f
  = EitherPF f f
  --   | AlsoZeroPF f f -- superposition of zero and pair
  | AnyPF
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 SuperPositionF where
  liftEq test a b = case (a,b) of
    (AnyPF, AnyPF)               -> True
    (EitherPF a b, EitherPF c d) -> test a c && test b d
    -- (AlsoZeroPF a b, AlsoZeroPF c d) -> test a c && test b d
    _                            -> False

instance Show1 SuperPositionF where
  liftShowsPrec showsPrec showList prec = \case
    EitherPF a b -> shows "EitherPF (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
    -- AlsoZeroPF a b -> shows "AlsoZeroPF (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
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

newtype SplitFunctor g f x = SplitFunctor { unSplitF :: Either (g x) (f x) } deriving (Eq, Show)

instance (Eq1 f, Eq1 g) => Eq1 (SplitFunctor g f) where
  liftEq test (SplitFunctor a) (SplitFunctor b) = case (a,b) of
    (Right fa, Right fb) -> liftEq test fa fb
    (Left ga, Left gb)   -> liftEq test ga gb
    _                    -> False

instance (Show1 f, Show1 g) => Show1 (SplitFunctor g f) where
  liftShowsPrec showsPrec showList prec (SplitFunctor x) = case x of
    Right x -> shows "(SplitFunctorR " . liftShowsPrec showsPrec showList 0 x . shows ")"
    Left x -> shows "(SplitFunctorL " . liftShowsPrec showsPrec showList 0 x . shows ")"

instance (Functor f, Functor g) => Functor (SplitFunctor g f) where
  fmap f (SplitFunctor e) = case e of
    Left lf  -> SplitFunctor . Left $ fmap f lf
    Right rf -> SplitFunctor . Right $ fmap f rf

instance (Foldable f, Foldable g) => Foldable (SplitFunctor g f) where
  foldMap f (SplitFunctor x) = case x of
    Left fg  -> foldMap f fg
    Right ff -> foldMap f ff

instance (Traversable f, Traversable g) => Traversable (SplitFunctor g f) where
  traverse f (SplitFunctor x) = case x of
    Left fg  -> SplitFunctor . Left <$> traverse f fg
    Right ff -> SplitFunctor . Right <$> traverse f ff

{-
mergeSuper :: (SuperExpr f -> SuperExpr f -> SuperExpr f)
  -> SuperExpr f -> SuperExpr f -> SuperExpr f
-}
{-
mergeSuper :: (Base x
 ~ SplitFunctor
     (SplitFunctor (SplitFunctor g SuperPositionF) (StuckF x))
     PartExprF,
 Eq x, Corecursive x, Recursive x) =>
  (x -> x -> x) -> x -> x -> x
-}
mergeSuper :: (Base x ~ SuperBase x f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeSuper mergeOther a b =
  let reMerge = mergeSuper mergeOther
      mergeZero pa pb = case (pa,pb) of
        (ZeroSF, ZeroSF)                  -> ZeroFW ZeroSF
        (EnvSF, EnvSF)                    -> ZeroFW EnvSF
        (PairSF a b, PairSF c d) | a == c -> ZeroFW $ PairSF a (reMerge b d)
        (PairSF a b, PairSF c d) | b == d -> ZeroFW $ PairSF (reMerge a c) b
        (SetEnvSF x, SetEnvSF y)          -> ZeroFW $ SetEnvSF (reMerge x y)
        (GateSF a b, GateSF c d) | a == c -> ZeroFW $ GateSF a (reMerge b d)
        (GateSF a b, GateSF c d) | b == d -> ZeroFW $ GateSF (reMerge a c) b
        (LeftSF x, LeftSF y)              -> ZeroFW $ LeftSF (reMerge x y)
        (RightSF x, RightSF y)            -> ZeroFW $ RightSF (reMerge x y)
        _                                 -> TwoFW $ EitherPF (embed $ ZeroFW pa) (embed $ ZeroFW pb)
  in case (a,b) of
    (ZeroEE ba, ZeroEE bb) -> embed $ mergeZero ba bb
    (OneEE (StuckF ba), OneEE (StuckF bb)) -> embed . OneFW . StuckF $ reMerge ba bb
    (TwoEE AnyPF, _) -> embed $ TwoFW AnyPF
    (_, TwoEE AnyPF) -> embed $ TwoFW AnyPF
    (TwoEE (EitherPF a b), TwoEE (EitherPF c d)) -> embed . TwoFW $ EitherPF (reMerge a c) (reMerge b d)
    _ -> mergeOther a b

{-
mergeAbort :: (AbortExpr f -> AbortExpr f -> AbortExpr f)
  -> AbortExpr f -> AbortExpr f -> AbortExpr f
-}
mergeAbort :: (Base x ~ AbortBase x f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeAbort mergeOther a b =
  case (a,b) of
    (ThreeEE (AbortedF x), ThreeEE (AbortedF y)) | x == y -> embed . ThreeFW $ AbortedF x
    (ThreeEE AbortF, ThreeEE AbortF) -> embed $ ThreeFW AbortF
    _ -> mergeOther a b

{-
mergeUnsized :: (Eq1 f) => (UnsizedExpr f -> UnsizedExpr f -> UnsizedExpr f)
  -> UnsizedExpr f -> UnsizedExpr f -> UnsizedExpr f
-}
mergeUnsized :: (Base x ~ UnsizedBase x f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeUnsized mergeOther a b =
  let mergeDown = mergeSuper (mergeAbort (mergeUnsized mergeOther))
  in case (a,b) of
    (FourEE aa, FourEE bb) -> case (aa,bb) of
      (RecursionTestF ta x, RecursionTestF tb y) | ta == tb -> embed . FourFW . RecursionTestF ta $ mergeDown x y
      (NestedSetEnvsF ta x, NestedSetEnvsF tb y) | ta == tb -> embed . FourFW . NestedSetEnvsF ta $ mergeDown x y
      -- (SizingResultsF ta (x:xs), SizingResultsF tb (y:_)) | ta == tb && x == y -> embed . FourFW $ SizingResultsF ta (x:xs) -- this is wrong
      (SizingResultsF ta x, SizingResultsF tb y) | ta == tb -> embed . FourFW . SizingResultsF ta $ zipWith mergeDown x y
    _ -> mergeOther a b

-- mergeUnknown :: (Eq1 f) => SuperExpr f -> SuperExpr f -> SuperExpr f
mergeUnknown :: (Base x ~ SuperBase x f, Eq x, Corecursive x, Recursive x) => x -> x -> x
mergeUnknown a b = if a == b
  then a
  else embed . TwoFW $ EitherPF a b

data UnsizedRecursionF f
  = RecursionTestF UnsizedRecursionToken f
  | NestedSetEnvsF UnsizedRecursionToken f
  | SizingResultsF UnsizedRecursionToken [f]
  --   | UnsizableF UnsizedRecursionToken -- TODO change to AbortedF ?
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    (NestedSetEnvsF ta a, NestedSetEnvsF tb b) -> ta == tb && test a b
    (SizingResultsF ta (a:_), SizingResultsF tb (b:_)) -> ta == tb && test a b
    _                                          -> False

instance Show1 UnsizedRecursionF where
  --  Show1 f => (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> f a -> ShowS
  liftShowsPrec showsPrec showList prec x = case x of
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec 0 x . shows ")"
    NestedSetEnvsF t x -> shows "NestedSetEnvsF (" . shows t . shows " " . showsPrec 0 x . shows ")"
    SizingResultsF t x -> shows "SizingResultsF (" . shows t . shows " " . showList x . shows ")"

instance (PrettyPrintable1 f, PrettyPrintable1 g) => PrettyPrintable1 (SplitFunctor f g) where
  showP1 (SplitFunctor f) = case f of
    Left fx  -> showP1 fx
    Right gx -> showP1 gx

instance PrettyPrintable1 PartExprF where
  showP1 = \case
    ZeroSF     -> pure "Z"
    PairSF a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    EnvSF      -> pure "E"
    SetEnvSF x -> indentWithOneChild' "S" $ showP x
    -- DeferSF x  -> indentWithOneChild' "D" $ showP x
    GateSF l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    LeftSF x   -> indentWithOneChild' "L" $ showP x
    RightSF x  -> indentWithOneChild' "R" $ showP x

instance PrettyPrintable f => PrettyPrintable1 (StuckF f) where
  showP1 = \case
    StuckF d -> indentWithOneChild' "D" $ showP d

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
    NestedSetEnvsF (UnsizedRecursionToken ind) x -> indentWithOneChild' "?" $ showP x
    RecursionTestF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("T(" <> show ind <> ")") $ showP x
    SizingResultsF _ (x:_) -> (\nx -> "[" <> nx <> "...]") <$> showP x

instance PrettyPrintable1 VoidF where
  showP1 _ = error "VoidF should never be inhabited, so should not be PrettyPrintable1"

term3ToUnsizedExpr :: Functor f => Term3 -> UnsizedExpr f
term3ToUnsizedExpr (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag -> ZeroFW ZeroSF
        PairFrag a b -> ZeroFW $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag -> ZeroFW EnvSF
        SetEnvFrag x -> ZeroFW . SetEnvSF $ convertFrag' x
        DeferFrag ind -> OneFW . StuckF . convertFrag' . unFragExprUR $ fragLookup ind
        AbortFrag -> ThreeFW AbortF
        GateFrag l r -> ZeroFW $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x -> ZeroFW . LeftSF $ convertFrag' x
        RightFrag x -> ZeroFW . RightSF $ convertFrag' x
        TraceFrag -> ZeroFW EnvSF
        AuxFrag (RecursionTest tok (FragExprUR x)) -> FourFW . RecursionTestF tok $ convertFrag' x
        AuxFrag (NestedSetEnvs t) -> FourFW . NestedSetEnvsF t . embed $ ZeroFW EnvSF
  in convertFrag' . unFragExprUR $ rootFrag termMap

newtype UnsizedAggregate = UnsizedAggregate { unUnAgg :: Map UnsizedRecursionToken ( Bool, Bool) }

aggTest :: UnsizedRecursionToken -> UnsizedAggregate
aggTest x = UnsizedAggregate (Map.singleton x (True, False) )

aggSetEnvs :: UnsizedRecursionToken -> UnsizedAggregate
aggSetEnvs x = UnsizedAggregate (Map.singleton x (False, True))

instance Semigroup UnsizedAggregate where
  (<>) (UnsizedAggregate a) (UnsizedAggregate b) = UnsizedAggregate $ Map.unionWith (\(a, b) (c, d) -> (a || c, b || d)) a b

instance Monoid UnsizedAggregate where
  mempty = UnsizedAggregate $ Map.empty

readyForSizing :: UnsizedAggregate -> Bool
readyForSizing (UnsizedAggregate m) = not (null m) && all (\(a,b) -> a && b) m

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

{-
sizeTerm :: (Traversable f, PrettyPrintable s, Show s, Show1 f, Eq s, Eq1 f, PrettyPrintable1 f) =>
  Integer -> StuckExpr (SizeStuck s) (StuckUnsizedBase f) -> Either UnsizedRecursionToken (StuckExpr (SetStuck s) (StuckAbortBase f))
sizeTerm recursionLimit = tidyUp . findSize . sizeF . unStuckExpr where
  showBeginning x = trace ("sizeTerm beginning with:\n" <> prettyPrint x) x
  showSizingExpr :: (PrettyPrintable1 f) => EnhancedUnsizedStuck f s -> EnhancedUnsizedStuck f s
  showSizingExpr x = trace ("sizeTerm sizing expression:\n" <> prettyPrint x) x
  showPartialExpr x = trace ("sizeTerm partially evaled expression:\n" <> prettyPrint x) x
  sizeF = cata $ \case
    ur@(FourFW (UnsizedRecursionF x)) -> (aggSetEnvs x, FourEE $ UnsizedRecursionF x)
    ur@(FourFW (RecursionTestF t (tm, x))) -> (aggTest t <> tm, FourEE $ RecursionTestF t x)
    ZeroFW (DeferSF (tm, x)) | readyForSizing tm -> findSize (tm, ZeroEE (DeferSF x))
    x -> embed <$> sequence x
  findSize (tm, x) =
    let evaled = evalS . unsizedTermToSizeTerm $ StuckExpr testG
        sizingResults = unMonoidList . fst . recursionResult $ evaled
        testG = case x of -- hacky, to handle many situations
          ZeroEE (DeferSF _) -> ZeroEE $ FillFunction x (TwoEE AnyPF) -- from sizeF
          ZeroEE (PairSF d@(ZeroEE (DeferSF _)) _) -> ZeroEE $ FillFunction d (TwoEE AnyPF) -- compiling main
          _ -> ZeroEE $ FillFunction (ZeroEE (DeferSF x)) (TwoEE AnyPF) -- compiling test expression
        selectResult (n, r) alt = case r of
          Just (UnsizableSR _) -> (tm, x)
          Nothing -> (mempty, setSizes n x)
          _ -> alt
    in case sizingResults of
      [] -> (tm, x)
      _ -> foldr selectResult (tm, x) . tail $ zip [0..] sizingResults
  tidyUp = \case
    (UnsizedAggregate uam, _) | not (null uam) -> case Map.minViewWithKey uam of
                                  Just ((urt, _), _) -> Left urt
    (_, x) -> pure . StuckExpr . clean $ x
  clean = hoist $ \case
    ZeroFW x  -> ZeroFW x
    OneFW (StuckF (Right StuckNeedsEnv) (StuckExpr x)) -> OneFW (StuckF (Right StuckNeedsEnv) (StuckExpr $ clean x))
    TwoFW x   -> TwoFW x
    ThreeFW x -> ThreeFW x
    z         -> error "sizeTerm clean should be impossible"
  setSizes n = cata $ \case
    {-
    OneFW (StuckF (Left (Right StuckNeedsSizing)) (StuckExpr e)) -> evalPossible' $ setSizes n e
    OneFW (StuckF r (StuckExpr e)) -> OneEE (StuckF r (StuckExpr $ setSizes n e))
-}
    FourFW (UnsizedRecursionF _) -> iterate (ZeroEE . SetEnvSF) (ZeroEE EnvSF) !! n
    x -> embed x
  constish x = (x, undefined)
  recursionResult = transformM $ \case
    SizingResultsS srs -> constish . MonoidList $ map (fst . transformM gr) srs where
      gr = \case
        AbortedS AbortRecursion -> constish $ Just AbortedSR
        UnsizeableS t -> constish . Just $ UnsizableSR t
        _ -> constish Nothing
    x -> constish $ MonoidList []
-}

-- type UnsizedUnstuckBase f = UnStuckBase  (SplitFunctor (SplitFunctor (SplitFunctor f UnsizedRecursionF) AbortableF) SuperPositionF)

-- >>> fmap (+1) $ SizingResultsF (toEnum 0) [0,1]
-- SizingResultsF (UnsizedRecursionToken {unUnsizedRecursionToken = 0}) [1,2]

sizeTerm :: (Traversable f, Show1 f, Eq1 f, PrettyPrintable1 f) =>
  Integer -> UnsizedExpr f -> Either UnsizedRecursionToken (AbortExpr f)
-- sizeTerm recursionLimit = tidyUp . findSize . (\(tm, sx) -> (tm, stick sx)) . sizeF . unstick where
sizeTerm recursionLimit = tidyUp . findSize . sizeF where
  showBeginning x = trace ("sizeTerm beginning with:\n" <> prettyPrint x) x
  showSizingExpr x = trace ("sizeTerm sizing expression:\n" <> prettyPrint x) x
  showPartialExpr x = trace ("sizeTerm partially evaled expression:\n" <> prettyPrint x) x
  -- sizeF = cata $ \case
  sizeF = transformStuckM $ \case
    ur@(FourFW (NestedSetEnvsF t (tm, x))) -> (aggSetEnvs t <> tm, embed . FourFW $ NestedSetEnvsF t x)
    ur@(FourFW (RecursionTestF t (tm, x))) -> (aggTest t <> tm, embed . FourFW $ RecursionTestF t x)
  {-
    ZeroFW (PairSF (tmc, c) (tme, e)) | readyForSizing (tmc <> tme) ->
                                        findSize (tmc <> tme, embed . ZeroFW $ PairSF c e)
-}
    ZeroFW (PairSF (tmc, c@(OneEE _)) (tme, e@(ZeroEE ZeroSF))) | readyForSizing (tmc <> tme) ->
                                        findSize (tmc <> tme, embed . ZeroFW $ PairSF c e)
    -- OneFW (UnStuckF (tm, x)) | readyForSizing tm -> (\(tm, sx) -> (tm, unstick sx)) $ findSize (tm, stick . embed . OneFW $ UnStuckF x)
    x -> embed <$> sequence x
  findSize (tm, x) =
    let evaled = evalPossible testG
        sizingResults = (\f -> map (\n -> (n, f n)) $ [1..fromIntegral recursionLimit]) . recursionResults $ evaled
        testG = case x of -- hacky, to handle many situations
          OneEE (StuckF _) -> embed . ZeroFW $ fillFunction x (embed $ TwoFW AnyPF) -- from sizeF
          ZeroEE (PairSF d@(OneEE (StuckF _)) _) -> trace "doing 'main' testG" embed . ZeroFW $ fillFunction d (embed $ TwoFW AnyPF) -- compiling main
          _ -> trace "doing 'test' testG" embed . ZeroFW $ fillFunction (embed $ OneFW (StuckF x)) (embed $ TwoFW AnyPF) -- compiling test expression
        selectResult (n, r) alt = case r of
          Just (UnsizableSR _) -> (tm, x)
          Nothing -> trace ("after setting sizes is\n" <> prettyPrint (setSizes n x)) (mempty, setSizes n x)
          _ -> alt
        -- selectResult _ _ = (mempty, setSizes 10 x)
    in trace ("sizing results:\n" <> prettyPrint evaled <> "\nfrom original:\n" <> prettyPrint x) foldr selectResult (tm, x) sizingResults
  tidyUp = \case
    (UnsizedAggregate uam, _) | not (null uam) -> case Map.minViewWithKey uam of
                                  Just ((urt, _), _) -> Left urt
    (_, x) -> pure . clean $ x
  clean :: Functor f => UnsizedExpr f -> AbortExpr f
  -- clean = cata (embed . f) where
  clean = transformStuck (embed . f) where
    f = \case
  -- clean = hoist $ \case
      ZeroFW x  -> ZeroFW x
      -- OneFW x -> OneFW x
      -- OneFW (StuckF x) -> OneFW . StuckF $ clean x
      TwoFW x   -> TwoFW x
      ThreeFW x -> ThreeFW x
      z         -> error "sizeTerm clean should be impossible"
  {-
  stick :: Functor f => Fix (UnsizedUnstuckBase f) -> UnsizedExpr f
  -- stick = hoist f where
  stick = cata (embed . f) where
    -- f :: UnsizedUnstuckBase f a -> UnsizedBase (UnsizedExpr f) f a
    f = \case
      ZeroFW x -> ZeroFW x
      OneFW (UnStuckF x) -> OneFW (StuckF x)
      TwoFW x -> TwoFW x
      ThreeFW x -> ThreeFW x
      FourFW x -> FourFW x
  unstick :: Functor f => UnsizedExpr f -> Fix (UnsizedUnstuckBase f)
  -- unstick = hoist f where
  unstick = cata (embed . f) where
    -- f :: UnsizedBase (UnsizedExpr f) f a -> UnsizedUnstuckBase f a
    f x' = case x' of
      ZeroFW x -> ZeroFW x
      OneFW (StuckF x) -> OneFW (UnStuckF $ unstick x)
      TwoFW x -> TwoFW x
      ThreeFW x -> ThreeFW x
      FourFW x -> FourFW x
-}
  -- setSizes n = cata $ \case
  setSizes n = trace ("setting size to " <> show n) transformStuck $ \case
    FourFW (SizingResultsF _ rl) -> rl !! n
    FourFW (RecursionTestF _ x) -> x
    FourFW (NestedSetEnvsF _ x) -> iterate (embed . ZeroFW . SetEnvSF) x !! n
    x -> embed x
  -- recursionResults = cata $ \case
  {-
  recursionResults = transformStuckM f where
    f :: UnsizedBase (UnsizedExpr f) f (Int -> Maybe SizedResult) -> (Int -> Maybe SizedResult)
    f = \case
      ThreeFW (AbortedF AbortRecursion) -> const $ Just AbortedSR
      ThreeFW (AbortedF (AbortUnsizeable t)) -> const . Just . UnsizableSR . toEnum . g2i $ t
      FourFW (SizingResultsF _ rl) -> \n -> (rl !! n) n
      x                                 -> Data.Foldable.fold x
-}
  -- >>> Just AbortedSR <> Nothing
  --
  recursionResults :: (Functor f, Foldable f) => UnsizedExpr f -> (Int -> Maybe SizedResult)
  recursionResults = cata f where
    f :: (Functor f, Foldable f) => UnsizedBase (UnsizedExpr f) f (Int -> Maybe SizedResult) -> (Int -> Maybe SizedResult)
    f = \case
      OneFW (StuckF x) -> recursionResults x
      ThreeFW (AbortF) -> const $ Just AbortedSR
      ThreeFW (AbortedF AbortRecursion) -> const $ Just AbortedSR
      ThreeFW (AbortedF (AbortUnsizeable t)) -> const . Just . UnsizableSR . toEnum . g2i $ t
      FourFW (SizingResultsF _ rl) -> \n -> (rl !! n) n
      x                                 -> Data.Foldable.fold x
  unsizedMerge = mergeSuper (mergeAbort (mergeUnsized mergeUnknown))
  evalPossible = evalBottomUp (stuckStep (superStep unsizedMerge (abortStep (unsizedStep unhandledError))))
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)


instance Functor o => TelomareLike (StuckExpr o) where
  fromTelomare = \case
    Zero     -> embed $ ZeroFW ZeroSF
    Pair a b -> embed . ZeroFW $ PairSF (fromTelomare a) (fromTelomare b)
    Env      -> embed $ ZeroFW EnvSF
    SetEnv x -> embed . ZeroFW $ SetEnvSF (fromTelomare x)
    Defer x  -> embed . OneFW $ StuckF (fromTelomare x)
    Gate l r -> embed . ZeroFW $ GateSF (fromTelomare l) (fromTelomare r)
    PLeft x  -> embed . ZeroFW $ LeftSF (fromTelomare x)
    PRight x -> embed . ZeroFW $ RightSF (fromTelomare x)
    Trace    -> error "EnhancedExpr trace"
  toTelomare = \case
    ZeroEE x -> case x of
      ZeroSF     -> pure Zero
      PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
      EnvSF      -> pure Env
      SetEnvSF p -> SetEnv <$> toTelomare p
      -- DeferSF d  -> Defer <$> toTelomare d
      GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
      LeftSF x   -> PLeft <$> toTelomare x
      RightSF x  -> PRight <$> toTelomare x
    OneEE (StuckF x) -> Defer <$> toTelomare x
    _ -> Nothing

evalBU :: IExpr -> Maybe IExpr
evalBU = toIExpr . ebu . fromTelomare where
  toIExpr = toTelomare
  -- ebu :: StuckExpr (SetStuck Void) VoidF -> StuckExpr (SetStuck Void) VoidF
  ebu :: StuckExpr VoidF -> StuckExpr VoidF
  ebu = evalBottomUp (stuckStep undefined)

evalBU' :: IExpr -> IO IExpr
evalBU' = f . evalBU where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x

term4toAbortExpr :: Functor f => Term4 -> AbortExpr f
term4toAbortExpr (Term4 termMap) =
  let convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag      -> ZeroFW ZeroSF
        PairFrag a b  -> ZeroFW $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag       -> ZeroFW EnvSF
        SetEnvFrag x  -> ZeroFW . SetEnvSF $ convertFrag' x
        DeferFrag ind -> OneFW . StuckF . convertFrag' $ termMap Map.! ind
        AbortFrag     -> ThreeFW AbortF
        GateFrag l r  -> ZeroFW $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x    -> ZeroFW . LeftSF $ convertFrag' x
        RightFrag x   -> ZeroFW . RightSF $ convertFrag' x
        TraceFrag     -> ZeroFW EnvSF
        z             -> error ("term4toAbortExpr'' unexpected " <> show z)
  in convertFrag' (rootFrag termMap)

abortExprToTerm4 :: (Show1 f, Functor f, Foldable f, Traversable f, PrettyPrintable1 f) => AbortExpr f -> Either IExpr Term4
abortExprToTerm4 x =
  let
    findAborted = cata $ \case
      ThreeFW (AbortedF e) -> Just e
      x                    -> foldr (<|>) empty x
    -- convert :: Traversable f => AbortBase (AbortExpr f) f (State a (FragExpr Void)) -> State a (FragExpr Void)
    convert = \case
      ZeroFW ZeroSF       -> pure ZeroFrag
      ZeroFW (PairSF a b) -> PairFrag <$> a <*> b
      ZeroFW EnvSF        -> pure EnvFrag
      ZeroFW (SetEnvSF x) -> SetEnvFrag <$> x
      -- ZeroFW (DeferSF x)  -> deferF x
      OneFW (StuckF x)    -> deferF $ cata convert x
      ThreeFW AbortF      -> pure AbortFrag
      ZeroFW (GateSF l r) -> GateFrag <$> l <*> r
      ZeroFW (LeftSF x)   -> LeftFrag <$> x
      ZeroFW (RightSF x)  -> RightFrag <$> x
      -- z                   -> error ("abortExprToTerm4 unexpected thing " <> prettyPrint z) -- <> show (fmap (const ()) z))
      z                   -> error ("abortExprToTerm4 unexpected thing " )
  in case findAborted x of
    Just e -> Left e
    _      -> pure . Term4 . buildFragMap . cata convert $ x

evalA :: (Maybe IExpr -> Maybe IExpr -> Maybe IExpr) -> Maybe IExpr -> Term4 -> Maybe IExpr
evalA combine base t =
  let initialEnv :: AbortExpr VoidF
      initialEnv = embed $ TwoFW AnyPF
      unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let eval' :: AbortExpr VoidF -> AbortExpr VoidF
                      -- eval' = evalBottomUp (evalBasicDoNothing (evalSuper eval' (evalAbort unhandledError)))
                      eval' = evalBottomUp (stuckStep (superStep (mergeSuper (mergeAbort mergeUnknown)) (abortStep unhandledError)))
                  in eval' . deheadMain $ term4toAbortExpr t
      -- hack to check main functions as well as unit tests
      deheadMain = \case
        ZeroEE (PairSF (OneEE (StuckF f)) _) -> f
        x                                      -> x
      getAborted = \case
        ThreeFW (AbortedF e) -> Just e
        TwoFW (EitherPF a b) -> combine a b
        x                    -> foldr (<|>) Nothing x
  in flip combine base . cata getAborted $ trace ("evalA runResult is\n" <> prettyPrint runResult) runResult

-- type checking stuff in here, maybe replace old type checking eventually
data TypedF f
  = TypedF PartialType f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 TypedF where
  liftEq test (TypedF ta a) (TypedF tb b) = ta == tb && test a b

instance Show1 TypedF where
  liftShowsPrec showsPrec showList prec (TypedF t x) = shows "TypedF " . shows t . shows " (" . showsPrec 0 x . shows ")"
