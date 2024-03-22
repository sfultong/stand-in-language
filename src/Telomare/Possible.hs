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
import           Data.List                 (sortBy, partition)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Monoid
import           Data.Semigroup (Max(..))
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
import Data.SBV.RegExp (everything)

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
    RightSF x -> shows "RightSF (" . showsPrec 0 x . shows ")"

newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show)

instance PrettyPrintable FunctionIndex where
  showP = pure . ("F" <>) . show . fromEnum

data StuckF f
  = DeferSF FunctionIndex f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance PrettyPrintable1 StuckF where
  showP1 = \case
    DeferSF ind x -> liftM2 (<>) (showP ind) (showP x)

instance Eq1 StuckF where
  liftEq test a b = case (a,b) of
    (DeferSF ix _, DeferSF iy _) | ix == iy -> True -- test a b
    _ -> False

class BasicBase g where
  embedB :: PartExprF x -> g x
  extractB :: g x -> Maybe (PartExprF x)

class StuckBase g where
  embedS :: StuckF x -> g x
  extractS :: g x -> Maybe (StuckF x)

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
pattern StuckFW :: (StuckBase g) => StuckF x -> g x
pattern StuckFW x <- (extractS -> Just x)
pattern StuckEE :: (Base g ~ f, StuckBase f, Recursive g) => StuckF g -> g
pattern StuckEE x <- (project -> StuckFW x)
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
stuckEE :: (Base g ~ f, StuckBase f, Corecursive g) => StuckF g -> g
stuckEE = embed . embedS
superEE :: (Base g ~ f, SuperBase f, Corecursive g) => SuperPositionF g -> g
superEE = embed . embedP
abortEE :: (Base g ~ f, AbortBase f, Corecursive g) => AbortableF g -> g
abortEE = embed . embedA
unsizedEE :: (Base g ~ f, UnsizedBase f, Corecursive g) => UnsizedRecursionF g -> g
unsizedEE = embed . embedU
zeroB :: (Base g ~ f, BasicBase f, Corecursive g) => g
zeroB = basicEE ZeroSF
pairB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
pairB a b = basicEE $ PairSF a b
envB :: (Base g ~ f, BasicBase f, Corecursive g) => g
envB = basicEE EnvSF
setEnvB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
setEnvB = basicEE . SetEnvSF
gateB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
gateB l r = basicEE $ GateSF l r
leftB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
leftB = basicEE . LeftSF
rightB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
rightB = basicEE . RightSF

pattern FillFunction :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> f g
pattern FillFunction c e <- BasicFW (SetEnvSF (BasicEE (PairSF c e)))
pattern GateSwitch :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> g -> f g
pattern GateSwitch l r s <- FillFunction (BasicEE (GateSF l r)) s

fillFunction :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
fillFunction c e = setEnvB (pairB c e)

gateSwitch :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g -> g
gateSwitch  l r = fillFunction (gateB l r)

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

basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, PrettyPrintable g, Monad m) => (f (m g) -> m g) -> f (m g) -> m g
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

transformNoDefer :: (Base g ~ f, StuckBase f, Recursive g) => (f g -> g) -> g -> g
transformNoDefer f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> s
    x -> fmap c x

transformNoDeferM :: (Base g ~ f, StuckBase f, Monad m, Recursive g) => (f (m g) -> m g) -> g -> m g
transformNoDeferM f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> fmap pure s
    x -> fmap c x

stuckStep :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDefer (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db = if True -- fid == toEnum 5
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      else id
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x -> x
  -- stuck value
  x@(StuckFW _) -> embed x
  x -> handleOther x

stuckStepM :: (Base a ~ f, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f (m a) -> m a) -> f (m a) -> m a
stuckStepM handleOther x = sequence x >>= f where
  f = \case
    FillFunction (StuckEE (DeferSF fid d)) e -> transformNoDeferM runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = pure <$> project e
      replaceEnv = \case
        BasicFW EnvSF -> e'
        x -> x
    -- stuck value
    x@(StuckFW _) -> pure $ embed x
    _ -> handleOther x

superStep :: (Base a ~ f, BasicBase f, SuperBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> a -> a) -> (f a -> a) -> (f a -> a) -> f a -> a
superStep mergeSuper step handleOther = \case
    BasicFW (LeftSF (SuperEE AnyPF)) -> superEE AnyPF
    BasicFW (LeftSF (SuperEE (EitherPF a b))) -> mergeSuper (step . embedB . LeftSF $ a) (step . embedB . LeftSF $ b)
    BasicFW (RightSF (SuperEE AnyPF)) -> superEE AnyPF
    BasicFW (RightSF (SuperEE (EitherPF a b))) -> mergeSuper (step . embedB . RightSF $ a) (step . embedB . RightSF $ b)
    BasicFW (SetEnvSF (SuperEE (EitherPF a b))) -> mergeSuper (step . embedB . SetEnvSF $ a) (step . embedB . SetEnvSF $ b)
    (GateSwitch l r (SuperEE AnyPF)) -> mergeSuper l r
    (GateSwitch l r (SuperEE (EitherPF (BasicEE ZeroSF) _))) -> mergeSuper l r
    (GateSwitch l r (SuperEE (EitherPF _ (BasicEE ZeroSF)))) -> mergeSuper l r
    (GateSwitch l r (SuperEE (EitherPF a b))) -> superEE (EitherPF l r)
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

abortStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> a
    FillFunction a@(AbortEE (AbortedF _)) _ -> a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> stuckEE . DeferSF i . basicEE $ EnvSF where
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

abortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f (m a) -> m a) -> f (m a) -> m a
abortStepM handleOther x = sequence x >>= f where
  f = \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> pure a
    FillFunction a@(AbortEE (AbortedF _)) _ -> pure a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> pure . stuckEE . DeferSF i . basicEE $ EnvSF where
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

newtype SizedRecursion = SizedRecursion { unSizedRecursion :: Map UnsizedRecursionToken Int}

instance Semigroup SizedRecursion where
  (<>) (SizedRecursion a) (SizedRecursion b) = SizedRecursion $ Map.unionWith max a b

instance Monoid SizedRecursion where
  mempty = SizedRecursion Map.empty

instance PrettyPrintable1 ((,) SizedRecursion) where
  showP1 (_,x) = showP x

iteB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g -> g
iteB i t e = fillFunction (gateB e t) i

unsizedStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => Int -> (f (SizedRecursion, a) -> (SizedRecursion, a)) -> (f (SizedRecursion, a) -> (SizedRecursion, a)) -> f (SizedRecursion, a) -> (SizedRecursion, a)
unsizedStepM maxSize fullStep handleOther x = sequence x >>= f where
  f = \case
    UnsizedFW (SizingWrapperF tok (BasicEE (PairSF d (BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF))))))))))
      -> case tp of
            BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
              let nt = pairB (stuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
                  trb = pairB b (pairB r (pairB nt zeroB))
                  fi = toEnum (-1)
                  argOne = leftB envB
                  argTwo = leftB (rightB envB)
                  argThree = leftB (rightB (rightB envB))
                  argFour = leftB (rightB (rightB (rightB envB)))
                  argFive = leftB (rightB (rightB (rightB (rightB envB))))
                  deferB = stuckEE . DeferSF fi
                  twiddle = deferB $ pairB (leftB (rightB envB)) (pairB (leftB envB) (rightB (rightB envB)))
                  appB c i = setEnvB (setEnvB (pairB twiddle (pairB i c)))
                  lamB x = pairB (deferB x) envB
                  abrt = lamB . abortEE . AbortedF $ AbortRecursion
                  rf n = lamB (lamB (unsizedEE . SizeStageF tok n $ iteB (appB argFive argOne)
                                                                         (appB (appB argFour argTwo) argOne)
                                                                         (appB argThree argOne)))
                  -- rf' n = appB (rf n) (rf' (n + 1))
                  rf' n = if n > maxSize
                    -- then error "reached recursion limit"
                    -- then argThree
                    then abrt
                    else appB (rf n) (rf' (n + 1))
              in pure $ pairB (deferB $ rf' 1) trb
    UnsizedFW (RecursionTestF ri x) ->
      let test = \case
            z@(BasicEE ZeroSF) -> z
            p@(BasicEE (PairSF _ _)) -> p
            SuperEE AnyPF -> abortEE . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
            SuperEE (EitherPF a b) -> superEE $ EitherPF (test a) (test b)
            a@(AbortEE (AbortedF _)) -> a
            z -> error ("evalRecursionTest checkTest unexpected\n" <> prettyPrint z)
      in pure $ test x
    UnsizedFW (SizeStageF urt n x) -> (SizedRecursion $ Map.singleton urt n, x)
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

mergeStuck :: (Base x ~ f, StuckBase f, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeStuck mergeOther a b =
  case (a,b) of
    -- should we try merging within functions? Probably not
    (s@(StuckEE (DeferSF fida _)), StuckEE (DeferSF fidb _)) | fida == fidb -> s
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

mergeUnsized :: (Base x ~ f, UnsizedBase f, PrettyPrintable x, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> (x -> x -> x) -> x -> x -> x
mergeUnsized mergeDown mergeOther a b = case (a,b) of
  (UnsizedEE aa, UnsizedEE bb) -> case (aa,bb) of
    (RecursionTestF ta x, RecursionTestF tb y) | ta == tb -> unsizedEE . RecursionTestF ta $ mergeDown x y
    (UnsizedStubF ta x, UnsizedStubF tb y) | ta == tb -> unsizedEE . UnsizedStubF ta $ mergeDown x y
    (SizingWrapperF ta x, SizingWrapperF tb y) | ta == tb -> unsizedEE . SizingWrapperF ta $ mergeDown x y
    (SizeStageF ta na x, SizeStageF tb nb y) | ta == tb -> unsizedEE . SizeStageF ta (max na nb) $ mergeDown x y
    _ -> mergeOther a b
  _ -> mergeOther a b

mergeUnknown :: (Base x ~ f, SuperBase f, Eq x, Corecursive x, Recursive x) => x -> x -> x
mergeUnknown a b = if a == b
  then a
  else superEE $ EitherPF a b

data UnsizedRecursionF f
  = RecursionTestF UnsizedRecursionToken f
  | UnsizedStubF UnsizedRecursionToken f
  | SizingWrapperF UnsizedRecursionToken f
  | SizeStageF UnsizedRecursionToken Int f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    _                                          -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec showList prec x = case x of
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec 0 x . shows ")"
    SizeStageF urt n x -> shows "SizeStageF " . shows urt . shows "_" . shows n
      . shows " (" . showsPrec 0 x . shows ")"

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
    UnsizedStubF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("#" <> show ind) $ showP x
    SizeStageF (UnsizedRecursionToken ind) n x -> indentWithOneChild' ("^" <> show ind <> "|" <> show n) $ showP x

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

data StuckExprF f
  = StuckExprB (PartExprF f)
  | StuckExprS (StuckF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase StuckExprF where
  embedB = StuckExprB
  extractB = \case
    StuckExprB x -> Just x
    _ -> Nothing
instance StuckBase StuckExprF where
  embedS = StuckExprS
  extractS = \case
    StuckExprS x -> Just x
    _ -> Nothing
instance PrettyPrintable1 StuckExprF where
  showP1 = \case
    StuckExprB x -> showP1 x
    StuckExprS x -> showP1 x

type StuckExpr = Fix StuckExprF
instance PrettyPrintable StuckExpr where
  showP = showP1 . project

data UnsizedExprF f
  = UnsizedExprB (PartExprF f)
  | UnsizedExprS (StuckF f)
  | UnsizedExprP (SuperPositionF f)
  | UnsizedExprA (AbortableF f)
  | UnsizedExprU (UnsizedRecursionF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase UnsizedExprF where
  embedB = UnsizedExprB
  extractB = \case
    UnsizedExprB x -> Just x
    _ -> Nothing
instance StuckBase UnsizedExprF where
  embedS = UnsizedExprS
  extractS = \case
    UnsizedExprS x -> Just x
    _ -> Nothing
instance SuperBase UnsizedExprF where
  embedP = UnsizedExprP
  extractP = \case
    UnsizedExprP x -> Just x
    _ -> Nothing
instance AbortBase UnsizedExprF where
  embedA = UnsizedExprA
  extractA = \case
    UnsizedExprA x -> Just x
    _ -> Nothing
instance UnsizedBase UnsizedExprF where
  embedU = UnsizedExprU
  extractU = \case
    UnsizedExprU x -> Just x
    _ -> Nothing
instance Eq1 UnsizedExprF where
  liftEq test a b = case (a,b) of
    (UnsizedExprB x, UnsizedExprB y) -> liftEq test x y
    (UnsizedExprS x, UnsizedExprS y) -> liftEq test x y
    (UnsizedExprP x, UnsizedExprP y) -> liftEq test x y
    (UnsizedExprA x, UnsizedExprA y) -> liftEq test x y
    (UnsizedExprU x, UnsizedExprU y) -> liftEq test x y
    _ -> False
instance PrettyPrintable1 UnsizedExprF where
  showP1 = \case
    UnsizedExprB x -> showP1 x
    UnsizedExprS x -> showP1 x
    UnsizedExprP x -> showP1 x
    UnsizedExprA x -> showP1 x
    UnsizedExprU x -> showP1 x

type UnsizedExpr = Fix UnsizedExprF
instance PrettyPrintable UnsizedExpr where
  showP = showP1 . project

data SuperExprF f
  = SuperExprB (PartExprF f)
  | SuperExprS (StuckF f)
  | SuperExprA (AbortableF f)
  | SuperExprP (SuperPositionF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase SuperExprF where
  embedB = SuperExprB
  extractB = \case
    SuperExprB x -> Just x
    _ -> Nothing
instance StuckBase SuperExprF where
  embedS = SuperExprS
  extractS = \case
    SuperExprS x -> Just x
    _ -> Nothing
instance AbortBase SuperExprF where
  embedA = SuperExprA
  extractA = \case
    SuperExprA x -> Just x
    _ -> Nothing
instance SuperBase SuperExprF where
  embedP = SuperExprP
  extractP = \case
    SuperExprP x -> Just x
    _ -> Nothing
instance Eq1 SuperExprF where
  liftEq test a b = case (a,b) of
    (SuperExprB x, SuperExprB y) -> liftEq test x y
    (SuperExprS x, SuperExprS y) -> liftEq test x y
    (SuperExprA x, SuperExprA y) -> liftEq test x y
    (SuperExprP x, SuperExprP y) -> liftEq test x y
    _ -> False
instance PrettyPrintable1 SuperExprF where
  showP1 = \case
    SuperExprB x -> showP1 x
    SuperExprS x -> showP1 x
    SuperExprA x -> showP1 x
    SuperExprP x -> showP1 x

type SuperExpr = Fix SuperExprF
instance PrettyPrintable SuperExpr where
  showP = showP . project

data AbortExprF f
  = AbortExprB (PartExprF f)
  | AbortExprS (StuckF f)
  | AbortExprA (AbortableF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase AbortExprF where
  embedB = AbortExprB
  extractB = \case
    AbortExprB x -> Just x
    _ -> Nothing
instance StuckBase AbortExprF where
  embedS = AbortExprS
  extractS = \case
    AbortExprS x -> Just x
    _ -> Nothing
instance AbortBase AbortExprF where
  embedA = AbortExprA
  extractA = \case
    AbortExprA x -> Just x
    _ -> Nothing
instance Eq1 AbortExprF where
  liftEq test a b = case (a,b) of
    (AbortExprB x, AbortExprB y) -> liftEq test x y
    (AbortExprS x, AbortExprS y) -> liftEq test x y
    (AbortExprA x, AbortExprA y) -> liftEq test x y
    _ -> False
instance PrettyPrintable1 AbortExprF where
  showP1 = \case
    AbortExprB x -> showP1 x
    AbortExprS x -> showP1 x
    AbortExprA x -> showP1 x

type AbortExpr = Fix AbortExprF
instance PrettyPrintable AbortExpr where
  showP = showP . project

instance PrettyPrintable Char where
  showP = pure . (:[])

unsized2abortExpr :: UnsizedExpr -> AbortExpr
unsized2abortExpr = hoist f where
  f :: UnsizedExprF a -> AbortExprF a
  f = \case
    UnsizedExprB x -> AbortExprB x
    UnsizedExprS x -> AbortExprS x
    -- UnsizedExprP x -> AbortExprP x
    UnsizedExprA x -> AbortExprA x
    x -> error $ "unsized2abortExpr unexpected unsized bit: " <> prettyPrint (fmap (const ' ') x)

term3ToUnsizedExpr :: Int -> Term3 -> UnsizedExpr
term3ToUnsizedExpr maxSize (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag -> embedB ZeroSF
        PairFrag a b -> embedB $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag -> embedB EnvSF
        SetEnvFrag x -> embedB . SetEnvSF $ convertFrag' x
        DeferFrag ind -> embedS . DeferSF (toEnum $ fromEnum ind) . convertFrag' . unFragExprUR $ fragLookup ind
        AbortFrag -> embedA AbortF
        GateFrag l r -> embedB $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x -> embedB . LeftSF $ convertFrag' x
        RightFrag x -> embedB . RightSF $ convertFrag' x
        TraceFrag -> embedB EnvSF
        AuxFrag (SizingWrapper tok (FragExprUR x)) -> embedU . SizingWrapperF tok $ convertFrag' x
        AuxFrag (NestedSetEnvs t) -> embedU . UnsizedStubF t . embed $ embedB EnvSF
  in convertFrag' . unFragExprUR $ rootFrag termMap

data SizedResult = AbortedSR | UnsizableSR UnsizedRecursionToken
  deriving (Eq, Ord, Show)

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

capMain :: (Base g ~ f, BasicBase f, StuckBase f, SuperBase f, Recursive g, Corecursive g) => g -> g
capMain = \case  -- make sure main functions are fully applied with Any data
  BasicEE (PairSF d@(StuckEE (DeferSF _ _)) _) -> basicEE . SetEnvSF . basicEE . PairSF d $ superEE AnyPF
  x -> x

isClosure :: (Base g ~ f, BasicBase f, StuckBase f, SuperBase f, Recursive g, Corecursive g) => g -> Bool
isClosure = \case
  BasicEE (PairSF (StuckEE (DeferSF _ _)) _) -> True
  _ -> False

sizeTerm :: Int -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
sizeTerm maxSize x = tidyUp . transformNoDeferM evalStep $ capMain x where
  tidyUp (SizedRecursion sm, r) = case foldAborted r of
    Just (UnsizableSR i) -> Left i
    _ -> let sized = setSizes sm x
         in pure . clean $ if isClosure x
            then uncap sized
            else sized
      where uncap = \case
              BasicEE (SetEnvSF (BasicEE (PairSF d _))) -> basicEE $ PairSF d (basicEE ZeroSF)
              _ -> error "sizeTerm tidyUp trying to uncap something that isn't a main function"
  clean = unsized2abortExpr
  setSizes :: Map UnsizedRecursionToken Int -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = trace ("setting sizes: " <> show sizeMap) cata $ \case
    UnsizedFW sw@(SizingWrapperF tok sx) -> case Map.lookup tok sizeMap of
      Just _ -> sx
      _ -> unsizedEE sw
    UnsizedFW us@(UnsizedStubF tok _) -> case Map.lookup tok sizeMap of
      Just n -> iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _ -> unsizedEE us
    x -> embed x
  foldAborted :: UnsizedExpr -> Maybe SizedResult
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF AbortRecursion) -> Just AbortedSR
      AbortFW (AbortedF (AbortUnsizeable t)) -> Just . UnsizableSR . toEnum . g2i $ t
      x                                 -> Data.Foldable.fold x
  unsizedMerge = mergeBasic (mergeStuck (mergeAbort (mergeSuper unsizedMerge (mergeUnsized unsizedMerge mergeUnknown))))
  evalStep = basicStepM (stuckStepM (abortStepM (superStepM unsizedMerge evalStep (unsizedStepM maxSize evalStep (anyFunctionStepM unhandledError)))))
  {-
  debugStep :: UnsizedExprF UnsizedExpr -> UnsizedExpr
  debugStep x =
    let nx = evalStep x
        hasBad = f where
          f = \case
            BasicEE (SetEnvSF (BasicEE (PairSF (BasicEE ZeroSF) _))) -> True
            x -> getAny . foldMap (Any . f) $ project x
    in if hasBad nx
          then error ("found potential issue before:\n" <> prettyPrint x <> "\n---after---\n" <> prettyPrint nx)
          else nx
-}
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)

convertToF :: (Base g ~ f, BasicBase f, StuckBase f, Traversable f, Corecursive g) => IExpr -> g
convertToF = flip State.evalState (toEnum 0) . anaM' f where
  f = \case
    Zero -> pure $ embedB ZeroSF
    Pair a b -> pure . embedB $ PairSF a b
    Env -> pure $ embedB EnvSF
    SetEnv x -> pure . embedB $ SetEnvSF x
    Defer x -> embedS <$> (DeferSF <$> nextVar <*> pure x)
    Gate l r -> pure . embedB $ GateSF l r
    PLeft x -> pure . embedB $ LeftSF x
    PRight x -> pure . embedB $ RightSF x
    Trace    -> error "EnhancedExpr trace"
  nextVar :: State FunctionIndex FunctionIndex
  nextVar = do
    i <- State.get
    State.put $ succ i
    pure i

convertFromF :: (Base g ~ f, TelomareLike g, BasicBase f, StuckBase f, Traversable f, Recursive g) => g -> Maybe IExpr
convertFromF = \case
  BasicEE x -> case x of
    ZeroSF     -> pure Zero
    PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
    EnvSF      -> pure Env
    SetEnvSF p -> SetEnv <$> toTelomare p
    GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
    LeftSF x   -> PLeft <$> toTelomare x
    RightSF x  -> PRight <$> toTelomare x
  StuckEE (DeferSF _ x) -> Defer <$> toTelomare x
  _ -> Nothing

instance TelomareLike StuckExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

instance TelomareLike UnsizedExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

instance TelomareLike AbortExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

evalBU :: IExpr -> Maybe IExpr
evalBU = toIExpr . ebu . fromTelomare where
  toIExpr = toTelomare
  ebu :: StuckExpr -> StuckExpr
  ebu = transformNoDefer (basicStep (stuckStep undefined) . (\x -> debugTrace ("evalBU starting expr:\n" <> prettyPrint x) x))

evalBU' :: IExpr -> IO IExpr
evalBU' = f . evalBU where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x

term4toAbortExpr :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Corecursive g) => Term4 -> g
term4toAbortExpr (Term4 termMap) =
  let convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag      -> embedB ZeroSF
        PairFrag a b  -> embedB $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag       -> embedB EnvSF
        SetEnvFrag x  -> embedB . SetEnvSF $ convertFrag' x
        DeferFrag ind -> embedS . DeferSF (toEnum . fromEnum $ ind) . convertFrag' $ termMap Map.! ind
        AbortFrag     -> embedA AbortF
        GateFrag l r  -> embedB $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x    -> embedB . LeftSF $ convertFrag' x
        RightFrag x   -> embedB . RightSF $ convertFrag' x
        TraceFrag     -> embedB EnvSF
        z             -> error ("term4toAbortExpr'' unexpected " <> show z)
  in convertFrag' (rootFrag termMap)

abortExprToTerm4 :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Foldable f, Recursive g) => g -> Either IExpr Term4
abortExprToTerm4 x =
  let
    findAborted = cata $ \case
      AbortFW (AbortedF e) -> Just e
      x                    -> foldr (<|>) empty x
    convert = \case
      BasicFW ZeroSF       -> pure ZeroFrag
      BasicFW (PairSF a b) -> PairFrag <$> a <*> b
      BasicFW EnvSF        -> pure EnvFrag
      BasicFW (SetEnvSF x) -> SetEnvFrag <$> x
      StuckFW (DeferSF _ x)    -> deferF x
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
      runResult = let aStep :: SuperExprF SuperExpr -> SuperExpr
                      aStep = basicStep (stuckStep (superStep aMerge aStep (abortStep unhandledError)))
                      aMerge = mergeBasic (mergeStuck (mergeSuper aMerge (mergeAbort mergeUnknown)))
                      eval' :: SuperExpr -> SuperExpr
                      eval' = transformNoDefer aStep
                  in eval' . capMain $ term4toAbortExpr t
      getAborted = \case
        AbortFW (AbortedF e) -> Just e
        SuperFW (EitherPF a b) -> combine a b
        x                    -> foldr (<|>) Nothing x
  in flip combine base . cata getAborted $ runResult

newtype VarIndex = VarIndex { unVarIndex :: Int } deriving (Eq, Ord, Enum, Show)

data BitsExprF f
  = ZeroB
  | PairB f f
  | FunctionB VarIndex f
  | SetEnvB f
  | GateB f f
  | VarB VarIndex
  | AbortB
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type BitsExpr = Fix BitsExprF

data BitsExprWMap = BitsExprWMap BitsExpr (Map VarIndex BitsExpr)

data EnvAnnotation a f
  = EnvAnnotation a f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data NumberedEnvsF f
  = NDeferF VarIndex f
  | NEnv VarIndex
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data NumberedEnvsBase f
  = NumberedEnvsB (PartExprF f)
  | NumberedEnvsS (StuckF f)
  | NumberedEnvsA (AbortableF f)
  | NumberedEnvsN (NumberedEnvsF f)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
instance BasicBase NumberedEnvsBase where
  embedB = NumberedEnvsB
  extractB = \case
    NumberedEnvsB x -> Just x
    _ -> Nothing
instance StuckBase NumberedEnvsBase where
  embedS = NumberedEnvsS
  extractS = \case
    NumberedEnvsS x -> Just x
    _ -> Nothing
instance AbortBase NumberedEnvsBase where
  embedA = NumberedEnvsA
  extractA = \case
    NumberedEnvsA x -> Just x
    _ -> Nothing

type NumberedEnvsExpr = Fix NumberedEnvsBase

-- | takes abortexpr and converts it to an expression where defer indexes are converted to variable indexes, and all envs underneath are given the same ids
convertEnvs :: AbortExpr -> NumberedEnvsExpr
convertEnvs = ($ toEnum 0) . cata f where
  f :: AbortExprF (VarIndex -> NumberedEnvsExpr) -> VarIndex -> NumberedEnvsExpr
  f x n = case x of
    StuckFW (DeferSF ni dx) -> let nen = toEnum $ fromEnum ni in embed . NumberedEnvsN . NDeferF nen $ dx nen
    BasicFW EnvSF -> embed . NumberedEnvsN $ NEnv n
    BasicFW x -> basicEE . ($ n) $ sequence x
    StuckFW x -> stuckEE . ($ n) $ sequence x
    AbortFW x -> abortEE . ($ n) $ sequence x

convertToBits :: VarIndex -> NumberedEnvsExpr -> (BitsExpr, (VarIndex, Map VarIndex BitsExpr))
convertToBits startVar = flip State.runState (startVar, Map.empty) . cata f where
  f = fmap embed . g
  g = \case
    BasicFW x -> case x of
      ZeroSF -> pure ZeroB
      PairSF a b -> PairB <$> a <*> b
      SetEnvSF x -> SetEnvB <$> x
      GateSF l r -> GateB <$> l <*> r
      LeftSF x' -> fmap project x' >>= \case
        VarB i -> do
          eVar <- lookupM i
          case eVar of
            Nothing -> do
              ln <- nextVar
              rn <- nextVar
              addKey i . embed $ PairB (embed $ VarB ln) (embed $ VarB rn)
              pure $ VarB ln
            Just (Fix (PairB l r)) -> case project l of
              el -> pure el
        s@(SetEnvB _) -> do
          ln <- nextVar
          rn <- nextVar
          fin <- nextVar
          addKey fin . embed $ PairB (embed $ VarB ln) (embed $ VarB rn)
          pure . SetEnvB . embed $ PairB (embed . FunctionB fin . embed $ VarB ln) (embed s)
      RightSF x' -> fmap project x' >>= \case
        VarB i -> do
          eVar <- lookupM i
          case eVar of
            Nothing -> do
              ln <- nextVar
              rn <- nextVar
              addKey i . embed $ PairB (embed $ VarB ln) (embed $ VarB rn)
              pure $ VarB rn
            Just (Fix (PairB l r)) -> case project r of
              er -> pure er
        s@(SetEnvB _) -> do
          ln <- nextVar
          rn <- nextVar
          fin <- nextVar
          addKey fin . embed $ PairB (embed $ VarB ln) (embed $ VarB rn)
          pure . SetEnvB . embed $ PairB (embed . FunctionB fin . embed $ VarB rn) (embed s)
    NumberedEnvsN x -> case x of
      NDeferF ni x' -> FunctionB ni <$> x'
      NEnv vi -> pure $ VarB vi
    AbortFW AbortF -> trace "convertToBits doing abort now" pure AbortB
  nextVar = do
    (i, m) <- State.get
    State.put (succ i, m)
    pure i
  lookupM :: VarIndex -> State (VarIndex, Map VarIndex BitsExpr) (Maybe BitsExpr)
  lookupM k = do
    (_, m) <- State.get
    pure $ Map.lookup k m
  addKey k v = State.modify (second (Map.insert k v))

-- selective transform, stops at function boundaries
transformS :: (BitsExprF BitsExpr -> BitsExpr) -> BitsExpr -> BitsExpr
transformS f =
  let s = \case
        fu@(FunctionB _ _) -> fu
        x -> fmap c x
      c = f . s . project
  in c

evalB :: BitsExprWMap -> BitsExprWMap
evalB (BitsExprWMap x varMap) = showExpr BitsExprWMap (transformS (f varMap) x) varMap where
  showExpr = debugTrace ("evalB BitsExprWMap\n" <> prettyPrint (BitsExprWMap x varMap))
  f vm = \case
    SetEnvB (Fix (PairB df e)) -> case project df of
      GateB l r -> case project e of
        ZeroB -> l
        PairB _ _ -> r
      AbortB -> trace "doing abort here" $ case project e of
        ZeroB -> embed . FunctionB tempIndex . embed $ VarB tempIndex
        _ -> embed AbortB
      FunctionB vi dx -> showAssign $ transformS (f boundMap) dx where
        boundMap = assignInputVars vi e varMap
        showAssign x = if vi == toEnum 8
          then debugTrace ("assigning inputs for 8:\n" <> prettyPrint e) x
          else x
      z -> error ("evalB setenv pair f _, found unexpected f of " <> show z <> "\nalso, e is " <> prettyPrint e)
    VarB v -> deepLookup vm v
    x -> embed x
  assignInputVars :: VarIndex -> BitsExpr -> Map VarIndex BitsExpr -> Map VarIndex BitsExpr
  assignInputVars vin vars = case (vin, Map.lookup vin varMap, project vars) of
    (_, Just (Fix (PairB (Fix (VarB a)) (Fix (VarB b)))), PairB c d) -> assignInputVars a c . assignInputVars b d
    (k, _, v) -> Map.insert k $ embed v
    (_, Just za, zb) -> error $ "evalB assignInputVars got " <> prettyPrint za <> "\nand:\n" <> prettyPrint zb
  tempIndex = toEnum (-1)
  deepLookup vm vi = case Map.lookup vi vm of
    Nothing -> embed $ VarB vi
    (Just (Fix p@(PairB _ _))) -> embed $ fmap lookupIV p where
      lookupIV = \case
        Fix (VarB vi') -> deepLookup vm vi'
        x -> x
    Just x -> x

instance PrettyPrintable1 BitsExprF where
  showP1 = \case
    ZeroB -> pure "Z"
    PairB a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    FunctionB vi x -> indentWithOneChild' ("F" <> show (fromEnum vi)) (showP x)
    SetEnvB x -> indentWithOneChild' "S" $ showP x
    GateB l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    VarB vi -> pure $ "V" <> (show $ fromEnum vi)
    AbortB -> pure "A"

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

instance Show1 BitsExprF where
  liftShowsPrec showsPrec showList prec = \case
    ZeroB -> shows "ZeroB"
    PairB a b -> shows "PairB (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
    FunctionB vi x -> shows "FunctionB " . shows vi . shows " (" . showsPrec 0 x  . shows ")"
    SetEnvB x -> shows "SetEnvB (" . showsPrec 0 x . shows ")"
    GateB l r -> shows "GateB (" . showsPrec 0 l . shows ", " . showsPrec 0 r . shows ")"
    VarB vi -> shows "VarB " . shows vi
    AbortB -> shows "AbortB"

instance TelomareLike BitsExprWMap where
  fromTelomare = wrapUp . convertToBits' . convertEnvs . fromTelomare where
    convertToBits' nee = let vi = toEnum . getMax $ cata f nee
                             f = \case
                               NumberedEnvsN (NEnv n) -> Max $ fromEnum n
                               x -> Data.Foldable.fold x
                         in convertToBits vi nee
    wrapUp (expr, (_, m)) = BitsExprWMap expr m
  toTelomare (BitsExprWMap x varMap) = cata (f iVarMap) x where
    iVarMap = cata doFuns x
    doFuns :: BitsExprF (Map VarIndex IExpr) -> Map VarIndex IExpr
    doFuns = \case
      FunctionB vi m -> addPaths id (deepLookup . embed $ VarB vi) m where
        deepLookup vin = case vin of
          vo@(Fix (VarB v)) -> case Map.lookup v varMap of
            Nothing -> vo
            (Just (Fix p@(PairB _ _))) -> embed $ fmap deepLookup p
        addPaths prefix = \case
          Fix (PairB a b) -> addPaths (PLeft . prefix) a . addPaths (PRight . prefix) b
          Fix (VarB v) -> Map.insert v (prefix Env)
          _ -> id
      x -> Data.Foldable.fold x
    f iVarMap = \case
      ZeroB -> pure Zero
      PairB a b -> Pair <$> a <*> b
      VarB v -> Map.lookup v iVarMap
      SetEnvB x -> SetEnv <$> x
      FunctionB _ x -> Defer <$> x
      GateB l r -> Gate <$> l <*> r
      -- _ -> Nothing
      z -> trace ("bitsexprwmap totelomare found unexpected " <> show z) Nothing

debugEvalB x@(BitsExprWMap _ m) = debugTrace ("evalB evaluated to " <> prettyPrint x <> "\nand map is " <> show m) x

evalB' :: IExpr -> Maybe IExpr
evalB' = toTelomare . debugEvalB . evalB . fromTelomare

evalB'' :: IExpr -> IO IExpr
evalB'' = f . evalB' where
  f = \case
    Nothing -> error "evalB' evaluated to Nothing"
    Just x -> pure x
