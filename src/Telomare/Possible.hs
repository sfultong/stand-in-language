{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

module Telomare.Possible where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Lens.Plated (transform)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State.Strict (State, StateT)
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class
import Data.Bifunctor
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Fix (Fix (..), hoistFix')
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Kind
import Data.List (nubBy, partition, sortBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid
import Data.SBV ((.<), (.>))
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug
import Debug.Trace
import PrettyPrint
import Telomare (BreakState' (..), FragExpr (..), FragExprF (..),
                 FragExprUR (..), FragIndex, IExpr (..), IExprF (SetEnvF),
                 LocTag (DummyLoc), PartialType (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..),
                 TelomareLike (fromTelomare, toTelomare), Term3 (..),
                 Term4 (..), UnsizedRecursionToken (UnsizedRecursionToken),
                 buildFragMap, deferF, forget, g2i, i2g, indentWithChildren',
                 indentWithOneChild, indentWithOneChild', indentWithTwoChildren,
                 indentWithTwoChildren', pattern AbortAny,
                 pattern AbortRecursion, pattern AbortUnsizeable, rootFrag,
                 sindent, convertAbortMessage, pattern AbortUser, s2g, toPartialType)
import Data.Validity (Validity (..), trivialValidation, declare)
import GHC.Generics (Generic)
import Data.Semigroup (Max(..))
import Data.GenValidity
import Data.GenValidity.Map
import Test.QuickCheck.Gen (sized)
import Test.QuickCheck (Gen, oneof, Arbitrary (..))
import Control.Comonad.Trans.Cofree (CofreeF, headF)

-- import           Telomare.TypeChecker
debug :: Bool
debug = True

debugTrace :: String -> a -> a
-- debugTrace s x = if debug then debugTrace' s x else x
debugTrace s x = if debug then trace s x else x

anaM' :: (Monad m, Corecursive t, x ~ Base t, Traversable x) => (a -> m (Base t a)) -> a -> m t
anaM' f = c where c = (fmap embed . mapM c) <=< f

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
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

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

newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show, Generic)

instance Validity FunctionIndex

instance PrettyPrintable FunctionIndex where
  showP = pure . ("F" <>) . show . fromEnum

data StuckF f
  = DeferSF FunctionIndex f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Show1 StuckF where
  liftShowsPrec showsPrec showList prec = \case
    DeferSF fi x -> shows "DeferSF " . shows fi . shows " (" . showsPrec 0 x . shows ")"
instance PrettyPrintable1 StuckF where
  showP1 = \case
    DeferSF ind x -> liftM2 (<>) (fmap (<> " ") $ showP ind) (showP x)
instance Eq1 StuckF where
  liftEq test a b = case (a,b) of
    (DeferSF ix _, DeferSF iy _) | ix == iy -> True -- test a b
    _                                       -> False

class BasicBase g where
  embedB :: PartExprF x -> g x
  extractB :: g x -> Maybe (PartExprF x)

class StuckBase g where
  embedS :: StuckF x -> g x
  extractS :: g x -> Maybe (StuckF x)

class SuperBase g where
  embedP :: SuperPositionF x -> g x
  extractP :: g x -> Maybe (SuperPositionF x)

class FuzzyBase g where
  embedF :: FuzzyInputF x -> g x
  extractF :: g x -> Maybe (FuzzyInputF x)

class AbortBase g where
  embedA :: AbortableF x -> g x
  extractA :: g x -> Maybe (AbortableF x)

class UnsizedBase g where
  embedU :: UnsizedRecursionF x -> g x
  extractU :: g x -> Maybe (UnsizedRecursionF x)

class IndexedInputBase g where
  embedI :: IndexedInputF x -> g x
  extractI :: g x -> Maybe (IndexedInputF x)

class DeferredEvalBase g where
  embedD :: DeferredEvalF x -> g x
  extractD :: g x -> Maybe (DeferredEvalF x)

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
pattern FuzzyFW :: FuzzyBase g => FuzzyInputF x -> g x
pattern FuzzyFW x <- (extractF -> Just x)
pattern FuzzyEE :: (Base g ~ f, FuzzyBase f, Recursive g) => FuzzyInputF g -> g
pattern FuzzyEE x <- (project -> (FuzzyFW x))
pattern AbortFW :: AbortBase g => AbortableF x -> g x
pattern AbortFW x <- (extractA -> Just x)
pattern AbortEE :: (Base g ~ f, AbortBase f, Recursive g) => AbortableF g -> g
pattern AbortEE x <- (project -> (AbortFW x))
pattern UnsizedFW :: UnsizedBase g => UnsizedRecursionF x -> g x
pattern UnsizedFW x <- (extractU -> Just x)
pattern UnsizedEE :: (Base g ~ f, UnsizedBase f, Recursive g) => UnsizedRecursionF g -> g
pattern UnsizedEE x <- (project -> (UnsizedFW x))
pattern IndexedFW :: IndexedInputBase g => IndexedInputF x -> g x
pattern IndexedFW x <- (extractI -> Just x)
pattern IndexedEE :: (Base g ~ f, IndexedInputBase f, Recursive g) => IndexedInputF g -> g
pattern IndexedEE x <- (project -> (IndexedFW x))
pattern DeferredFW :: DeferredEvalBase g => DeferredEvalF x -> g x
pattern DeferredFW x <- (extractD -> Just x)
pattern DeferredEE :: (Base g ~ f, DeferredEvalBase f, Recursive g) => DeferredEvalF g -> g
pattern DeferredEE x <- (project -> (DeferredFW x))
basicEE :: (Base g ~ f, BasicBase f, Corecursive g) => PartExprF g -> g
basicEE = embed . embedB
stuckEE :: (Base g ~ f, StuckBase f, Corecursive g) => StuckF g -> g
stuckEE = embed . embedS
superEE :: (Base g ~ f, SuperBase f, Corecursive g) => SuperPositionF g -> g
superEE = embed . embedP
fuzzyEE :: (Base g ~ f, FuzzyBase f, Corecursive g) => FuzzyInputF g -> g
fuzzyEE = embed . embedF
abortEE :: (Base g ~ f, AbortBase f, Corecursive g) => AbortableF g -> g
abortEE = embed . embedA
unsizedEE :: (Base g ~ f, UnsizedBase f, Corecursive g) => UnsizedRecursionF g -> g
unsizedEE = embed . embedU
indexedEE :: (Base g ~ f, IndexedInputBase f, Corecursive g) => IndexedInputF g -> g
indexedEE = embed . embedI
deferredEE :: (Base g ~ f, DeferredEvalBase f, Corecursive g) => DeferredEvalF g -> g
deferredEE = embed . embedD
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
gateSwitch l r = fillFunction (gateB l r)

basicStep :: (Base g ~ f, BasicBase f, Corecursive g, Recursive g) => (f g -> g) -> f g -> g
basicStep handleOther = \case
  BasicFW (LeftSF z@(BasicEE ZeroSF))      -> z
  BasicFW (LeftSF (BasicEE (PairSF l _)))  -> l
  BasicFW (RightSF z@(BasicEE ZeroSF))     -> z
  BasicFW (RightSF (BasicEE (PairSF _ r))) -> r
  GateSwitch l _ (BasicEE ZeroSF)          -> l
  GateSwitch _ r (BasicEE (PairSF _ _))    -> r
  -- stuck values
  x@(BasicFW ZeroSF)                       -> embed x
  x@(BasicFW (PairSF _ _))                 -> embed x
  x@(BasicFW (GateSF _ _))                 -> embed x
  x                                        -> handleOther x

basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, PrettyPrintable g, Monad m) => (f g -> m g) -> f g -> m g
basicStepM handleOther x = f x where
  f = \case
    BasicFW (LeftSF z@(BasicEE ZeroSF))      -> pure z
    BasicFW (LeftSF (BasicEE (PairSF l _)))  -> pure l
    BasicFW (RightSF z@(BasicEE ZeroSF))     -> pure z
    BasicFW (RightSF (BasicEE (PairSF _ r))) -> pure r
    GateSwitch l _ (BasicEE ZeroSF)          -> pure l
    GateSwitch _ r (BasicEE (PairSF _ _))    -> pure r
    -- stuck values
    x@(BasicFW ZeroSF)                       -> pure $ embed x
    x@(BasicFW (PairSF _ _))                 -> pure $ embed x
    x@(BasicFW (GateSF _ _))                 -> pure $ embed x

    _                                        -> handleOther x

transformNoDefer :: (Base g ~ f, StuckBase f, Recursive g) => (f g -> g) -> g -> g
transformNoDefer f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> s
    x                         -> fmap c x

transformNoDeferM :: (Base g ~ f, StuckBase f, Traversable f, Monad m, Recursive g) => (f g -> m g) -> g -> m g
transformNoDeferM f = c where
  c = (f =<<) . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> pure s
    x                         -> mapM c x

stuckStep :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDefer (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db = if False --  fid == toEnum (-6)
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      -- then debugTrace ("function " <> show fid)
      else id
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x             -> x
  -- stuck value
  x@(StuckFW _) -> embed x
  x -> handleOther x

stuckStepM :: (Base a ~ f, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
stuckStepM handleOther x = f x where
  f = \case
    FillFunction (StuckEE (DeferSF fid d)) e -> transformNoDeferM runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = project e
      replaceEnv = \case
        BasicFW EnvSF -> e'
        x             -> x
    -- stuck value
    x@(StuckFW _) -> pure $ embed x
    _ -> handleOther x

data GateResult a
  = GateResult
  { leftBranch :: Bool
  , rightBranch :: Bool
  , noBranch :: Maybe a
  }

{-
instance (Base g ~ f, SuperBase f, Corecursive g) => Semigroup (GateResult g) where
  (<>) (GateResult la ra ba) (GateResult lb rb bb) = GateResult (la || lb) (ra || rb) $ comb ba bb where
    comb ba bb = case (ba, bb) of
      (Just ba', Just bb') -> superEE $ EitherPF ba bb
      _ -> ba <|> bb

instance Monoid (GateResult g) where
  mempty = GateResult False False Nothing
-}

gateBasicResult :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateBasicResult handleOther = \case
  BasicEE ZeroSF -> GateResult True False Nothing
  BasicEE (PairSF _ _) -> GateResult False True Nothing
  x -> handleOther x

gateSuperResult :: (Base g ~ f, SuperBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> (g -> GateResult g) -> g -> GateResult g
gateSuperResult step handleOther = \case
  SuperEE (EitherPF a b) -> let GateResult la ra ba = step a
                                GateResult lb rb bb = step b
                                co = case (ba, bb) of
                                  (Just ba', Just bb') -> pure . superEE $ EitherPF ba' bb'
                                  _ -> ba <|> bb
                            in debugTrace " " GateResult (la || lb) (ra || rb) co
  x -> handleOther x

gateAbortResult :: (Base g ~ f, AbortBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateAbortResult handleOther = \case
  a@(AbortEE (AbortedF _)) -> GateResult False False $ Just a
  x -> handleOther x

gateIndexedResult :: (Base g ~ f, IndexedInputBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateIndexedResult handleOther = \case
  IndexedEE (IVarF n) -> GateResult True False Nothing
  x -> handleOther x

{-
gateUnsizedResult :: (Base g ~ f, UnsizedBase f, SuperBase f, Recursive g, Corecursive g) => (g -> g -> g -> GateResult g) -> (g -> g -> g -> GateResult g)
  -> g -> g -> g -> GateResult g
gateUnsizedResult step handleOther l r = \case
  -- UnsizedEE (SizeStageF _ x) -> step l r x
  UnsizedEE (SizeStageF sr x) -> GateResult False False . pure . unsizedEE . SizeStageF sr . foldGateResult l r $ step l r x
  x -> handleOther l r x
-}

mergeShallow :: (Base g ~ f, SuperBase f, ShallowEq1 f, Recursive g, Corecursive g) => g -> g -> g
mergeShallow a b = if shallowEq1 (project a) (project b)
  then a
  else superEE $ EitherPF a b

foldGateResult :: forall g f. (Base g ~ f, SuperBase f, Corecursive g) => g -> g -> GateResult g -> g
foldGateResult l r (GateResult doL doR o) = fromJust $ foldr f Nothing [o, tm l doL, tm r doR] where
  fromJust = \case
    Nothing -> error "foldGateResult: no results"
    Just x -> x
  tm b s = if s then Just b else Nothing
  f :: Maybe g -> Maybe g -> Maybe g
  f a b = case (a,b) of
    (Nothing, Nothing) -> Nothing
    (Just _, Nothing) -> a
    (Nothing, Just _) -> b
    (Just a', Just b') -> pure . superEE $ EitherPF a' b'

superStep :: forall a f. (Base a ~ f, BasicBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> GateResult a) -> (f a -> a) -> (f a -> a) -> f a -> a
superStep gateResult step handleOther =
  \case
    BasicFW (LeftSF (SuperEE (EitherPF a b))) -> mergeShallow (step . embedB . LeftSF $ a) (step . embedB . LeftSF $ b)
    BasicFW (RightSF (SuperEE (EitherPF a b))) -> mergeShallow (step . embedB . RightSF $ a) (step . embedB . RightSF $ b)
    BasicFW (SetEnvSF (SuperEE (EitherPF a b))) -> mergeShallow (step . embedB . SetEnvSF $ a) (step . embedB . SetEnvSF $ b)
  {-
    GateSwitch l r x@(SuperEE _) -> case foldr f Nothing [noBranch res, tm l $ leftBranch res, tm r $ rightBranch res] of
      Nothing -> error "superStep gateswich should have at least one result"
      Just res' -> res'
      where
      res = gateResult l r x
      tm b s = if s then Just b else Nothing
      f :: Maybe a -> Maybe a -> Maybe a
      f a b = case (a,b) of
        (Nothing, Nothing) -> Nothing
        (Just _, Nothing) -> a
        (Nothing, Just _) -> b
        (Just a', Just b') -> pure . superEE $ EitherPF a' b'
-}
    GateSwitch l r x@(SuperEE _) -> (\dx -> debugTrace ("superStep gateSwitch\n" <> prettyPrint dx) dx) . foldGateResult l r $ gateResult x
    (FillFunction (SuperEE (EitherPF sca scb)) e) -> mergeShallow
      (step . embedB . SetEnvSF . basicEE $ PairSF sca e)
      (step . embedB . SetEnvSF . basicEE $ PairSF scb e)
    -- stuck values
    x@(SuperFW (EitherPF _ _)) -> embed x
    x -> handleOther x

superUnsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, SuperBase f, UnsizedBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> GateResult a) -> (f a -> a) -> (f a -> a) -> f a -> a
superUnsizedStep gateResult step handleOther =
  \case
    BasicFW (LeftSF (SuperEE (EitherPF a b))) -> mergeShallow (step . embedB . LeftSF $ a) (step . embedB . LeftSF $ b)
    BasicFW (RightSF (SuperEE (EitherPF a b))) -> mergeShallow (step . embedB . RightSF $ a) (step . embedB . RightSF $ b)
    BasicFW (SetEnvSF (SuperEE (EitherPF a b))) -> mergeShallow (step . embedB . SetEnvSF $ a) (step . embedB . SetEnvSF $ b)
    GateSwitch l r x@(SuperEE _) -> case foldr f Nothing [noBranch res, tm l $ leftBranch res, tm r $ rightBranch res] of
      Nothing -> error "superStep gateswich should have at least one result"
      Just res' -> if null (unSizedRecursion srx)
        then res'
        else unsizedEE $ SizeStageF srx res'
      where
      (srx, nx) = extractSizeStages x
      res = gateResult nx
      tm b s = if s then Just b else Nothing
      f :: Maybe a -> Maybe a -> Maybe a
      f a b = case (a,b) of
        (Nothing, Nothing) -> Nothing
        (Just _, Nothing) -> a
        (Nothing, Just _) -> b
        (Just a', Just b') -> pure . superEE $ EitherPF a' b'
      extractSizeStages = cata $ \case
        UnsizedFW (SizeStageF sr (srb, x)) -> (sr <> srb, x)
        x -> embed <$> sequence x
    (FillFunction (SuperEE (EitherPF sca scb)) e) -> mergeShallow
      (step . embedB . SetEnvSF . basicEE $ PairSF sca e)
      (step . embedB . SetEnvSF . basicEE $ PairSF scb e)
    -- stuck values
    x@(SuperFW (EitherPF _ _)) -> embed x
    x -> handleOther x

superStepM :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (a -> GateResult a) -> (f a -> m a) -> (f a -> m a) -> f a -> m a
superStepM gateResult step handleOther x = f x where
  pbStep bf = step . embedB . bf
  -- f :: f a -> m a
  f = \case
    BasicFW (LeftSF (SuperEE (EitherPF a b))) -> mergeShallow <$> pbStep LeftSF a <*> pbStep LeftSF b
    BasicFW (RightSF (SuperEE (EitherPF a b))) -> mergeShallow <$> pbStep RightSF a <*> pbStep RightSF b
    BasicFW (SetEnvSF (SuperEE (EitherPF a b))) -> mergeShallow <$> pbStep SetEnvSF a <*> pbStep SetEnvSF b
    GateSwitch l r x@(SuperEE _) -> case foldr f Nothing [noBranch res, tm l $ leftBranch res, tm r $ rightBranch res] of
      Nothing -> error "superStepM gateswich should have at least one result"
      Just res' -> pure res'
      where
      res = gateResult x
      tm b s = if s then Just b else Nothing
      f :: Maybe a -> Maybe a -> Maybe a
      f a b = case (a,b) of
        (Nothing, Nothing) -> Nothing
        (Just _, Nothing) -> a
        (Nothing, Just _) -> b
        (Just a', Just b') -> pure . superEE $ EitherPF a' b'
    FillFunction (SuperEE (EitherPF sca scb)) e -> mergeShallow
       <$> (pbStep SetEnvSF . basicEE $ PairSF sca e)
       <*> (pbStep SetEnvSF . basicEE $ PairSF scb e)
    -- stuck values
    x@(SuperFW (EitherPF _ _)) -> pure $ embed x

    _ -> handleOther x

superAbortStep :: (Base g ~ f, Traversable f, BasicBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g)
  => (f g -> g) -> (f g -> g) -> f g -> g
superAbortStep step handleOther x = f x where
  pbStep bf = step . project . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF a b)) ->
      mergeShallow (pbStep (fillFunction (abortEE AbortF)) a) (pbStep (fillFunction (abortEE AbortF)) b)
    _ -> handleOther x

superAbortStepM :: (Base g ~ f, Traversable f, BasicBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, Monad m)
  => (f g -> m g) -> (f g -> m g) -> f g -> m g
superAbortStepM step handleOther x = f x where
  pbStep bf = step . project . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF a b)) ->
      liftM2 mergeShallow (pbStep (fillFunction (abortEE AbortF)) a) (pbStep (fillFunction (abortEE AbortF)) b)
    _ -> handleOther x

indexedAbortStep :: (Base a ~ f, Traversable f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedAbortStep handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF n)) -> abortEE $ AbortedF AbortAny
  x -> handleOther x

indexedAbortStepM :: (Base a ~ f, Traversable f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedAbortStepM handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF n)) -> pure . abortEE $ AbortedF AbortAny
  x -> handleOther x

indexedSuperStep :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedSuperStep handleOther = \case
  GateSwitch l r (IndexedEE (IVarF _)) -> superEE $ EitherPF l r
  x -> handleOther x

indexedSuperStepM :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedSuperStepM handleOther = \case
  GateSwitch l r (IndexedEE (IVarF _)) -> pure . superEE $ EitherPF l r

  x -> handleOther x

fuzzyStepM :: (Base a ~ f, Traversable f, BasicBase f, FuzzyBase f, Recursive a, Corecursive a, Show a, PrettyPrintable a, Monad m) => (a -> a -> a)
  -> (f (m a) -> m a) -> (f (m a) -> m a) -> f (m a) -> m a
fuzzyStepM merge step handleOther x = sequence x >>= f where
  liftStep x = step . fmap pure . embedB . x
  f = \case
    BasicFW (LeftSF s@(FuzzyEE SomeInputF)) -> pure s
    BasicFW (LeftSF (FuzzyEE (MaybePairF l _))) -> pure l
    BasicFW (RightSF s@(FuzzyEE SomeInputF)) -> pure s
    BasicFW (RightSF (FuzzyEE (MaybePairF _ r))) -> pure r
    GateSwitch l r (FuzzyEE _) -> debugTrace ("fuzzyStepM merging...\n" <> prettyPrint l <> "\n------------\n" <> prettyPrint r) pure $ merge l r
    FillFunction (FuzzyEE (FunctionListF l)) e -> debugTrace ("fuzzyStepM operating over list: " <> show l) $ do
      rl <- mapM (liftStep SetEnvSF . basicEE . flip PairSF e) l
      case rl of
        (x:xs) -> pure $ foldl' merge x xs
        _ -> error "superStepM fill functionlist, unexpected empty list"
    -- stuck values
    x@(FuzzyFW _) -> pure $ embed x
    _ -> handleOther x

abortStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> a
    FillFunction a@(AbortEE (AbortedF _)) _ -> a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> deferB abortInd . basicEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> abortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> Zero
        BasicFW (PairSF a b) -> Pair a b
        _                    -> Zero -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> embed x
    x@(AbortFW AbortF) -> embed x
    x -> handleOther x

abortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
abortStepM handleOther x = f x where
  f = \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> pure a
    FillFunction a@(AbortEE (AbortedF _)) _ -> pure a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> pure . deferB abortInd . basicEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> pure . abortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> Zero
        BasicFW (PairSF a b) -> Pair a b
        _                    -> Zero -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> pure $ embed x
    x@(AbortFW AbortF) -> pure $ embed x
    _ -> handleOther x

newtype SizedRecursion = SizedRecursion { unSizedRecursion :: Map UnsizedRecursionToken (Maybe Int)}
  deriving (Eq, Ord, Show, Generic)

instance Semigroup SizedRecursion where
  (<>) (SizedRecursion a) (SizedRecursion b) = SizedRecursion $ Map.unionWith (liftM2 max) a b where

instance Monoid SizedRecursion where
  mempty = SizedRecursion Map.empty

instance PrettyPrintable1 ((,) SizedRecursion) where
  showP1 (_,x) = showP x

instance Validity SizedRecursion where
  validate = trivialValidation

data StrictAccum a x = StrictAccum
  { getAccum :: !a
  , getX :: x
  }
  deriving Functor

instance Monoid a => Applicative (StrictAccum a) where
  pure = StrictAccum mempty
  StrictAccum u f <*> StrictAccum v x = StrictAccum (u <> v) $ f x
  liftA2 f (StrictAccum u x) (StrictAccum v y) = StrictAccum (u <> v) $ f x y

instance Monoid a => Monad (StrictAccum a) where
  StrictAccum u x >>= f = case f x of StrictAccum v y -> StrictAccum (u <> v) y

instance PrettyPrintable1 (StrictAccum SizedRecursion) where
  showP1 (StrictAccum _ x) = showP x

-- list of defer indexes for functions generated during eval. Need to be unique (grammar under defer n should always be the same)
[twiddleInd, unsizedStepMEInd, unsizedStepMTInd, unsizedStepMa, unsizedStepMrfa, unsizedStepMrfb, unsizedStepMw, removeRefinementWrappersTC, abortInd]
  = take 9 [-1, -2 ..]

deferB :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
deferB n = stuckEE . DeferSF (toEnum n)

lamB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
lamB n x = pairB (deferB n x) envB

twiddleB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
twiddleB = deferB twiddleInd $ pairB (leftB (rightB envB)) (pairB (leftB envB) (rightB (rightB envB)))

appB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
appB c i = setEnvB (setEnvB (pairB twiddleB (pairB i c)))

unsizedTestIndexed :: (Base g ~ f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive g, Corecursive g)
  => Set Integer -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestIndexed zeroes handleOther ri = \case
  iv@(IndexedEE (IVarF n)) -> debugTrace ("evalRecursionTest ivar " <> show n) $ if isUnbounded zeroes n
    then debugTrace ("evalRecursion punted to abort on " <> show n) abortEE . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
    else iv
  x -> handleOther ri x

unsizedTestSuper :: (Base g ~ f, SuperBase f, Recursive g, Corecursive g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestSuper reTest handleOther ri = \case
  SuperEE (EitherPF a b) -> superEE $ EitherPF (reTest a) (reTest b)
  x -> handleOther ri x

unsizedTestDeferred :: (Base g ~ f, DeferredEvalBase f, Recursive g, Corecursive g)
  => (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestDeferred handleOther ri = \case
  x@(DeferredEE (BarrierF _)) -> x
  x -> handleOther ri x

unsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f
                           , Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => Int -> (UnsizedRecursionToken -> (a -> a) -> a -> a)
  -> (f a -> a) -> (f a -> a) -> f a -> a
unsizedStep maxSize recursionTest fullStep handleOther =
  let combineSizes :: SizedRecursion -> a -> a
      combineSizes sm = \case
        UnsizedEE (SizeStageF smb x) -> unsizedEE $ SizeStageF (smb <> sm) x
        x -> unsizedEE $ SizeStageF sm x
  in \case
    UnsizedFW (SizingWrapperF tok (BasicEE (PairSF d (BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF))))))))))
      -> case tp of
            BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
              let nt = pairB (stuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
                  trb = pairB b (pairB r (pairB nt zeroB))
                  argOne = leftB envB
                  argTwo = leftB (rightB envB)
                  argThree = leftB (rightB (rightB envB))
                  argFour = leftB (rightB (rightB (rightB envB)))
                  argFive = leftB (rightB (rightB (rightB (rightB envB))))
                  iteB i t e = fillFunction (fillFunction (gateB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t)) i) envB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!
                  abrt = lamB unsizedStepMa . abortEE . AbortedF $ AbortRecursion
                  rf n = lamB unsizedStepMrfb (lamB unsizedStepMrfa (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure n)
                                                                     $ iteB (appB argFive argOne)
                                                                         (appB (appB argFour argTwo) argOne)
                                                                         (appB argThree argOne)))
                  -- rf' n = appB (rf n) (rf' (n + 1))
                  rf' n = if n > maxSize
                    -- then error "reached recursion limit"
                    then abrt
                    else appB (rf n) (rf' (n + 1))
              in pairB (deferB unsizedStepMw $ rf' 1) trb
    UnsizedFW (RecursionTestF ri x) ->
      let test = \case
            z@(BasicEE ZeroSF) -> z
            p@(BasicEE (PairSF _ _)) -> p
            a@(AbortEE (AbortedF _)) -> a
            s@(UnsizedEE (SizeStageF sm x)) -> unsizedEE . SizeStageF sm $ test x
            x -> recursionTest ri test x
      in test x
    BasicFW (LeftSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedB $ LeftSF x
    BasicFW (RightSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedB $ RightSF x
    BasicFW (SetEnvSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedB $ SetEnvSF x
    FillFunction (UnsizedEE (SizeStageF sm x)) e -> combineSizes sm . fullStep . project $ fillFunction x e
    GateSwitch l r (UnsizedEE (SizeStageF sm x)) -> combineSizes sm . fullStep . project $ gateSwitch l r x
    -- stuck value
    ss@(UnsizedFW (SizeStageF _ _)) -> embed ss
    t@(UnsizedFW (RecursionTestF _ _)) -> embed t
    x -> handleOther x

indexedInputStep :: (Base a ~ f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep zeroes handleOther =
  let res n = if Set.member n zeroes then zeroB else indexedEE $ IVarF n
  in \case
  BasicFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  BasicFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  BasicFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  BasicFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
  IndexedFW (IVarF n) -> res n
  -- stuck values
  i@(IndexedFW _) -> embed i

  x -> handleOther x

indexedInputStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedInputStepM handleOther x = f x where
  f = \case
    BasicFW (LeftSF (IndexedEE (IVarF n))) -> pure . indexedEE . IVarF $ n * 2 + 1
    BasicFW (RightSF (IndexedEE (IVarF n))) -> pure . indexedEE . IVarF $ n * 2 + 2
    BasicFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    BasicFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    BasicFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    GateSwitch _ _ (IndexedEE AnyF) -> pure $ indexedEE AnyF
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

indexedInputIgnoreSwitchStepM :: (Base a ~ f, Traversable f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedInputIgnoreSwitchStepM handleOther x = f x where
  f = \case
    GateSwitch _ _ (IndexedEE (IVarF _)) -> pure $ indexedEE AnyF
    _ -> handleOther x

indexSwitchSuperSplitStep :: (Base a ~ f, BasicBase f, IndexedInputBase f, SuperBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
indexSwitchSuperSplitStep handleOther = \case
  GateSwitch l r (IndexedEE AnyF) -> superEE $ EitherPF l r

  x -> handleOther x

deferredEvalStep :: (Base a ~ f, Traversable f, BasicBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep handleOther = \case
    -- combine
    BasicFW (LeftSF (DeferredEE (BarrierF (DeferredEE (ManyLefts n x))))) -> deferredEE . BarrierF . deferredEE $ ManyLefts (n + 1) x
    BasicFW (RightSF (DeferredEE (BarrierF (DeferredEE (ManyRights n x))))) -> deferredEE . BarrierF . deferredEE $ ManyRights (n + 1) x
    BasicFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyLefts 1 x
    BasicFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyRights 1 x
    BasicFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ fillFunction c e
    GateSwitch l r (DeferredEE (BarrierF s)) -> deferredEE . BarrierF $ gateSwitch l r s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

deferredEvalStep' :: (Base a ~ f, Traversable f, BasicBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep' handleOther = \case
    BasicFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ LeftSF x
    BasicFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ RightSF x
    BasicFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ fillFunction c e
    GateSwitch l r (DeferredEE (BarrierF s)) -> deferredEE . BarrierF $ gateSwitch l r s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

abortDeferredStep :: (Base a ~ f, BasicBase f, AbortBase f, DeferredEvalBase f, Recursive a, Corecursive a)
  => (f a -> a) -> f a -> a
abortDeferredStep handleOther = \case
  FillFunction a@(AbortEE AbortF) (DeferredEE (BarrierF e)) -> deferredEE . BarrierF $ fillFunction a e

  x -> handleOther x

-- is a variable limited in value or unbounded?
isUnbounded :: Set Integer -> Integer -> Bool
isUnbounded s n = f s where
  f s'
    | null s' = True
    | Set.member n s' = False
    | otherwise = (f . Set.map (flip div 2 . pred)) $ Set.filter (>= n) s'

extractZeroes :: InputSizingExpr -> Set Integer
extractZeroes = cleanup . f Nothing where
  f expected = f' expected . project
  f' :: Maybe Bool -> InputSizingExprF InputSizingExpr -> Maybe (StrictAccum (Set Integer) InputSizingExpr)
  f' expected = \case
    z@(BasicFW ZeroSF) -> case expected of
      Just True -> Nothing
      _ -> pure . pure $ embed z
    p@(BasicFW (PairSF _ _)) -> case expected of
      Just False -> Nothing
      _ -> pure . pure $ embed p
    IndexedFW (IVarF n) -> case expected of
      Just False -> Just (StrictAccum (Set.singleton n) $ basicEE ZeroSF)
      Just True -> Just (StrictAccum Set.empty $ pairB zeroB zeroB)
      _ -> Just (StrictAccum Set.empty zeroB)
    FillFunction (AbortEE AbortF) i -> f (Just False) i
    GateSwitch l r s ->
      let nl = f expected l
          nr = f expected r
          pf = \case
            Just (StrictAccum s _) -> s
            _ -> Set.empty
      -- in debugTrace ("extractZeroes gate switch " <> show expected <> " " <> show (pf nl, pf nr) <> "\n" <> prettyPrint s) $ case (nl, nr) of
      in case (nl, nr) of
        (Nothing, Nothing) -> Nothing
        (Just (StrictAccum sta x), Just (StrictAccum stb _)) -> case f Nothing s of
          Nothing -> Nothing
          Just (StrictAccum st _) -> pure $ StrictAccum (st <> Set.intersection sta stb) x
        (Just (StrictAccum sta x), _) -> case f (Just False) s of
          Nothing -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
        (_, Just (StrictAccum sta x)) -> case f (Just True) s of
          Nothing -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
    _ -> Nothing
  cleanup = \case
    Just (StrictAccum s _) -> s
    _ -> Set.empty

findInputLimitStepM :: (InputSizingExprF InputSizingExpr -> StrictAccum (Set Integer) InputSizingExpr)
  -> InputSizingExprF InputSizingExpr -> StrictAccum (Set Integer) InputSizingExpr
findInputLimitStepM handleOther x = f x where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let performTC = setEnvB $ pairB (abortEE AbortF) (appB tc c)
          wrapDefer = \case
            g@(GateSwitch _ _ (IndexedEE _)) -> deferredEE . BarrierF $ embed g
            x -> error $ "findInputLimitStepM eval unexpected:\n" <> prettyPrint x
          evalStep = basicStep (stuckStep (abortStep (deferredEvalStep (abortDeferredStep (indexedInputStep Set.empty wrapDefer)))))
          stripBarrier = \case
            DeferredFW (BarrierF x) -> x
            x -> embed x
          s = extractZeroes . cata stripBarrier . (\x -> debugTrace ("findInputLimitStepM tc test is:\n" <> prettyPrint x) x) . transformNoDefer evalStep $ performTC
      in StrictAccum s c
    _ -> handleOther x

data VoidF f
  deriving (Functor, Foldable, Traversable)

instance Eq1 VoidF where
  liftEq test a b = undefined

instance Show1 VoidF where
  liftShowsPrec showsPrec showList prec x = undefined

data SuperPositionF f
  = EitherPF !f !f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 SuperPositionF where
  liftEq test a b = case (a,b) of
    (EitherPF a b, EitherPF c d) -> test a c && test b d
    _                            -> False

instance Show1 SuperPositionF where
  liftShowsPrec showsPrec showList prec = \case
    EitherPF a b -> shows "EitherPF (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"

data FuzzyInputF f
  = MaybePairF f f
  | SomeInputF
  | FunctionListF [f]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 FuzzyInputF where
  liftEq test a b = case (a,b) of
    (SomeInputF, SomeInputF) -> True
    (MaybePairF a b, MaybePairF c d) -> test a c && test b d
    (FunctionListF x, FunctionListF y) -> length x == length y && and (zipWith test x y)
    _ -> False

instance Show1 FuzzyInputF where
  liftShowsPrec showsPrec showList prec = \case
    SomeInputF -> shows "SomeInputF"
    MaybePairF a b -> shows "MaybePairF (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
    FunctionListF x -> shows "FunctionListF " . showList x

-- TODO we can simplify abort semantics to (defer env), and then could do gate x (abort [message] x) for conditional abort
data AbortableF f
  = AbortF
  | AbortedF IExpr
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 AbortableF  where
  liftEq test a b = case (a,b) of
    (AbortF, AbortF)                  -> True
    (AbortedF a, AbortedF b) | a == b -> True
    _                                 -> False

instance Show1 AbortableF where
  liftShowsPrec showsPrec showList prec = \case
    AbortF     -> shows "AbortF"
    AbortedF x -> shows "(AbortedF " . shows x . shows ")"

class ShallowEq a where
  shallowEq :: a -> a -> Bool
class ShallowEq1 f where
  shallowEq1 :: f a -> f b -> Bool
instance ShallowEq1 PartExprF where
  shallowEq1 a b = case (a,b) of
    (ZeroSF, ZeroSF) -> True
    _ -> False
instance ShallowEq1 StuckF where
  shallowEq1 a b = case (a,b) of
    (DeferSF fida _, DeferSF fidb _) -> fida == fidb
    _ -> False
instance ShallowEq1 AbortableF where
  shallowEq1 a b = case (a,b) of
    (AbortedF a', AbortedF b') -> a' == b'
    (AbortF, AbortF) -> True
    _ -> False

data UnsizedRecursionF f
  = RecursionTestF UnsizedRecursionToken f
  | UnsizedStubF UnsizedRecursionToken f
  | SizingWrapperF UnsizedRecursionToken f
  | SizeStageF SizedRecursion f
  | RefinementWrapperF LocTag f f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    _                                          -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec showList prec x = case x of
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec 0 x . shows ")"
    SizeStageF sm x -> shows "SizeStageF " . shows sm
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
    EitherPF a b -> indentWithTwoChildren' "%" (showP a) (showP b)

instance PrettyPrintable1 FuzzyInputF where
  showP1 = \case
    SomeInputF -> pure "A"
    MaybePairF a b -> indentWithTwoChildren' "%" (showP a) (showP b)
    FunctionListF l -> indentWithChildren' "^" $ fmap showP l

instance PrettyPrintable1 AbortableF where
  showP1 = \case
    AbortF      -> pure "!"
    AbortedF am -> pure $ "(aborted - " <> convertAbortMessage am <> ")"

instance PrettyPrintable1 UnsizedRecursionF where
  showP1 = \case
    RecursionTestF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("T(" <> show ind <> ")") $ showP x
    SizingWrapperF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("&(" <> show ind <> ")") $ showP x
    UnsizedStubF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("#" <> show ind) $ showP x
    SizeStageF _ x -> indentWithOneChild' "^" $ showP x
    RefinementWrapperF l tc x -> indentWithTwoChildren' (":" <> show l) (showP tc) (showP x)

instance PrettyPrintable1 VoidF where
  showP1 _ = error "VoidF should never be inhabited, so should not be PrettyPrintable1"

data IndexedInputF f
  = IVarF Integer
  | AnyF
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 IndexedInputF where
  liftEq test a b = case (a, b) of
    (IVarF x, IVarF y) -> x == y
    (AnyF, AnyF) -> True
    _ -> False

instance Show1 IndexedInputF where
  liftShowsPrec showsPrec showList prec x = case x of
    IVarF n -> shows $ "IVarF " <> show n
    AnyF -> shows "IgnoreThis"

instance PrettyPrintable1 IndexedInputF where
  showP1 = \case
    IVarF n -> pure $ "I" <> show n
    AnyF -> pure "-"

data DeferredEvalF f
  = BarrierF f
  | ManyLefts Integer f
  | ManyRights Integer f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 DeferredEvalF where
  liftEq test a b = case (a, b) of
    (BarrierF x, BarrierF y) -> test x y
    (ManyLefts na va, ManyLefts nb vb) -> na == nb && test va vb
    (ManyRights na va, ManyRights nb vb) -> na == nb && test va vb
    _ -> False

instance Show1 DeferredEvalF where
  liftShowsPrec showsPrec showList prec x = case x of
    BarrierF x -> shows "BarrierF (" . showsPrec 0 x . shows ")"
    ManyLefts n x -> shows ("ManyLefts " <> show n) . shows " (" . showsPrec 0 x . shows ")"
    ManyRights n x -> shows ("ManyRights " <> show n) . shows " (" . showsPrec 0 x . shows ")"

instance PrettyPrintable1 DeferredEvalF where
  showP1 = \case
    BarrierF x -> indentWithOneChild' "|" $ showP x
    ManyLefts n x -> indentWithOneChild' ("L" <> show n) $ showP x
    ManyRights n x -> indentWithOneChild' ("R" <> show n) $ showP x

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

instance (Functor f, PrettyPrintable1 f) => PrettyPrintable (Fix f) where
  showP = showP1 . project

data StuckExprF f
  = StuckExprB (PartExprF f)
  | StuckExprS (StuckF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase StuckExprF where
  embedB = StuckExprB
  extractB = \case
    StuckExprB x -> Just x
    _            -> Nothing
instance StuckBase StuckExprF where
  embedS = StuckExprS
  extractS = \case
    StuckExprS x -> Just x
    _            -> Nothing
instance PrettyPrintable1 StuckExprF where
  showP1 = \case
    StuckExprB x -> showP1 x
    StuckExprS x -> showP1 x

type StuckExpr = Fix StuckExprF

data DeferredExprF f
  = DeferredExprB (PartExprF f)
  | DeferredExprS (StuckF f)
  | DeferredExprD (DeferredEvalF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase DeferredExprF where
  embedB = DeferredExprB
  extractB = \case
    DeferredExprB x -> Just x
    _ -> Nothing
instance StuckBase DeferredExprF where
  embedS = DeferredExprS
  extractS = \case
    DeferredExprS x -> Just x
    _ -> Nothing
instance DeferredEvalBase DeferredExprF where
  embedD = DeferredExprD
  extractD = \case
    DeferredExprD x -> Just x
    _ -> Nothing
instance PrettyPrintable1 DeferredExprF where
  showP1 = \case
    DeferredExprB x -> showP1 x
    DeferredExprS x -> showP1 x
    DeferredExprD x -> showP1 x

type DeferredExpr = Fix DeferredExprF

data UnsizedExprF f
  = UnsizedExprB (PartExprF f)
  | UnsizedExprS (StuckF f)
  | UnsizedExprP (SuperPositionF f)
--  | UnsizedExprZ (FuzzyInputF f)
  | UnsizedExprA (AbortableF f)
  | UnsizedExprU (UnsizedRecursionF f)
  | UnsizedExprI (IndexedInputF f)
  deriving (Functor, Foldable, Traversable, Generic)
instance BasicBase UnsizedExprF where
  embedB = UnsizedExprB
  extractB = \case
    UnsizedExprB x -> Just x
    _              -> Nothing
instance StuckBase UnsizedExprF where
  embedS = UnsizedExprS
  extractS = \case
    UnsizedExprS x -> Just x
    _ -> Nothing
instance Show1 UnsizedExprF where
  liftShowsPrec showsPrec showList prec = \case
    UnsizedExprB x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprS x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprP x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprA x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprU x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprI x -> liftShowsPrec showsPrec showList prec x
instance SuperBase UnsizedExprF where
  embedP = UnsizedExprP
  extractP = \case
    UnsizedExprP x -> Just x
    _              -> Nothing
{-
instance FuzzyBase UnsizedExprF where
  embedF = UnsizedExprZ
  extractF = \case
    UnsizedExprZ x -> Just x
    _ -> Nothing
-}
instance AbortBase UnsizedExprF where
  embedA = UnsizedExprA
  extractA = \case
    UnsizedExprA x -> Just x
    _              -> Nothing
instance IndexedInputBase UnsizedExprF where
  embedI = UnsizedExprI
  extractI = \case
    UnsizedExprI x -> Just x
    _              -> Nothing
instance UnsizedBase UnsizedExprF where
  embedU = UnsizedExprU
  extractU = \case
    UnsizedExprU x -> Just x
    _              -> Nothing
instance Eq1 UnsizedExprF where
  liftEq test a b = case (a,b) of
    (UnsizedExprB x, UnsizedExprB y) -> liftEq test x y
    (UnsizedExprS x, UnsizedExprS y) -> liftEq test x y
    (UnsizedExprP x, UnsizedExprP y) -> liftEq test x y
--    (UnsizedExprZ x, UnsizedExprZ y) -> liftEq test x y
    (UnsizedExprA x, UnsizedExprA y) -> liftEq test x y
    (UnsizedExprU x, UnsizedExprU y) -> liftEq test x y
    (UnsizedExprI x, UnsizedExprI y) -> liftEq test x y
    _                                -> False
instance ShallowEq1 UnsizedExprF where
  shallowEq1 a b = case (a,b) of
    (UnsizedExprB x, UnsizedExprB y) -> shallowEq1 x y
    (UnsizedExprS x, UnsizedExprS y) -> shallowEq1 x y
    (UnsizedExprA x, UnsizedExprA y) -> shallowEq1 x y
    _ -> False

instance PrettyPrintable1 UnsizedExprF where
  showP1 = \case
    UnsizedExprB x -> showP1 x
    UnsizedExprS x -> showP1 x
    UnsizedExprP x -> showP1 x
--    UnsizedExprZ x -> showP1 x
    UnsizedExprA x -> showP1 x
    UnsizedExprU x -> showP1 x
    UnsizedExprI x -> showP1 x

type UnsizedExpr = Fix UnsizedExprF

data SuperExprF f
  = SuperExprB (PartExprF f)
  | SuperExprS (StuckF f)
  | SuperExprA (AbortableF f)
  | SuperExprP (SuperPositionF f)
  | SuperExprI (IndexedInputF f)
--  | SuperExprZ (FuzzyInputF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase SuperExprF where
  embedB = SuperExprB
  extractB = \case
    SuperExprB x -> Just x
    _            -> Nothing
instance StuckBase SuperExprF where
  embedS = SuperExprS
  extractS = \case
    SuperExprS x -> Just x
    _            -> Nothing
instance AbortBase SuperExprF where
  embedA = SuperExprA
  extractA = \case
    SuperExprA x -> Just x
    _            -> Nothing
instance SuperBase SuperExprF where
  embedP = SuperExprP
  extractP = \case
    SuperExprP x -> Just x
    _            -> Nothing
instance IndexedInputBase SuperExprF where
  embedI = SuperExprI
  extractI = \case
    SuperExprI x -> Just x
    _            -> Nothing
{-
instance FuzzyBase SuperExprF where
  embedF = SuperExprZ
  extractF = \case
    SuperExprZ x -> Just x
    _ -> Nothing
-}
instance Eq1 SuperExprF where
  liftEq test a b = case (a,b) of
    (SuperExprB x, SuperExprB y) -> liftEq test x y
    (SuperExprS x, SuperExprS y) -> liftEq test x y
    (SuperExprA x, SuperExprA y) -> liftEq test x y
    (SuperExprP x, SuperExprP y) -> liftEq test x y
    (SuperExprI x, SuperExprI y) -> liftEq test x y
    _                            -> False
instance ShallowEq1 SuperExprF where
  shallowEq1 a b = case (a,b) of
    (SuperExprB x, SuperExprB y) -> shallowEq1 x y
    (SuperExprS x, SuperExprS y) -> shallowEq1 x y
    (SuperExprA x, SuperExprA y) -> shallowEq1 x y
    _                            -> False
--    (SuperExprZ x, SuperExprZ y) -> liftEq test x y
instance PrettyPrintable1 SuperExprF where
  showP1 = \case
    SuperExprB x -> showP1 x
    SuperExprS x -> showP1 x
    SuperExprA x -> showP1 x
    SuperExprP x -> showP1 x
    SuperExprI x -> showP1 x
--    SuperExprZ x -> showP1 x

type SuperExpr = Fix SuperExprF

data AbortExprF f
  = AbortExprB (PartExprF f)
  | AbortExprS (StuckF f)
  | AbortExprA (AbortableF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase AbortExprF where
  embedB = AbortExprB
  extractB = \case
    AbortExprB x -> Just x
    _            -> Nothing
instance StuckBase AbortExprF where
  embedS = AbortExprS
  extractS = \case
    AbortExprS x -> Just x
    _            -> Nothing
instance AbortBase AbortExprF where
  embedA = AbortExprA
  extractA = \case
    AbortExprA x -> Just x
    _            -> Nothing
instance Eq1 AbortExprF where
  liftEq test a b = case (a,b) of
    (AbortExprB x, AbortExprB y) -> liftEq test x y
    (AbortExprS x, AbortExprS y) -> liftEq test x y
    (AbortExprA x, AbortExprA y) -> liftEq test x y
    _                            -> False
instance PrettyPrintable1 AbortExprF where
  showP1 = \case
    AbortExprB x -> showP1 x
    AbortExprS x -> showP1 x
    AbortExprA x -> showP1 x

type AbortExpr = Fix AbortExprF

data InputSizingExprF f
  = InputSizingB (PartExprF f)
  | InputSizingS (StuckF f)
  | InputSizingA (AbortableF f)
  | InputSizingU (UnsizedRecursionF f)
  | InputSizingD (DeferredEvalF f)
  | InputSizingI (IndexedInputF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase InputSizingExprF where
  embedB = InputSizingB
  extractB = \case
    InputSizingB x -> Just x
    _            -> Nothing
instance StuckBase InputSizingExprF where
  embedS = InputSizingS
  extractS = \case
    InputSizingS x -> Just x
    _            -> Nothing
instance AbortBase InputSizingExprF where
  embedA = InputSizingA
  extractA = \case
    InputSizingA x -> Just x
    _            -> Nothing
instance UnsizedBase InputSizingExprF where
  embedU = InputSizingU
  extractU = \case
    InputSizingU x -> Just x
    _ -> Nothing
instance DeferredEvalBase InputSizingExprF where
  embedD = InputSizingD
  extractD = \case
    InputSizingD x -> Just x
    _ -> Nothing
instance IndexedInputBase InputSizingExprF where
  embedI = InputSizingI
  extractI = \case
    InputSizingI x -> Just x
    _ -> Nothing
instance Eq1 InputSizingExprF where
  liftEq test a b = case (a,b) of
    (InputSizingB x, InputSizingB y) -> liftEq test x y
    (InputSizingS x, InputSizingS y) -> liftEq test x y
    (InputSizingA x, InputSizingA y) -> liftEq test x y
    (InputSizingU x, InputSizingU y) -> liftEq test x y
    (InputSizingD x, InputSizingD y) -> liftEq test x y
    (InputSizingI x, InputSizingI y) -> liftEq test x y
    _ -> False
instance Show1 InputSizingExprF where
  liftShowsPrec showsPrec showList prec = \case
    InputSizingB x -> liftShowsPrec showsPrec showList prec x
    InputSizingS x -> liftShowsPrec showsPrec showList prec x
    InputSizingA x -> liftShowsPrec showsPrec showList prec x
    InputSizingU x -> liftShowsPrec showsPrec showList prec x
    InputSizingD x -> liftShowsPrec showsPrec showList prec x
    InputSizingI x -> liftShowsPrec showsPrec showList prec x
instance PrettyPrintable1 InputSizingExprF where
  showP1 = \case
    InputSizingB x -> showP1 x
    InputSizingS x -> showP1 x
    InputSizingA x -> showP1 x
    InputSizingU x -> showP1 x
    InputSizingD x -> showP1 x
    InputSizingI x -> showP1 x
type InputSizingExpr = Fix InputSizingExprF

instance PrettyPrintable Char where
  showP = pure . (:[])

convertBasic :: (BasicBase g, BasicBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertBasic convertOther = \case
  BasicFW x -> basicEE x
  x -> convertOther x
convertStuck :: (StuckBase g, StuckBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertStuck convertOther = \case
  StuckFW x -> stuckEE x
  x -> convertOther x
convertSuper :: (SuperBase g, SuperBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertSuper convertOther = \case
  SuperFW x -> superEE x
  x -> convertOther x
convertFuzzy :: (FuzzyBase g, FuzzyBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertFuzzy convertOther = \case
  FuzzyFW x -> fuzzyEE x
  x -> convertOther x
convertAbort :: (AbortBase g, AbortBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertAbort convertOther = \case
  AbortFW x -> abortEE x
  x -> convertOther x
convertUnsized :: (UnsizedBase g, UnsizedBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertUnsized convertOther = \case
  UnsizedFW x -> unsizedEE x
  x -> convertOther x
convertIndexed :: (IndexedInputBase g, IndexedInputBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertIndexed convertOther = \case
  IndexedFW x -> indexedEE x
  x -> convertOther x
convertDeferred :: (DeferredEvalBase g, DeferredEvalBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertDeferred convertOther = \case
  DeferredFW x -> deferredEE x
  x -> convertOther x

unsized2abortExpr :: UnsizedExpr -> AbortExpr
unsized2abortExpr = cata (convertBasic (convertStuck (convertAbort unexpected))) where
  unexpected x = error $ "unsized2abortExpr unexpected unsized bit: " <> prettyPrint (fmap (const ' ') x)

term3ToUnsizedExpr :: Int -> Term3 -> UnsizedExpr
term3ToUnsizedExpr maxSize (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      f = \case
        ZeroFrag -> basicEE ZeroSF
        PairFrag a b -> basicEE $ PairSF (f a) (f b)
        EnvFrag -> basicEE EnvSF
        SetEnvFrag x -> basicEE . SetEnvSF $ f x
        DeferFrag ind -> stuckEE . DeferSF (toEnum $ fromEnum ind) . f . forget . unFragExprUR $ fragLookup ind
        AbortFrag -> abortEE AbortF
        GateFrag l r -> basicEE $ GateSF (f l) (f r)
        LeftFrag x -> basicEE . LeftSF $ f x
        RightFrag x -> basicEE . RightSF $ f x
        TraceFrag -> basicEE EnvSF
        AuxFrag (SizingWrapper tok (FragExprUR x)) -> unsizedEE . SizingWrapperF tok . f $ forget x
        AuxFrag (NestedSetEnvs t) -> unsizedEE . UnsizedStubF t . embed $ embedB EnvSF
        AuxFrag (CheckingWrapper loc (FragExprUR tc) (FragExprUR c)) -> unsizedEE $ RefinementWrapperF loc (f $ forget tc) (f $ forget c)
  in f . forget . unFragExprUR $ rootFrag termMap

-- get simple input limits derived from refinements
-- returns a set of guaranteed Zeros, where the Integer is the encoded path from root of intput
getInputLimits :: UnsizedExpr -> Set Integer
getInputLimits = getAccum . transformNoDeferM evalStep . capMain (indexedEE $ IVarF 0) . convertIS where
  convertU = \case
    UnsizedFW (SizingWrapperF _ _) -> indexedEE AnyF
    UnsizedFW (UnsizedStubF _ _) -> indexedEE AnyF
    UnsizedFW (RecursionTestF _ x) -> x
    UnsizedFW rw@(RefinementWrapperF _ _ _) -> unsizedEE rw
    x -> error $ "getInputLimits convert, unhandled:\n" <> prettyPrint x
  convertIS :: UnsizedExpr -> InputSizingExpr
  convertIS = cata $ convertBasic (convertStuck (convertAbort convertU))
  unexpectedI x = error $ "getInputLimits eval, unexpected:\n" <> prettyPrint x
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM (indexedInputIgnoreSwitchStepM (findInputLimitStepM unexpectedI)))))

data SizedResult = AbortedSR | UnsizableSR UnsizedRecursionToken
  deriving (Eq, Ord, Show)

instance Semigroup SizedResult where
  (<>) a b = case (a,b) of
    (u@(UnsizableSR _), _) -> u
    (_, u@(UnsizableSR _)) -> u
    _                      -> a

newtype MonoidList a = MonoidList { unMonoidList :: [a] }

instance Semigroup a => Semigroup (MonoidList a) where
  (<>) (MonoidList a) (MonoidList b) = MonoidList $ zipWith (<>) a b

instance Semigroup a => Monoid (MonoidList a) where
  mempty = MonoidList []

capMain :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
capMain cap = \case  -- make sure main functions are fully applied with Any data
  BasicEE (PairSF d@(StuckEE (DeferSF _ _)) _) -> basicEE . SetEnvSF . basicEE . PairSF d $ cap
  x -> x

isClosure :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> Bool
isClosure = \case
  BasicEE (PairSF (StuckEE (DeferSF _ _)) _) -> True
  _                                          -> False

sizeTerm :: Int -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
sizeTerm maxSize x = tidyUp . foldAborted . transformNoDefer evalStep $ peTerm where
  failConvert x = error $ "sizeTerm convert, unhandled:\n" <> prettyPrint x
  zeros = (\x -> debugTrace ("sizeTerm zeros are " <> show x) x) $ getInputLimits x
  convertForPartial :: UnsizedExpr -> InputSizingExpr
  convertForPartial = cata $ convertBasic (convertStuck (convertAbort (convertUnsized (convertIndexed failConvert))))
  convertFromPartial :: InputSizingExpr -> UnsizedExpr
  convertFromPartial = cata $ convertBasic (convertStuck (convertAbort (convertUnsized (convertIndexed failConvert))))
  cm = (\x -> debugTrace ("capped main term\n" <> prettyPrint x) x) . removeRefinementWrappers . capMain (indexedEE $ IVarF 0) $ convertForPartial x
  tidyUp =  \case
    (Just (UnsizableSR i), sm) -> Left i
    (_, SizedRecursion sm) -> let sized = debugTrace ("sizes are: " <> show sm) setSizes sm peTerm
                              in pure . clean $ if isClosure x
                                                then uncap sized
                                                else sized
      where uncap = \case
              BasicEE (SetEnvSF (BasicEE (PairSF d _))) -> basicEE $ PairSF d (basicEE ZeroSF)
              z -> error ("sizeTerm tidyUp trying to uncap something that isn't a main function: " <> show z)
  clean :: UnsizedExpr -> AbortExpr
  clean = cata (convertBasic (convertStuck (convertAbort failConvert)))
  convertPartialError x = error ("convertPartialSizing unhandled " <> prettyPrint x)
  tracePartialSizes = id
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW sw@(SizingWrapperF tok sx) -> sx
    UnsizedFW us@(UnsizedStubF tok _) -> tracePartialSizes $ case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("sizeTerm setting size: " <> show (tok, n)) iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _      ->  basicEE . SetEnvSF $ basicEE EnvSF
    x -> embed x
  setSomeSizes :: Map UnsizedRecursionToken (Maybe Int) -> InputSizingExpr -> InputSizingExpr
  setSomeSizes sizeMap = cata $ \case
    UnsizedFW sw@(SizingWrapperF tok sx) -> case Map.lookup tok sizeMap of
      Just (Just _) -> sx
      _ -> embed $ embedU sw
    UnsizedFW us@(UnsizedStubF tok _) -> tracePartialSizes $ case Map.lookup tok sizeMap of
      Just (Just n) -> iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _      -> embed $ embedU us
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF AbortRecursion) -> (Just . UnsizableSR $ toEnum (-2), mempty)
      AbortFW (AbortedF AbortAny) -> (Just . UnsizableSR $ toEnum (-1), mempty)
      AbortFW (AbortedF (AbortUnsizeable t)) -> (Just . UnsizableSR . toEnum . g2i $ t, mempty)
      UnsizedFW (SizeStageF sm x) -> (Nothing, sm) <> x
      x                                 -> Data.Foldable.fold x
  nextPartialSizing (SizedRecursion sm, expr) = debugTrace ("partialSizes setting " <> show sm) $
    if not (null sm)
    then let nexpr = setSomeSizes sm expr in (evalPartialUnsized zeros nexpr, nexpr)
    else (evalPartialUnsized zeros expr, expr)
  hasSizes (SizedRecursion sm, _) = not . null $ Map.filter (not . null) sm
  peTerm = convertFromPartial . snd . head . dropWhile hasSizes . tail
    $ iterate nextPartialSizing (SizedRecursion Map.empty, cm)
  -- peTerm = convertFromPartial cm -- in case debugging is needed
  unhandledMerge x y = error ("sizeTerm unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("sizeTerm unhandled gate input: " <> show x)
  gateResult = debugTrace "gateResult" gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> (UnsizedExpr -> UnsizedExpr) -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri reTest = debugTrace "unsizedTest" unsizedTestIndexed zeros (unsizedTestSuper reTest (\_ x -> error ("sizeTerm unsizedTest unhandled " <> prettyPrint x))) ri
  evalStep = debugTrace "s" basicStep (stuckStep (abortStep (indexedAbortStep (indexedInputStep zeros (indexedSuperStep (superUnsizedStep gateResult evalStep (superAbortStep evalStep (unsizedStep maxSize unsizedTest evalStep unhandledError))))))))
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)

removeRefinementWrappers :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g) => g -> g
removeRefinementWrappers = cata f where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (leftB envB) (rightB envB)
          performTC = deferB removeRefinementWrappersTC . setEnvB $ pairB (setEnvB $ pairB (abortEE AbortF) innerTC) (rightB envB)
      in setEnvB $ pairB performTC (pairB tc c)
    x -> embed x

convertToF :: (Base g ~ f, BasicBase f, StuckBase f, Traversable f, Corecursive g) => IExpr -> g
convertToF = flip State.evalState (toEnum 0) . anaM' f where
  f = \case
    Zero     -> pure $ embedB ZeroSF
    Pair a b -> pure . embedB $ PairSF a b
    Env      -> pure $ embedB EnvSF
    SetEnv x -> pure . embedB $ SetEnvSF x
    Defer x  -> embedS <$> (DeferSF <$> nextVar <*> pure x)
    Gate l r -> pure . embedB $ GateSF l r
    PLeft x  -> pure . embedB $ LeftSF x
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

instance TelomareLike DeferredExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

evalBU :: IExpr -> IExpr
evalBU = toIExpr . ebu . fromTelomare where
  toIExpr = unwrapMaybe . toTelomare
  unwrapMaybe = \case
    Just x -> x
    Nothing -> error "evalBU: could not convert back to IExpr"
  ebu :: StuckExpr -> StuckExpr
  ebu = transformNoDefer (basicStep (stuckStep undefined)) . (\x -> debugTrace ("evalBU starting expr:\n" <> prettyPrint x) x)

evalBU' :: IExpr -> IO IExpr
evalBU' = pure . evalBU

term4toAbortExpr :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Corecursive g) => Term4 -> g
term4toAbortExpr (Term4 termMap') =
  let termMap = forget <$> termMap'
      convertFrag' = embed . convertFrag
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
    dl = (DummyLoc :<)
    pv = pure . dl
    findAborted = cata $ \case
      AbortFW (AbortedF e) -> Just e
      x                    -> asum x
    convert = \case
      BasicFW ZeroSF        -> pv ZeroFragF
      BasicFW (PairSF a b)  -> dl <$> (PairFragF <$> a <*> b)
      BasicFW EnvSF         -> pv EnvFragF
      BasicFW (SetEnvSF x)  -> dl . SetEnvFragF <$> x
      StuckFW (DeferSF _ x) -> deferF x
      AbortFW AbortF        -> pv AbortFragF
      BasicFW (GateSF l r)  -> dl <$> (GateFragF <$> l <*> r)
      BasicFW (LeftSF x)    -> dl . LeftFragF <$> x
      BasicFW (RightSF x)   -> dl . RightFragF <$> x
      z                     -> error "abortExprToTerm4 unexpected thing "
  in case findAborted x of
    Just e -> Left e
    _      -> pure . Term4 . buildFragMap . cata convert $ x

evalA :: (Maybe IExpr -> Maybe IExpr -> Maybe IExpr) -> Maybe IExpr -> Term4 -> Maybe IExpr
evalA combine base t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: SuperExprF SuperExpr -> SuperExpr
                      aStep = basicStep (stuckStep (indexedInputStep Set.empty (indexSwitchSuperSplitStep (superStep aGate aStep (abortStep unhandledError)))))
                      aGate = gateBasicResult (gateAbortResult (gateSuperResult aGate unhandledError))
                      eval' :: SuperExpr -> SuperExpr
                      eval' = transformNoDefer aStep
                  in eval' . capMain (indexedEE $ IVarF 0) $ term4toAbortExpr t
      getAborted = \case
        AbortFW (AbortedF e) -> Just e
        -- SuperFW (EitherPF a b) -> combine a b
        x                    -> foldr (<|>) Nothing x
  in flip combine base . cata getAborted $ runResult

evalPartial :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => g -> g
evalPartial = cata removeBarriers . transformNoDefer step where
  step = deferStep (basicStep (stuckStep (deferredEvalStep' wrapUnknownStep)))
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    BasicFW EnvSF -> embedD $ BarrierF envB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> seq x $ embed x -- does seq have any performance consequence here?
  wrapUnknownStep = deferredEE . BarrierF . embed

evalPartialUnsized :: Set Integer -> InputSizingExpr -> SizedRecursion
evalPartialUnsized zeroes = cata gatherLimits . transformNoDefer step where
  unsizedTest ri reTest = unsizedTestIndexed zeroes (unsizedTestDeferred (\_ x -> error ("evalPartialUnsized unsizedTest unhandled:\n" <> prettyPrint x))) ri
  step = deferStep (basicStep (stuckStep (deferredEvalStep' (indexedInputStep zeroes (abortStep (abortDeferredStep (unsizedStep 255 unsizedTest step wrapUnknownStep)))))))
  -- dof id =  debugTrace ("doing function " <> show id)
  dof _ =  id
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> dof id deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    BasicFW EnvSF -> embedD $ BarrierF envB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> embed x
  -- wrapUnknownStep = deferredEE . BarrierF . embed . (\x -> debugTrace ("unknown dump:\n" <> prettyPrint x) x)
  wrapUnknownStep = deferredEE . BarrierF . embed
  gatherLimits = \case
    UnsizedFW (RecursionTestF ri x) -> SizedRecursion $ Map.singleton ri Nothing
    UnsizedFW (SizeStageF sm x) -> sm <> x
    x -> Data.Foldable.fold x

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

data TypeAssociation = TypeAssociation Int PartialType
  deriving (Eq, Ord, Show)

type AnnotateState = ExceptT TypeCheckError (State (PartialType, Set TypeAssociation, Int))

makeAssociations :: PartialType -> PartialType -> Either TypeCheckError (Set TypeAssociation)
makeAssociations ta tb = case (ta, tb) of
  (x, y) | x == y -> pure mempty
  (AnyType, _) -> pure mempty
  (_, AnyType) -> pure mempty
  (TypeVariable _ i, _) -> pure . Set.singleton $ TypeAssociation i tb
  (_, TypeVariable _ i) -> pure . Set.singleton $ TypeAssociation i ta
  (ArrTypeP a b, ArrTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, PairTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, ZeroTypeP) -> Set.union <$> makeAssociations a ZeroTypeP <*> makeAssociations b ZeroTypeP
  (ZeroTypeP, PairTypeP a b) -> Set.union <$> makeAssociations a ZeroTypeP <*> makeAssociations b ZeroTypeP
  _ -> Left $ InconsistentTypes ta tb

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = liftEither (makeAssociations a b) >>= \set -> State.modify (changeState set) where
  changeState set (curVar, oldSet, v) = (curVar, oldSet <> set, v)

newPartialType :: AnnotateState PartialType
newPartialType = do
  (env, typeMap, v) <- State.get
  State.put (TypeVariable DummyLoc v, typeMap, v + 1)
  pure $ TypeVariable DummyLoc v

withNewEnv :: AnnotateState a -> AnnotateState (PartialType, a)
withNewEnv action = do
  (env, typeMap, v) <- State.get
  State.put (TypeVariable DummyLoc v, typeMap, v + 1)
  result <- action
  State.modify $ \(_, typeMap, v) -> (env, typeMap, v)
  pure (TypeVariable DummyLoc v, result)

class Annotatable a where
  anno :: a -> AnnotateState PartialType

class Annotatable1 f where
  liftAnno :: (a -> AnnotateState PartialType) -> f a -> AnnotateState PartialType

-- >>> 4 + 5
-- 9

instance Annotatable1 PartExprF where
  liftAnno anno = \case
     ZeroSF -> pure ZeroTypeP
     PairSF a b -> PairTypeP <$> anno a <*> anno b
     EnvSF -> State.gets (\(t, _, _) -> t)
     SetEnvSF x -> do
       xt <- anno x
       it <- newPartialType
       ot <- newPartialType
       associateVar (PairTypeP (ArrTypeP it ot) it) xt
       pure ot
     GateSF l r -> do
       lt <- anno l
       rt <- anno l
       associateVar lt rt
       pure $ ArrTypeP ZeroTypeP lt
     LeftSF x -> do
       xt <- anno x
       la <- newPartialType
       associateVar (PairTypeP la AnyType) xt
       pure la
     RightSF x -> do
       xt <- anno x
       ra <- newPartialType
       associateVar (PairTypeP AnyType ra) xt
       pure ra

instance Annotatable1 StuckF where
  liftAnno anno = \case
    DeferSF ind x -> do
      (it, ot) <- withNewEnv $ anno x
      pure $ ArrTypeP it ot

instance Annotatable1 SuperPositionF where
  liftAnno anno = \case
    EitherPF a b -> do
      at <- anno a
      bt <- anno b
      associateVar at bt
      pure at

instance Annotatable1 AbortableF where
  liftAnno anno = \case
    AbortF -> do
      it <- newPartialType
      pure $ ArrTypeP ZeroTypeP (ArrTypeP it it)
    AbortedF _ -> newPartialType

instance Annotatable1 UnsizedRecursionF where
  liftAnno anno = \case
    RecursionTestF _ x -> do
      xt <- anno x
      associateVar xt ZeroTypeP
      pure xt
    SizingWrapperF _ x -> anno x -- not bothering on checking for pair structure for now
    SizeStageF _ x -> anno x
    UnsizedStubF _ x -> anno x -- not bothering on checking internal structure (is it even possible?)
    RefinementWrapperF _ c x -> anno x -- not bothering on checking c

instance Annotatable1 IndexedInputF where
  liftAnno anno = \case
    AnyF -> pure ZeroTypeP
    IVarF _ -> pure ZeroTypeP

instance Annotatable1 UnsizedExprF where
  liftAnno anno = \case
    UnsizedExprB x -> liftAnno anno x
    UnsizedExprS x -> liftAnno anno x
    UnsizedExprP x -> liftAnno anno x
    UnsizedExprA x -> liftAnno anno x
    UnsizedExprU x -> liftAnno anno x
    UnsizedExprI x -> liftAnno anno x

instance (Functor f, Annotatable1 f) => Annotatable (Fix f) where
  anno = liftAnno anno . project

instance Annotatable (Cofree g PartialType) where
  anno (a :< _) = pure a

anno1 :: (Annotatable1 f, Annotatable g) => f g -> AnnotateState PartialType
anno1 = liftAnno anno

fullyResolve :: (Int -> Maybe PartialType) -> PartialType -> PartialType
fullyResolve resolve = convert where
    convert = transform endo
    endo = \case
      TypeVariable anno i -> case resolve i of
        Nothing -> TypeVariable anno i
        Just t  -> convert t
      x -> x

buildTypeMap :: Set TypeAssociation -> Either TypeCheckError (Map Int PartialType)
buildTypeMap assocSet =
  let multiMap = Map.fromListWith DList.append . fmap (\(TypeAssociation i t) -> (i, DList.singleton t))
        $ Set.toList assocSet
      getKeys = \case
        TypeVariable _ i -> DList.singleton i
        ArrTypeP a b     -> getKeys a <> getKeys b
        PairTypeP a b    -> getKeys a <> getKeys b
        _                -> mempty
      isRecursiveType resolvedSet k = case (Set.member k resolvedSet, Map.lookup k multiMap) of
        (True, _) -> Just k
        (_, Nothing) -> Nothing
        (_, Just t) -> foldr (\nk r -> isRecursiveType (Set.insert k resolvedSet) nk <|> r) Nothing
          $ foldMap getKeys t
      debugShowMap tm = debugTrace (concatMap (\(k, v) -> show k <> ": " <> show v <> "\n") $ Map.toAscList tm)
      buildMap assoc typeMap = case Set.minView assoc of
        Nothing -> debugShowMap typeMap $ pure typeMap
        Just (TypeAssociation i t, newAssoc) -> case Map.lookup i typeMap of
          Nothing -> buildMap newAssoc $ Map.insert i t typeMap
          Just t2 -> makeAssociations t t2 >>= (\assoc2 -> buildMap (newAssoc <> assoc2) typeMap)
  -- if any variables result in lookup cycles, fail with RecursiveType
  in case foldr (\t r -> isRecursiveType Set.empty t <|> r) Nothing (Map.keys multiMap) of
    Just k  -> Left $ RecursiveType k
    Nothing -> debugTrace (show multiMap) $ buildMap assocSet mempty

partiallyAnnotate :: (Base g ~ f, Annotatable1 f, Annotatable g)
  => g -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
partiallyAnnotate term =
  let runner :: State (PartialType, Set TypeAssociation, Int) (Either TypeCheckError PartialType)
      runner = runExceptT $ anno term
      initState = (TypeVariable DummyLoc 0, Set.empty, 0)
      (rt, (_, s, _)) = State.runState runner initState
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap s)

annotateTree :: forall g f. (Base g ~ f, Traversable f, Annotatable1 f, Recursive g, Annotatable g)
  => g -> Either TypeCheckError (Cofree f PartialType)
annotateTree term = do
  (rt, resolver) <- partiallyAnnotate term
  let fResolve = fullyResolve resolver
      ca x = anno1 x >>= \a -> pure (fResolve a :< x)
      f = ca <=< sequence
      initState = (TypeVariable DummyLoc 0, Set.empty, 0)
  flip State.evalState initState . runExceptT $ cata f term

matchType :: PartialType -> PartialType -> Bool
matchType a b = case (a,b) of
  (ZeroTypeP, ZeroTypeP) -> True
  (AnyType, _) -> True
  (_, AnyType) -> True
  (TypeVariable _ _, _) -> True
  (_, TypeVariable _ _) -> True
  (ArrTypeP a b, ArrTypeP c d) -> matchType a c && matchType b d
  (PairTypeP a b, PairTypeP c d) -> matchType a c && matchType b d
  _ -> False

matchTypeHead :: (Annotatable1 f, Annotatable g) => PartialType -> f g -> Bool
matchTypeHead t x =
  let initState = (TypeVariable DummyLoc 0, Set.empty, 0)
  in case State.evalState (runExceptT $ anno1 x) initState of
    Left _ -> False
    Right t' -> matchType t' t

instance Validity a => Validity (PartExprF a)
instance Validity a => Validity (StuckF a)
instance Validity a => Validity (SuperPositionF a)
instance Validity a => Validity (AbortableF a)
instance Validity a => Validity (UnsizedRecursionF a)
instance Validity a => Validity (IndexedInputF a)
instance Validity a => Validity (UnsizedExprF a)
instance Validity (Cofree UnsizedExprF PartialType) where
  validate x = let startVar = succ . getMax $ cata mv x
                   mv (a CofreeT.:< x) = mv' a <> Data.Foldable.fold x
                   mv' = \case
                     TypeVariable _ n -> Max n
                     ArrTypeP a b -> mv' a <> mv' b
                     PairTypeP a b -> mv' a <> mv' b
                     _ -> Max 0
                   initState = (TypeVariable DummyLoc startVar, Set.empty, startVar)
                   etb = \case
                     Right True -> True
                     _ -> False
                   getTypeLevel = flip State.evalState initState . runExceptT . liftAnno anno
                   matchLevel (a CofreeT.:< fx) = All (etb $ matchType a <$> getTypeLevel (fst <$> fx))
                     <> Data.Foldable.fold (snd <$> fx)
               in declare "grammar matches type annotations" . getAll $ para matchLevel x

instance GenValid a => GenValid (PartExprF a) where
instance GenValid FunctionIndex
instance GenValid a => GenValid (StuckF a) where
instance GenValid a => GenValid (SuperPositionF a) where
instance GenValid a => GenValid (AbortableF a) where
instance GenValid UnsizedRecursionToken
instance GenValid SizedRecursion where
instance GenValid a => GenValid (UnsizedRecursionF a) where
instance GenValid a => GenValid (IndexedInputF a) where
instance GenValid a => GenValid (UnsizedExprF a) where

instance GenValid (Cofree UnsizedExprF PartialType) where
  genValid = genValid >>= (sized . genTypedTree Nothing . toPartialType)
  shrinkValid (a :< x) = (a :<) <$> filter (matchTypeHead a) (shrinkValidStructurally x)

genTypedTree :: Maybe PartialType -> PartialType -> Int -> Gen (Cofree UnsizedExprF PartialType)
genTypedTree ti t i = -- TODO generate UnsizedF sections?
  let optionEnv = if ti == Just t
                  then (pure (t :< embedB EnvSF) :)
                  else id
      optionGate = case t of
        ArrTypeP ZeroTypeP to -> ((ta . embedB <$> (GateSF <$> genTypedTree ti to half <*> genTypedTree ti to half)) : )
        _ -> id
      optionAbort = case t of
        ArrTypeP ZeroTypeP (ArrTypeP _ _) -> ((pure . ta $ embedA AbortF) : )
        _ -> id
      ta = (t :<)
      half = div i 2
      setEnvOption = genValid >>= makeSetEnv where
        makeSetEnv ti' = ta . embedB . SetEnvSF <$> genTypedTree ti (PairTypeP (ArrTypeP ti' t) ti') (i - 1)
      leftOption = genValid >>= makeLeft where
        makeLeft ti' = ta . embedB . LeftSF <$> genTypedTree ti (PairTypeP t ti') (i - 1)
      rightOption = genValid >>= makeRight where
        makeRight ti' = ta . embedB . RightSF <$> genTypedTree ti (PairTypeP ti' t) (i - 1)
      eitherOption = ta . embedP <$> (EitherPF <$> genTypedTree ti t half <*> genTypedTree ti t half)
      abortedOption = pure . ta . embedA . AbortedF . AbortUser $ s2g "Arbitrary Test Data"
      addZeroPair = if t == ZeroTypeP
        then ((ta . embedB <$> (PairSF <$> genTypedTree ti ZeroTypeP half <*> genTypedTree ti ZeroTypeP half)) :)
        else id
      addBranches l = if i < 2 then l else leftOption : rightOption : setEnvOption : eitherOption : addZeroPair l
  in oneof . optionEnv . (abortedOption :) . addBranches $ case t of
    PairTypeP tl tr ->
      [ ta . embedB <$> (PairSF <$> genTypedTree ti tl half <*> genTypedTree ti tr half)
      ]
    ArrTypeP ti' to -> optionGate . optionAbort $
      [ ta . embedS . DeferSF (toEnum 0) <$> genTypedTree ti to (i - 1)
      ]
    _ ->
      [ pure . ta $ embedB ZeroSF
      , ta . embedI . IVarF <$> arbitrary
      , pure . ta $ embedI AnyF
      ]

tcAnnotatedProp :: Cofree UnsizedExprF PartialType -> Bool
tcAnnotatedProp exp = validate . pa $ cata f exp where
  pa :: UnsizedExpr -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
  pa = partiallyAnnotate
  f (_ CofreeT.:< x) = embed x
  validate = \case
    Right _ -> True
    _ -> False
