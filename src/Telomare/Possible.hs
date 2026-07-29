{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Telomare.Possible where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Lens.Plated (transform)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Lazy as StateL
import Control.Monad.State.Strict (State, StateT)
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class
import Data.Bifunctor
import Data.Char (chr)
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Fix (Fix (..), hoistFix')
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Kind
import Data.List (nub, nubBy, partition, sortBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
-- import Data.SBV ((.<), (.>))
-- import qualified Data.SBV as SBV
-- import qualified Data.SBV.Control as SBVC
import Control.Comonad.Trans.Cofree (CofreeF, headF)
import Control.Exception (Exception)
import Control.Exception.Base (throw)
import Control.Monad.Reader.Class
import Data.GenValidity
import Data.GenValidity.Map
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Validity (Validity (..), declare, trivialValidation)
import Data.Void
import Debug
import Debug.Trace
import GHC.Generics (Generic)
import PrettyPrint
import Telomare (AbortBase (..), AbortableF (..), AbstractRunTime (..),
                 BasicBase (..), BasicExpr, BasicExprF (..), CompiledExpr,
                 FunctionIndex (..), LocTag (..), PartialType (..),
                 RunTimeError (..), StuckBase (..), StuckExpr, StuckExprF,
                 StuckF (..), TelomareLike (fromTelomare, toTelomare),
                 Term3 (..), Term3F (..),
                 UnsizedRecursionToken (UnsizedRecursionToken), b2i,
                 convertAbort, convertAbortMessage, convertBasic, convertStuck,
                 forget, i2B, indentWithChildren', indentWithOneChild,
                 indentWithOneChild', indentWithTwoChildren,
                 indentWithTwoChildren', pattern AbortAny, pattern AbortEE,
                 pattern AbortFW, pattern AbortRecursion,
                 pattern AbortUnsizeable, pattern AbortUser, pattern AppEE,
                 pattern BasicEE, pattern BasicFW, pattern EnvB,
                 pattern FillFunction, pattern FillFunctionEE, pattern GateB,
                 pattern GateSwitch, pattern LeftB,
                 pattern PairB, pattern PairP, pattern RightB, pattern SetEnvB,
                 pattern StuckEE, pattern StuckFW, pattern ZeroB, s2b, sindent,
                 toPartialType)
import Telomare.PossibleData
-- import Telomare.RunTime (hvmEval)
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Test.QuickCheck (Arbitrary (..), Gen, oneof)
import Test.QuickCheck.Gen (sized)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
-- debugTrace s x = if debug then debugTrace' s x else x
debugTrace s x = if debug then trace s x else x

{-
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
-}

-- testSBV' :: IO Int
-- testSBV' = fromIntegral <$> SBV.runSMT testSBV

anaM' :: (Monad m, Corecursive t, x ~ Base t, Traversable x) => (a -> m (Base t a)) -> a -> m t
anaM' f = c where c = (fmap embed . mapM c) <=< f

basicStep :: (Base g ~ f, BasicBase f, Corecursive g, Recursive g) => (f g -> g) -> f g -> g
basicStep handleOther = \case
  -- stuck values
  x@(BasicFW ZeroSF)                       -> embed x
  x@(BasicFW (PairSF _ _))                 -> embed x
  x                                        -> handleOther x

basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, PrettyPrintable g, Monad m) => (f g -> m g) -> f g -> m g
basicStepM handleOther x = f x where
  f = \case
    -- stuck values
    x@(BasicFW ZeroSF)                       -> pure $ embed x
    x@(BasicFW (PairSF _ _))                 -> pure $ embed x

    _                                        -> handleOther x

transformNoDefer :: (Base g ~ f, StuckBase f, Recursive g) => (f g -> g) -> g -> g
transformNoDefer f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> s
    x                         -> fmap c x

transformNoDeferM :: (Base g ~ f, StuckBase f, Traversable f, Monad m, Recursive g) => (f g -> m g) -> g -> m g
transformNoDeferM f = c where
  c = f <=< (c' . project)
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> pure s
    x                         -> mapM c x

doLeft :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
doLeft = deferB leftGateInd $ LeftB EnvB

doRight :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
doRight = deferB rightGateInd $ RightB EnvB

-- | matches the branch-selector functions a gate evaluates to (doLeft/doRight)
isGateSelector :: (Base g ~ f, StuckBase f, Recursive g) => g -> Bool
isGateSelector x = case project x of
  StuckFW (DeferSF fi _) -> fi == toEnum leftGateInd || fi == toEnum rightGateInd
  _ -> False

stuckStep :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDefer (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db = if False -- fid == toEnum 74
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      -- then debugTrace ("function " <> show fid)
      else id
    replaceEnv = \case
      StuckFW EnvSF -> e'
      x             -> x
  StuckFW (LeftSF z@(BasicEE ZeroSF))      -> z
  StuckFW (LeftSF (BasicEE (PairSF l _)))  -> l
  StuckFW (RightSF z@(BasicEE ZeroSF))     -> z
  StuckFW (RightSF (BasicEE (PairSF _ r))) -> r
  FillFunction GateB ZeroB                 -> doLeft
  FillFunction GateB (PairB _ _)           -> doRight
  -- stuck values
  x@(StuckFW (DeferSF _ _)) -> embed x
  x@(StuckFW GateSF )                 -> embed x
  x -> handleOther x

{-
stuckStepDebug :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStepDebug handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDefer (basicStep (stuckStepDebug handleOther) . replaceEnv) d' where
    interestingIds = []
    e' = project e
    db = if False -- fid == toEnum 74
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      else id
    d' = if fromEnum fid `elem` interestingIds -- if fid == toEnum unsizedStepMw -- unsizedStepMrfa
      then debugTrace ("stuckStep dumping environment for " <> show fid <> "\n"  <> prettyPrint e) d
      else debugTrace ("stuckStep hit " <> show (fromEnum fid)) d
    replaceEnv = \case
      StuckFW EnvSF -> e'
      x             -> x
  -- stuck value
  x@(StuckFW _) -> embed x
  x -> handleOther x
-}

stuckStepM :: (Base a ~ f, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
stuckStepM handleOther x = f x where
  f = \case
    FillFunction (StuckEE (DeferSF fid d)) e -> transformNoDeferM runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = project e
      replaceEnv = \case
        StuckFW EnvSF -> e'
        x             -> x
    StuckFW (LeftSF z@(BasicEE ZeroSF))      -> pure z
    StuckFW (LeftSF (BasicEE (PairSF l _)))  -> pure l
    StuckFW (RightSF z@(BasicEE ZeroSF))     -> pure z
    StuckFW (RightSF (BasicEE (PairSF _ r))) -> pure r
    FillFunction GateB ZeroB                 -> pure doLeft
    FillFunction GateB (PairB _ _)           -> pure doRight
    -- stuck value
    x@(StuckFW (DeferSF _ _)) -> pure $ embed x
    x@(StuckFW GateSF)                 -> pure $ embed x
    _ -> handleOther x

{-
stuckStepDebugM :: forall a f m j. (Base a ~ f, Traversable f, StuckBase f, BasicBase f, AbortBase f, UnsizedBase f, IndexedInputBase f, SuperBase f
                   , ShallowEq1 f, Show a, Eq a, Recursive a, Corecursive a, PrettyPrintable a, GenValidAdj a, Monad m
                   , Gennable a ~ j, GenValid j, Eq j)
  => (f a -> m a) -> f a -> m a
stuckStepDebugM handleOther x = f x where
  interestingIds = [-5, 33, 32, 31, 29]
  f = \case
    ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDeferM runStuck d' where
      runStuck = basicStepM (stuckStepDebugM handleOther) . replaceEnv
      e' = project e
      d' = if fromEnum fid `elem` interestingIds -- if fid == toEnum unsizedStepMw -- unsizedStepMrfa
        then debugTrace ("stuckStepDebugM dumping environment for " <> show fid <> "\n"  <> prettyPrint e) d
        else debugTrace ("stuckStepDebugM hit " <> show (fromEnum fid)) d
      db = id
      replaceEnv = \case
        BasicFW EnvSF -> e'
        x             -> x
    -- stuck value
    x@(StuckFW _) -> pure $ embed x
    _ -> handleOther x
-}

{-
stuckStepWithTrace :: (Base a ~ f, MonadReader s m, s ~ TCallStack a, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> m a) -> f a -> m a
stuckStepWithTrace handleOther = \case
  FillFunction (StuckEE (DeferSF fid d)) e -> local addTrace $ transformNoDeferM runStuck d where
    addTrace = ((fid, e) :)
    runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
    e' = project e
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x             -> x
  -- stuck value
  x@(StuckFW _) -> pure $ embed x
  x -> handleOther x
-}

failAndPrintStack :: (Base a ~ f, MonadReader s m, s ~ TCallStack a, Corecursive a, PrettyPrintable a)
  => f a -> m b
failAndPrintStack x = do
  s <- ask
  error ("could not evaluate\n" <> prettyPrint (embed x) <> concatMap printCall s) where
    printCall (fi, i) = "\n--> from " <> show fi <> " with argument\n" <> prettyPrint i

gateBasicResult :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateBasicResult handleOther = \case
  BasicEE ZeroSF -> GateResult True False Nothing
  BasicEE (PairSF _ _) -> GateResult False True Nothing
  x -> handleOther x

gateSuperResult :: (Base g ~ f, SuperBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> (g -> GateResult g) -> g -> GateResult g
gateSuperResult step handleOther = \case
  SuperEE (EitherPF n a b) -> let GateResult la ra ba = step a
                                  GateResult lb rb bb = step b
                                  co = case (ba, bb) of
                                    (Just ba', Just bb') -> pure . superEE $ EitherPF n ba' bb'
                                    _ -> ba <|> bb
                              in GateResult (la || lb) (ra || rb) co
  x -> handleOther x

gateAbortResult :: (Base g ~ f, AbortBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateAbortResult handleOther = \case
  a@(AbortEE (AbortedF _)) -> GateResult False False $ Just a
  x -> handleOther x

gateIndexedResult :: (Base g ~ f, IndexedInputBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateIndexedResult handleOther = \case
  -- IndexedEE (IVarF n) -> GateResult True False Nothing -- wait, why lb but no rb?
  IndexedEE (IVarF n) -> GateResult True True Nothing
  x -> handleOther x

mergeShallow :: (Base g ~ f, SuperBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g) => Maybe Integer -> g -> g -> g
mergeShallow n a b = if shallowEq1 (project a) (project b)
  then debugTrace ("mergeShallow found same pair\n" <> prettyPrint a <> "\nand\n" <> prettyPrint b) a
  else superEE $ EitherPF n a b

foldGateResult :: forall g f. (Base g ~ f, SuperBase f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Maybe Integer -> GateResult g -> g
foldGateResult n (GateResult doL doR o) =
  let branchPart = case (doL, doR) of
        (True, True) -> pure . superEE $ EitherPF n doLeft doRight
        (True, _)    -> pure doLeft
        (_, True)    -> pure doRight
        _            -> Nothing
  in case (o, branchPart) of
    (Just o', Just bp) -> superEE $ EitherPF Nothing o' bp
    (Just x, _)        -> x
    (_, Just x)        -> x
    _                  -> error "foldGateResult: no results"

superStep :: forall a f. (Base a ~ f, BasicBase f, StuckBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> GateResult a) -> (f a -> a) -> (f a -> a) -> f a -> a
superStep gateResult step handleOther =
  let filterLeft :: Maybe Integer -> f a -> a
      filterLeft n = \case
        SuperFW (EitherPF nt a _) | nt == n -> a
        x -> embed x
      filterRight :: Maybe Integer -> f a -> a
      filterRight n = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
  in \case
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . LeftSF $ a) (step . embedS . LeftSF $ b)
    StuckFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . RightSF $ a) (step . embedS . RightSF $ b)
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . SetEnvSF $ a) (step . embedS . SetEnvSF $ b)
    FillFunction GateB x@(SuperEE (EitherPF n _ _)) -> foldGateResult n $ gateResult x
    FillFunction (SuperEE (EitherPF n sca scb)) e | isGateSelector sca && isGateSelector scb -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE $ PairSF sca e)
      (step . embedS . SetEnvSF . BasicEE $ PairSF scb e)
    (FillFunction (SuperEE (EitherPF n sca scb)) e) -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
      (step . embedS . SetEnvSF . BasicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> embed x
    x -> handleOther x

superUnsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, UnsizedBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> GateResult a) -> (f a -> a) -> (f a -> a) -> f a -> a
superUnsizedStep gateResult step handleOther =
  let filterLeft :: Maybe Integer -> f a -> a
      filterLeft n = \case
        SuperFW (EitherPF nt a _) | nt == n -> error "TODO make like superStepM" a
        x -> embed x
      filterRight :: Maybe Integer -> f a -> a
      filterRight n = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
  in \case
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . LeftSF $ a) (step . embedS . LeftSF $ b)
    StuckFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . RightSF $ a) (step . embedS . RightSF $ b)
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . SetEnvSF $ a) (step . embedS . SetEnvSF $ b)
    FillFunction GateB x@(SuperEE (EitherPF n _ _)) -> wrapSS $ foldGateResult n res where
      wrapSS = if null (unSizedRecursion srx) then id else unsizedEE . SizeStageF srx
      (srx, nx) = extractSizeStages x
      res = gateResult nx
      extractSizeStages = cata $ \case
        UnsizedFW (SizeStageF sr (srb, x)) -> (sr <> srb, x)
        x -> embed <$> sequence x
    FillFunction (SuperEE (EitherPF n sca scb)) e | isGateSelector sca && isGateSelector scb -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE $ PairSF sca e)
      (step . embedS . SetEnvSF . BasicEE $ PairSF scb e)
    (FillFunction (SuperEE (EitherPF n sca scb)) e) -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
      (step . embedS . SetEnvSF . BasicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> embed x
    x -> handleOther x

data SizingSettings = SizingSettings
  { maxSizingSize :: Int
  , doCap         :: Bool
  } deriving (Eq, Ord, Show)

superStepM :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (a -> GateResult a) -> (f a -> m a) -> (f a -> m a) -> f a -> m a
superStepM gateResult step handleOther x = f x where
  pbStep bf = step . embedS . bf
  filterLeft :: Maybe Integer -> f a -> a
  filterLeft n = \case
        s@(SuperFW (EitherPF nt a _)) | (decendant <$> nt <*> n) == Just True -> a
        x -> embed x
  filterRight :: Maybe Integer -> f a -> a
  filterRight n = \case
        s@(SuperFW (EitherPF nt _ b)) | (decendant <$> n <*> nt) == Just True -> b
        x -> embed x
  f = \case
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) ->  mergeShallow n <$> pbStep LeftSF a <*> pbStep LeftSF b
    StuckFW (RightSF (SuperEE (EitherPF n a b))) ->  mergeShallow n <$> pbStep RightSF a <*> pbStep RightSF b
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep SetEnvSF a <*> pbStep SetEnvSF b
    FillFunction GateB x@(SuperEE (EitherPF n _ _)) -> pure . foldGateResult n $ gateResult x
    -- when applying gate selectors, e holds the gate branches; filtering them by the scrutinee's
    -- tag collapses same-tagged input superpositions and under-approximates recursion sizes
    FillFunction (SuperEE (EitherPF n sca scb)) e | isGateSelector sca && isGateSelector scb ->
      mergeShallow n
       <$> (pbStep SetEnvSF . BasicEE $ PairSF sca e)
       <*> (pbStep SetEnvSF . BasicEE $ PairSF scb e)
    FillFunction (SuperEE (EitherPF n sca scb)) e ->
      let fl = if null n then id else cata (filterLeft n)
          fr = if null n then id else cata (filterRight n)
      in mergeShallow n
       <$> (pbStep SetEnvSF . BasicEE . PairSF sca $ fl e)
       <*> (pbStep SetEnvSF . BasicEE . PairSF scb $ fr e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> pure $ embed x

    _ -> handleOther x

superAbortStep :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g)
  => (f g -> g) -> (f g -> g) -> f g -> g
superAbortStep step handleOther x = f x where
  pbStep bf = step . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF n a b)) ->
      mergeShallow n (pbStep (FillFunction (AbortEE AbortF)) a) (pbStep (FillFunction (AbortEE AbortF)) b)
    _ -> handleOther x

superAbortStepM :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g, Monad m)
  => (f g -> m g) -> (f g -> m g) -> f g -> m g
superAbortStepM step handleOther x = f x where
  pbStep bf = step . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF n a b)) ->
      liftM2 (mergeShallow n) (pbStep (FillFunction (AbortEE AbortF)) a) (pbStep (FillFunction (AbortEE AbortF)) b)
    _ -> handleOther x

indexedAbortStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedAbortStep handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF n)) -> AbortEE $ AbortedF AbortAny
  x -> handleOther x

indexedAbortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedAbortStepM handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF n)) -> pure . AbortEE $ AbortedF AbortAny
  x -> handleOther x

indexedSuperStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedSuperStep handleOther = \case
  FillFunction GateB (IndexedEE (IVarF n)) -> superEE $ EitherPF (pure n) doLeft doRight
  x -> handleOther x

indexedSuperStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedSuperStepM handleOther = \case
  FillFunction GateB (IndexedEE (IVarF n)) -> pure . superEE $ EitherPF (pure n) doLeft doRight

  x -> handleOther x

abortStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, PrettyPrintable a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    StuckFW (LeftSF a@(AbortEE (AbortedF _))) -> a
    StuckFW (RightSF a@(AbortEE (AbortedF _))) -> a
    StuckFW (SetEnvSF a@(AbortEE (AbortedF _))) -> a
    FillFunction a@(AbortEE (AbortedF _)) _ -> a
    FillFunction GateB a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> deferB abortInd . StuckEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> (\x -> debugTrace ("aborted with value: " <> prettyPrint x) x) . AbortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> ZeroB
        BasicFW (PairSF a b) -> PairB a b
        _                    -> ZeroB -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> embed x
    x@(AbortFW AbortF) -> embed x
    x -> handleOther x

abortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
abortStepM handleOther x = f x where
  f = \case
    StuckFW (LeftSF a@(AbortEE (AbortedF _))) -> pure a
    StuckFW (RightSF a@(AbortEE (AbortedF _))) -> pure a
    StuckFW (SetEnvSF a@(AbortEE (AbortedF _))) -> pure a
    FillFunction a@(AbortEE (AbortedF _)) _ -> pure a
    FillFunction GateB a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> pure . deferB abortInd . StuckEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> pure . AbortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> ZeroB
        BasicFW (PairSF a b) -> PairB a b
        _                    -> ZeroB -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> pure $ embed x
    x@(AbortFW AbortF) -> pure $ embed x
    _ -> handleOther x

-- list of defer indexes for functions generated during eval. Need to be unique (grammar under defer n should always be the same)
[twiddleInd, leftGateInd, rightGateInd, unsizedStepMEInd, unsizedStepMTInd, unsizedStepMa, unsizedStepMrfa, unsizedStepMrfb, unsizedStepMw, removeRefinementWrappersTC, abortInd]
  = take 11 [-1, -2 ..]

deferB :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
deferB n = StuckEE . DeferSF (toEnum n)

lamB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
lamB n x = PairB (deferB n x) EnvB

twiddleB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
twiddleB = deferB twiddleInd $ PairB (LeftB (RightB EnvB)) (PairB (LeftB EnvB) (RightB (RightB EnvB)))

appB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
appB c i = SetEnvB (SetEnvB (PairB twiddleB (PairB i c)))

-- only intended for use inside of unsizedStep
iteB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g -> g
iteB i t e = FillFunctionEE (FillFunctionEE (FillFunctionEE GateB i) (PairB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t))) EnvB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!

argOneB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argOneB = LeftB EnvB
argTwoB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argTwoB = LeftB (RightB EnvB)
argThreeB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argThreeB = LeftB (RightB (RightB EnvB))
argFourB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argFourB = LeftB (RightB (RightB (RightB EnvB)))

unsizedTestIndexed :: (Base g ~ f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive g, Corecursive g)
  => Set Integer -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestIndexed zeroes handleOther ri = \case
  iv@(IndexedEE (IVarF n)) -> debugTrace ("evalRecursionTest ivar " <> show n) $ if isUnbounded zeroes n
    then debugTrace ("evalRecursion punted to abort on " <> show n) AbortEE . AbortedF . AbortUnsizeable . i2B . fromEnum $ ri
    else if Set.member n zeroes
    then debugTrace ("unsizedTestIndexed resolved to zero for var " <> show n) ZeroB
    else iv
  x -> handleOther ri x

unsizedTestSuper :: (Base g ~ f, SuperBase f, AbortBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestSuper reTest handleOther ri = \case
  SuperEE (EitherPF n a b) -> let getAU = \case
                                    a@(AbortEE (AbortedF (AbortUnsizeable _))) -> Just a
                                    _ -> Nothing
                                  na = reTest a
                                  nb = reTest b
                                  Just r = getAU na <|> getAU nb <|> (Just . superEE $ EitherPF n na nb)
                              in r
  x -> handleOther ri x

unsizedTestDeferred :: (Base g ~ f, DeferredEvalBase f, Recursive g, Corecursive g)
  => (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestDeferred handleOther ri = \case
  x@(DeferredEE (BarrierF _)) -> x
  x -> handleOther ri x

unsizedTestUnsized :: (Base g ~ f, UnsizedBase f, Recursive g, Corecursive g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestUnsized reTest handleOther ri = \case
  UnsizedEE (SizeStageF sm x) -> unsizedEE . SizeStageF sm $ reTest x
  x -> handleOther ri x

forceSizes :: Int -> UnsizedExpr -> UnsizedExpr
forceSizes n = cata $ \case
  UnsizedFW (UnsizedStubF _ _) -> iterate (StuckEE . SetEnvSF) EnvB !! n
  x -> embed x

unsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f
                           , Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => Int -> (UnsizedRecursionToken -> a -> a)
  -> (f a -> a) -> (f a -> a) -> f a -> a
unsizedStep maxSize recursionTest fullStep handleOther =
  let combineSizes :: SizedRecursion -> a -> a
      combineSizes sm = \case
        UnsizedEE (SizeStageF smb x) -> unsizedEE $ SizeStageF (smb <> sm) x
        x -> unsizedEE $ SizeStageF sm x
  in \case
    UnsizedFW (SizeStepStubF tok n (BasicEE (PairSF _ e))) ->
      PairB (deferB unsizedStepMrfa (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure (n + 1)) $ iteB (appB argFourB argOneB)
                                                (appB (appB argThreeB (unsizedEE $ SizeStepStubF tok (n + 1) EnvB)) argOneB)
                                                (appB argTwoB argOneB))) e
    UnsizedFW (RecursionTestF ri x) -> recursionTest ri x
    StuckFW (LeftSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedS $ LeftSF x
    StuckFW (RightSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedS $ RightSF x
    StuckFW (SetEnvSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedS $ SetEnvSF x
    FillFunction (UnsizedEE (SizeStageF sm x)) e -> combineSizes sm . fullStep $ FillFunction x e
    FillFunction GateB (UnsizedEE (SizeStageF sm x)) -> combineSizes sm . fullStep $ FillFunction GateB x
    -- stuck value
    ss@(UnsizedFW (SizeStageF _ _)) -> embed ss
    t@(UnsizedFW (RecursionTestF _ _)) -> embed t
    x -> handleOther x

unsizedStepM''' :: forall a f t m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a
                                   , Eq a, PrettyPrintable a, m ~ StrictAccum SizedRecursion, MonadTrans t, Applicative (t m))
  => Int -> Set Integer -> (UnsizedRecursionToken -> a -> a) -> (f a -> t m a) -> f a -> t m a
unsizedStepM''' maxSize zeros recursionTest handleOther x = f x where
  argOne = LeftB EnvB
  argTwo = LeftB (RightB EnvB)
  argThree = LeftB (RightB (RightB EnvB))
  argFour = LeftB (RightB (RightB (RightB EnvB)))
  f = \case
    UnsizedFW (UnsizedStubF tok (BasicEE (PairSF _ (BasicEE (PairSF _ (BasicEE (PairSF _ (BasicEE (PairSF _ env))))))))) -> case env of
      BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF)))))) -> case tp of
        BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
          let nt = PairB (StuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
              trb = PairB b (PairB r (PairB nt ZeroB))
              dbti = id
              -- \t r b i ->
              rf = deferB unsizedStepMrfa (iteB (dbti $ appB argFour argOne)
                                          (appB (appB argThree (unsizedEE $ SizeStepStubF tok 1 EnvB)) argOne)
                                          (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure 1) $ appB argTwo argOne))
              result = PairB ZeroB (PairB ZeroB (PairB ZeroB (PairB (PairB rf trb) ZeroB)))
          in pure result
    UnsizedFW (SizeStepStubF tok n _) | n > maxSize -> pure . AbortEE . AbortedF . AbortRecursion . i2B $ fromEnum n
    UnsizedFW (SizeStepStubF tok n e@(BasicEE (PairSF _ es))) ->
      let dbti = id
      in pure $ PairB (deferB unsizedStepMrfa (iteB (dbti $ appB argFour argOne)
                                                (appB (appB argThree (unsizedEE $ SizeStepStubF tok (n + 1) e)) argOne)
                                                (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure (n + 1)) $ appB argTwo argOne))) es
    UnsizedFW (RecursionTestF ri x) -> pure . recursionTest ri $ x
    UnsizedFW (SizeStageF sr x) -> lift . debugTrace ("Hit SizeStage: " <> show sr) $ StrictAccum sr x
    UnsizedFW (TraceF s x) -> pure $ debugTrace ("Hit TraceF: " <> s <> "\n" <> prettyPrint x) x
    _ -> handleOther x

zeroedInputStepM :: (Base a ~ g, Traversable f, IndexedInputBase f, BasicBase g, Recursive a, Corecursive a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
zeroedInputStepM zeros handleOther = f where
  f = \case
    IndexedFW (IVarF n) | Set.member n zeros -> pure $ BasicEE ZeroSF
    x -> handleOther x

indexedInputStep :: (Base a ~ f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep zeroes handleOther =
  let res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  in \case
  StuckFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  StuckFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  StuckFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  StuckFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
  IndexedFW (IVarF n) -> res n
  -- stuck values
  i@(IndexedFW _) -> embed i

  x -> handleOther x

{-
  7 8 9 A B C D E
   3   4   5   6
     1       2
         0
  B (11) : R -> L -> L
  P Z
    P Z
      Z
    Z

  11 % 2 = 1 -- L
  (11 - 1) / 2 = 5
  5 % 2 = 1 -- L
  (5 - 1) / 2 = 2
  2 % 2 = 0 -- R
  (2 - 1) / 2 = 0

-}

indexedInputStep' :: (Base a ~ f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep' zeroes handleOther =
  let res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  in \case
  StuckFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  StuckFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  StuckFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  StuckFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
  IndexedFW (IVarF n) -> res n
  -- stuck values
  i@(IndexedFW _) -> embed i

  x -> handleOther x

indexAbortIfUnboundStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, Show a)
  => Set Integer -> (f a -> a) -> f a -> a
indexAbortIfUnboundStep zeroes handleOther =
  let res s n = case (Set.member n zeroes, isUnbounded zeroes n) of
        (True, _) -> ZeroB
        (_, True) -> AbortEE $ AbortedF AbortAny
        _ -> PairB (indexedEE . IVarF $ n * 2 + 1) (indexedEE . IVarF $ n * 2 + 2)
      leftI = \case
        BasicEE (PairSF l _) -> l
        x -> x
      rightI = \case
        BasicEE (PairSF _ r) -> r
        x -> x
  in \case
  StuckFW (LeftSF (IndexedEE (IVarF n))) -> leftI $ res "left" n
  StuckFW (RightSF (IndexedEE (IVarF n))) -> rightI $ res "right" n
  IndexedFW (IVarF n) -> res "bare" n
  x -> handleOther x

indexedInputStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM zeroes handleOther x = f x where
  res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  f = \case
    StuckFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    StuckFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    StuckFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    FillFunction GateB (IndexedEE AnyF) -> pure $ indexedEE AnyF
    IndexedFW (IVarF n) -> pure $ res n
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

indexedInputStepM' :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM' zeroes handleOther x = f x where
  res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  f = \case
    StuckFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    StuckFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    StuckFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    FillFunction GateB (IndexedEE AnyF) -> pure $ indexedEE AnyF
    IndexedFW (IVarF n) -> pure $ res n
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

indexedInputIgnoreSwitchStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedInputIgnoreSwitchStepM handleOther x = f x where
  f = \case
    FillFunction GateB (IndexedEE (IVarF _)) -> pure $ indexedEE AnyF
    _ -> handleOther x

indexSwitchSuperSplitStep :: (Base a ~ f, BasicBase f, StuckBase f, IndexedInputBase f, SuperBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
indexSwitchSuperSplitStep handleOther = \case
  FillFunction GateB (IndexedEE AnyF) -> superEE $ EitherPF Nothing doLeft doRight

  x -> handleOther x

deferredEvalStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep handleOther = \case
    -- combine
    StuckFW (LeftSF (DeferredEE (BarrierF (DeferredEE (ManyLefts n x))))) -> deferredEE . BarrierF . deferredEE $ ManyLefts (n + 1) x
    StuckFW (RightSF (DeferredEE (BarrierF (DeferredEE (ManyRights n x))))) -> deferredEE . BarrierF . deferredEE $ ManyRights (n + 1) x
    StuckFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyLefts 1 x
    StuckFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyRights 1 x
    StuckFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ FillFunctionEE c e
    FillFunction GateB (DeferredEE (BarrierF s)) -> deferredEE . BarrierF . embed $ FillFunction GateB s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

deferredEvalStep' :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep' handleOther = \case
    StuckFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ LeftSF x
    StuckFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ RightSF x
    StuckFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ FillFunctionEE c e
    FillFunction GateB (DeferredEE (BarrierF s)) -> deferredEE . BarrierF . embed $ FillFunction GateB s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

abortDeferredStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, DeferredEvalBase f, Recursive a, Corecursive a)
  => (f a -> a) -> f a -> a
abortDeferredStep handleOther = \case
  FillFunction a@(AbortEE AbortF) (DeferredEE (BarrierF e)) -> deferredEE . BarrierF $ FillFunctionEE a e

  x -> handleOther x

-- is a variable limited in value or unbounded?
isUnbounded :: Set Integer -> Integer -> Bool
isUnbounded s n = f s where
  f s'
    | null s' = True
    | Set.member n s' = False
    | otherwise = (f . Set.map (flip div 2 . pred)) $ Set.filter (>= n) s'


-- NOTE this considers a node to be its own decendant
decendant :: Integer -> Integer -> Bool
decendant x d = case compare x d of
  GT -> decendant (flip div 2 $ pred x) d
  EQ -> True
  LT -> False

data InputRestrictions
  = InputRestrictions {zeroes :: Set Integer, pairs :: Set Integer}
  deriving Show

instance Semigroup InputRestrictions where
  (<>) (InputRestrictions za pa) (InputRestrictions zb pb) = InputRestrictions (za <> zb) (pa <> pb)
instance Monoid InputRestrictions where
  mempty = InputRestrictions mempty mempty

extractInputRestrictions :: InputSizingExpr -> InputRestrictions
extractInputRestrictions = cleanup . f Nothing where
  f expected = f' expected . project
  irIntersection (InputRestrictions za pa) (InputRestrictions zb pb) = InputRestrictions (za <> zb) (pa <> pb)
  f' :: Maybe Bool -> InputSizingExprF InputSizingExpr -> Maybe (StrictAccum InputRestrictions InputSizingExpr)
  f' expected = \case
    z@(BasicFW ZeroSF) -> case expected of
      Just True -> Nothing
      _         -> pure . pure $ embed z
    p@(BasicFW (PairSF _ _)) -> case expected of
      Just False -> Nothing
      _          -> pure . pure $ embed p
    IndexedFW (IVarF n) -> case expected of
      Just False -> Just (StrictAccum (InputRestrictions (Set.singleton n) mempty) ZeroB)
      Just True  -> Just (StrictAccum (InputRestrictions mempty (Set.singleton n)) $ PairB ZeroB ZeroB)
      _          -> Just (StrictAccum mempty ZeroB) -- is this ok?
    FillFunction (AbortEE AbortF) i -> f (Just False) i
    GateSwitch l r s ->
      let nl = f expected l
          nr = f expected r
          pf = \case
            Just (StrictAccum s _) -> s
            _ -> Set.empty
      in case (nl, nr) of
        (Nothing, Nothing) -> debugTrace "extractZeroes gate nothing" Nothing
        (Just (StrictAccum sta x), Just (StrictAccum stb _)) -> debugTrace "extractZeroes gate both" $ case f Nothing s of
          Nothing -> Nothing
          Just (StrictAccum st _) -> pure $ StrictAccum (st <> irIntersection sta stb) x
        (Just (StrictAccum sta x), _) -> case f (Just False) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
        (_, Just (StrictAccum sta x)) -> case f (Just True) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
    _ -> Nothing
  cleanup = \case
    Just (StrictAccum s _) -> s
    _ -> mempty

zeroToBranch :: (Base a ~ f, BasicBase f, Recursive a, Corecursive a) => Integer -> a
{-
zeroToBranch = ana f where
  f 0 = embedB ZeroSF
  f n = let n' = div (n - 1) 2 in if even n
    then embedB (PairSF n' 0)
    else embedB (PairSF 0 n')
-}
zeroToBranch n = g n id where
  g :: (Base a ~ f, BasicBase f, Recursive a, Corecursive a) => Integer -> (a -> a) -> a
  g 0 f = f ZeroB
  g n f = let g' = g (div (n - 1) 2) in if even n
    then g' (PairB ZeroB . f)
    else g' (flip PairB ZeroB . f)

testB :: UnsizedExpr
testB = zeroToBranch 11

pathToBranch :: Integer -> String
pathToBranch n = g n id where
  g 0 f = f []
  g n f = let g' = g (div (n - 1) 2) in if even n
    then g' (('R' :) . f)
    else g' (('L' :) . f)

-- >>> prettyPrint testB


findInputLimitStepM :: (InputSizingExprF InputSizingExpr -> StrictAccum InputRestrictions InputSizingExpr)
  -> InputSizingExprF InputSizingExpr -> StrictAccum InputRestrictions InputSizingExpr
findInputLimitStepM handleOther x = f x where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let
          performTC = SetEnvB $ PairB (AbortEE AbortF) (appB tc c)
          wrapDefer = \case
            FillFunction GateB i@(IndexedEE _) -> deferredEE . BarrierF . embed $ FillFunction GateB i
            x -> error $ "findInputLimitStepM eval unexpected:\n" <> prettyPrint x
          evalStep = basicStep (stuckStep (abortStep (deferredEvalStep (abortDeferredStep (indexedInputStep' Set.empty wrapDefer)))))
          convertIL :: InputSizingExpr -> UnsizedExpr
          convertIL = validate . cata f where
            f = convertBasic (convertStuck (convertAbort (convertIndexed convertFail)))
            -- convertFail z = Left ("findInputLimitStepM convert failed on unexpected\n" <> prettyPrint z)
            convertFail z = Left "findInputLimitStepM convert failed on something unexpected"
          validate = \case
            Left e -> error e
            Right x -> x
          ev = transformNoDefer evalStep
          stripBarrier = \case
            DeferredFW (BarrierF x) -> x
            x -> embed x
          s = extractInputRestrictions . cata stripBarrier . transformNoDefer evalStep $ performTC
      in StrictAccum s c
    _ -> handleOther x

unsized2abortExpr :: UnsizedExpr -> CompiledExpr
unsized2abortExpr = validate . cata (convertBasic (convertStuck (convertAbort unexpected))) where
  unexpected x = Left $ "unsized2abortExpr unexpected unsized bit: " <> prettyPrint (fmap (const ' ') x)
  validate = \case
    Left e -> error e
    Right x -> x

term3ToUnsizedExpr :: Term3 -> UnsizedExpr
term3ToUnsizedExpr = runIdentity . cata conv where
  conv :: CofreeT.CofreeF Term3F LocTag (Identity UnsizedExpr) -> Identity UnsizedExpr
  conv = convertBasic (convertStuck (convertAbort convertOther))
  convertOther (_ CofreeT.:< g) = case g of
    Term3Unsized urt -> pure . unsizedEE . UnsizedStubF urt $ EnvB
    Term3CheckingWrapper loc tc c -> unsizedEE <$> (RefinementWrapperF loc <$> tc <*> c)
    z -> error "term3ToUnsizedExpr could not convert"

-- get simple input limits derived from refinements
-- returns a set of guaranteed Zeros, where the Integer is the encoded path from root of intput
getInputLimits :: UnsizedExpr -> InputRestrictions
getInputLimits = getAccum . transformNoDeferM evalStep . convertIS where
  convertU = \case
    UnsizedFW (UnsizedStubF _ _) -> pure $ indexedEE AnyF
    UnsizedFW (RecursionTestF _ x) -> x
    UnsizedFW rw@(RefinementWrapperF _ _ _) -> unsizedEE <$> sequence rw
    x -> error $ "getInputLimits convert, unhandled:\n" <> prettyPrint (runIdentity $ sequence x)
  convertIS :: UnsizedExpr -> InputSizingExpr
  convertIS = runIdentity . cata (convertBasic (convertStuck (convertAbort (convertIndexed convertU))))
  unexpectedI x = error $ "getInputLimits eval, unexpected:\n" <> prettyPrint x
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM Set.empty (indexedInputIgnoreSwitchStepM (findInputLimitStepM unexpectedI)))))

capMain :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
capMain i c = appB c i


isClosure :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> Bool
isClosure = \case
  BasicEE (PairSF (StuckEE (DeferSF _ _)) _) -> True
  _                                          -> False

newtype UnexpectedGrammarException = UGException String

instance Show UnexpectedGrammarException where
  show (UGException e) = "UnexpectedGrammarException: " <> e

instance Exception UnexpectedGrammarException

{-
sizeTerm :: Int -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
sizeTerm maxSize x = tidyUp . foldAborted . debugResult . transformNoDefer evalStep $ peTerm where
  failConvert x = error $ "sizeTerm convert, unhandled:\n" <> prettyPrint x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  zeros = zeroes $ getInputLimits x
  debugResult r = debugTrace ("sizeTerm result is\n" <> prettyPrint r) r
  cm = removeRefinementWrappers $ capMain (indexedEE $ IVarF 0) x
  showSizes sm = debugTrace ("sizes are: " <> show sm)
  tidyUp =  \case
    (Just (UnsizableSR i), sm) -> Left i
    (_, SizedRecursion sm) -> let sized = showSizes sm $ setSizes sm peTerm
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
    UnsizedFW us@(UnsizedStubF tok _) -> tracePartialSizes $ case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("sizeTerm setting size: " <> show (tok, n)) iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _      ->  basicEE . SetEnvSF $ basicEE EnvSF
    x -> embed x
  setSomeSizes :: Map UnsizedRecursionToken (Maybe Int) -> InputSizingExpr -> InputSizingExpr
  setSomeSizes sizeMap = cata $ \case
    UnsizedFW us@(UnsizedStubF tok _) -> tracePartialSizes $ case Map.lookup tok sizeMap of
      Just (Just n) -> iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _             -> embed $ embedU us
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion _)) -> (Just . UnsizableSR $ toEnum (-2), mempty)
      AbortFW (AbortedF AbortAny) -> (Just . UnsizableSR $ toEnum (-1), mempty)
      AbortFW (AbortedF (AbortUnsizeable t)) -> (Just . UnsizableSR . toEnum . g2i $ t, mempty)
      UnsizedFW (SizeStageF sm x) -> (Nothing, sm) <> x
      x                                 -> Data.Foldable.fold x
  hasSizes (SizedRecursion sm, _) = not . null $ Map.filter (not . null) sm
  peTerm = cm -- in case debugging is needed
  unhandledMerge x y = error ("sizeTerm unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("sizeTerm unhandled gate input: " <> show x)
  gateResult = debugTrace "gateResult" gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (unsizedTestUnsized (unsizedTest ri) (const id))) ri
  evalStep = basicStep (stuckStep (abortStep (indexedAbortStep (indexedInputStep zeros (indexedSuperStep (superUnsizedStep gateResult evalStep (superAbortStep evalStep (unsizedStep maxSize unsizedTest evalStep unhandledError))))))))
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)
-}

initialInput :: (Base a ~ f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a) => InputRestrictions -> a
initialInput irs = f 0 where
  f n = if any (`decendant` n) $ pairs irs
    then PairB (f $ n * 2 + 1) (f $ n * 2 + 2)
    else indexedEE $ IVarF n

sizeTermM :: SizingSettings -> UnsizedExpr -> Either UnsizedRecursionToken CompiledExpr
sizeTermM sizingSettings x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ mx where
  failConvert x = (>>= Left) $ ("sizeTermM convert, unhandled:\n" <>) .  prettyPrint <$> sequence x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  inputRestrictions = (\x -> debugTrace ("sizeTermM zeros are\n" <> show x) x) $ getInputLimits cm'
  zeros = zeroes inputRestrictions
  convertNakedEnvs = \case
    StuckFW EnvSF -> ZeroB
    x -> embed x
  dtt :: UnsizedExpr -> UnsizedExpr
  dtt t = debugTrace ("sizeTermM initial term is\n" <> prettyPrint t) t
  cm' = dtt $ if doCap sizingSettings
    then capMain (indexedEE $ IVarF 0) x
    else x
  cm = removeRefinementWrappers cm'
  mx = removeRefinementWrappers $ if doCap sizingSettings
    then capMain (initialInput inputRestrictions) x
    else transformNoDefer convertNakedEnvs x
  tidyUp (StrictAccum (SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i) -> debugTrace "sizeTermM hit unsizable" Left i
    _ -> let sized = setSizes sm cm
         in debugTrace "sizeTermM found all sizes" pure . clean $ if doCap sizingSettings
            then uncap sized
            else sized
      where uncap = \case
              AppEE c _ -> c
              z -> error ("sizeTermM tidyUp trying to uncap something that isn't a main function:\n" <> prettyPrint z)
  clean :: UnsizedExpr -> CompiledExpr
  clean = verify . cata (convertBasic (convertStuck (convertAbort failConvert)))
  verify = \case
    Left e -> error e
    Right x -> x
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW us@(UnsizedStubF tok _) -> case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("sizeTermM setting size: " <> show (tok, n)) iterate (StuckEE . SetEnvSF) EnvB !! (n + 1)
      _      -> debugTrace ("no size found for " <> show tok) SetEnvB EnvB
    UnsizedFW (TraceF _ x) -> x
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion i)) -> case b2i i of
        Just i' -> Just . UnsizableSR $ toEnum i'
        _ -> error $ "sizeTermM foldAborted unexpected AbortRecursion value:\n" <> prettyPrint i
      AbortFW (AbortedF AbortAny) -> error "sizeTermM AbortAny hit"
      AbortFW (AbortedF (AbortUnsizeable t)) -> case b2i t of
        Just i' -> Just . UnsizableSR $ toEnum i'
        _ -> error $ "sizeTermM foldAborted unexpected AbortUnsizeable value:\n" <> prettyPrint t
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("sizeTermM unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("sizeTermM unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = (\x -> debugTrace ("unsizedTest evaluated to value of\n" <> prettyPrint x) x) . unsizedTest ri
  unhandledError x = throw $ UGException ("sizeTermM unhandled case\n" <> prettyPrint x)
  evalStep = basicStepM (stuckStepM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' (maxSizingSize sizingSettings) zeros unsizedTest' unhandledError))))))))

{-
evalTrace :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, SuperBase f, UnsizedBase f, Traversable f, ShallowEq1 f
             , Recursive a, Corecursive a, PrettyPrintable a, Show a) => a -> a
evalTrace x = debugTrace ("evalTrace:\n" <> prettyPrint (transformNoDefer evalStepT x)) x where
          unhandledGate x = error ("findInputLimitStepM evalT unhandled gate input: " <> show x)
          gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
          testZ = Set.singleton $ toEnum 127
          evalError z = error $ "findInputLimitStepM evalT unexpected:\n" <> prettyPrint (embed z)
          -- evalStepT = basicStep (stuckStep (abortStep (indexAbortIfUnboundStep testZ (indexedSuperStep (superAbortStep evalStepT (superStep gateResult evalStepT evalError))))))
          evalStepT = basicStep (stuckStep (abortStep (indexedInputStep testZ (indexedSuperStep (superAbortStep evalStepT (superStep gateResult evalStepT (traceRefinement evalStepT evalError)))))))
-}

{-
abortPossibilities :: Int -> UnsizedExpr -> Set IExpr
abortPossibilities maxSize x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ cm where
  sizingSettings = SizingSettings 255 True
  failConvert x = error $ "abortPossibilities convert, unhandled:\n" <> prettyPrint x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  showZeros z = "\nabortPossibilities zeros are: " <> show z <> "\nzeros are:\n" <> concatMap (prettyPrint . forceType . zeroToBranch) z
  inputRestrictions = getInputLimits x
  zeros = zeroes inputRestrictions
  cm = removeRefinementWrappers $ capMain (initialInput inputRestrictions) x
  tidyUp (StrictAccum (SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ foldAborted r
  clean :: UnsizedExpr -> AbortExpr
  clean = cata (convertBasic (convertStuck (convertAbort failConvert)))
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW us@(UnsizedStubF tok _) -> case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("abortPossibilities setting size: " <> show (tok, n)) iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _      ->  basicEE . SetEnvSF $ basicEE EnvSF
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF x) -> Set.singleton x
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("abortPossibilities unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("abortPossibilities unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = unsizedTest ri . (\x -> debugTrace ("unsizedTest value of\n" <> prettyPrint x) x)
  unhandledError x = error ("abortPossibilities unhandled case\n" <> prettyPrint x)
  evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest failAndPrintStack))))))))
-}

getSizesM :: Int -> UnsizedExpr -> Either UnsizedRecursionToken SizedRecursion
getSizesM maxSize x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ cm where
  sizingSettings = SizingSettings 255 True
  failConvert x = error $ "getSizesM convert, unhandled:\n" <> prettyPrint x
  inputRestrictions = getInputLimits x
  zeros = zeroes inputRestrictions
  cm = removeRefinementWrappers $ capMain (initialInput inputRestrictions) x
  tidyUp (StrictAccum sr@(SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i) -> Left i
    _                    -> pure sr
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion _)) -> Just . UnsizableSR $ toEnum (-2)
      AbortFW (AbortedF AbortAny) -> Just . UnsizableSR $ toEnum (-1)
      AbortFW (AbortedF (AbortUnsizeable t)) -> case b2i t of
        Just i' -> Just . UnsizableSR $ toEnum i'
        _ -> error $ "getSizesM foldAborted AbortUnsizeable unexpected value:\n" <> prettyPrint t
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("getSizesM unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("getSizesM unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = unsizedTest ri . (\x -> debugTrace ("getSizesM value of\n" <> prettyPrint x) x)
  unhandledError x = error ("getSizesM unhandled case\n" <> prettyPrint x)
  evalStep = basicStepM (stuckStepM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest' failAndPrintStack))))))))

removeRefinementWrappers :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g) => g -> g
removeRefinementWrappers = cata f where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (LeftB EnvB) (RightB EnvB)
          performTC = deferB removeRefinementWrappersTC . SetEnvB $ PairB (SetEnvB $ PairB (AbortEE AbortF) innerTC) (RightB EnvB)
      in SetEnvB $ PairB performTC (PairB tc c)
    x -> embed x

regularEval :: forall f g. (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, UnsizedBase f
               , Recursive g, Corecursive g, PrettyPrintable g) => g -> g
regularEval = transformNoDefer f . cata ss where
  f = basicStep (stuckStep (abortStep (indexedInputStep Set.empty unhandledError)))
  unhandledError z = error ("regularEval unhandled case\n" <> prettyPrint (embed z))
  ss :: f g -> g
  ss = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (LeftB EnvB) (RightB EnvB)
          performTC = deferB removeRefinementWrappersTC . SetEnvB $ PairB (SetEnvB $ PairB (AbortEE AbortF) innerTC) (RightB EnvB)
      in SetEnvB $ PairB performTC (PairB tc c)
    UnsizedFW (UnsizedStubF _ _) -> iterate SetEnvB EnvB !! 255
    x -> embed x

basicEval :: forall f g. (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g, PrettyPrintable g) => g -> g
basicEval = transformNoDefer f where
  f = basicStep (stuckStep unhandledError)
  unhandledError z = error ("basicEval unhandled case:\n" <> prettyPrint (embed z))

newtype PPOut a = PPOut a
--   deriving Functor

instance {-# OVERLAPPING #-} PrettyPrintable (PPOut CompiledExpr) where
  showP (PPOut x) = f x where
    f = \case
      BasicEE ZeroSF -> pure ""
      BasicEE (PairSF a b) -> liftA2 (<>) (doLet a) (f b)
      z -> indentWithTwoChildren' "#!#" (pure "") (showP z)
    doLet x = case cata lf x of
      Just n -> pure [chr n]
      _      -> indentWithTwoChildren' "#/#" (pure "") (showP x)
    lf = \case
      BasicFW ZeroSF -> Just 0
      BasicFW (PairSF n (Just 0)) -> succ <$> n
      _ -> Nothing

instance AbstractRunTime CompiledExpr where
  eval = checkError . (\x -> debugTrace ("CompiledExpr eval " <> dumpEval x) x) . transformNoDefer step where
    dumpEval = \case
      BasicEE (PairSF o s) -> "output:\n" <> prettyPrint (PPOut o) <> "\nnew state:\n" <> prettyPrint s
      z -> "unexpected eval state:\n" <> prettyPrint z
    step = basicStep (stuckStep (abortStep unhandledError))
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
    findError = \case
      AbortFW (AbortedF e) -> Just e
      x -> asum x
    checkError x = case cata findError x of
      Just e -> Left $ AbortRunTime e
      _      -> pure x

evalStaticCheck :: Bool -> StaticCheckExpr -> Maybe BasicExpr
evalStaticCheck doCap t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: StaticCheckExprF StaticCheckExpr -> StaticCheckExpr
                      aStep = basicStep (stuckStep (abortStep (deferredEvalStep' unhandledError)))
                      eval' :: StaticCheckExpr -> StaticCheckExpr
                      eval' = transformNoDefer aStep
                      inp = deferredEE $ BarrierF EnvB
                      x = (\x' -> debugTrace ("evalA starting expr:\n" <> prettyPrint x') x') $ if doCap then capMain inp t else t
                  in eval' x
      getAborted = \case
        AbortFW (AbortedF e) -> Just e
        DeferredFW (BarrierF _) -> Nothing
        x                    -> foldr (<|>) Nothing x
  in cata getAborted runResult

evalPartial :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => g -> g
evalPartial = cata removeBarriers . transformNoDefer step where
  step = deferStep (basicStep (stuckStep (deferredEvalStep' wrapUnknownStep)))
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    StuckFW EnvSF -> embedD $ BarrierF EnvB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> seq x $ embed x -- does seq have any performance consequence here?
  wrapUnknownStep = deferredEE . BarrierF . embed

evalPartialUnsized :: Set Integer -> InputSizingExpr -> SizedRecursion
evalPartialUnsized zeroes = cata gatherLimits . transformNoDefer step where
  unsizedTest = unsizedTestIndexed zeroes (unsizedTestDeferred (\_ x -> error ("evalPartialUnsized unsizedTest unhandled:\n" <> prettyPrint x)))
  step = deferStep (basicStep (stuckStep (deferredEvalStep' (indexedInputStep zeroes (abortStep (abortDeferredStep (unsizedStep 255 unsizedTest step wrapUnknownStep)))))))
  dof _ =  id
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> dof id deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    StuckFW EnvSF -> embedD $ BarrierF EnvB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> embed x
  wrapUnknownStep = deferredEE . BarrierF . embed
  gatherLimits = \case
    UnsizedFW (RecursionTestF ri x) -> SizedRecursion $ Map.singleton ri Nothing
    UnsizedFW (SizeStageF sm x) -> sm <> x
    x -> Data.Foldable.fold x

{-
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
      initState = (TypeVariable RuntimeLoc 0, Set.empty, 0)
      (rt, (_, s, _)) = State.runState runner initState
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap s)

annotateTree :: forall g f. (Base g ~ f, Traversable f, Annotatable1 f, Recursive g, Annotatable g)
  => g -> Either TypeCheckError (Cofree f PartialType)
annotateTree term = do
  (rt, resolver) <- partiallyAnnotate term
  let fResolve = fullyResolve resolver
      ca x = anno1 x >>= \a -> pure (fResolve a :< x)
      f = ca <=< sequence
      initState = (TypeVariable RuntimeLoc 0, Set.empty, 0)
  flip State.evalState initState . runExceptT $ cata f term

matchType :: PartialType -> PartialType -> Bool
matchType a b = case (a,b) of
  (ZeroTypeP, ZeroTypeP)         -> True
  (AnyType, _)                   -> True
  (_, AnyType)                   -> True
  (TypeVariable _ _, _)          -> True
  (_, TypeVariable _ _)          -> True
  (ArrTypeP a b, ArrTypeP c d)   -> matchType a c && matchType b d
  (PairTypeP a b, PairTypeP c d) -> matchType a c && matchType b d
  _                              -> False

matchTypeHead :: (Annotatable1 f, Annotatable g) => PartialType -> f g -> Bool
matchTypeHead t x =
  let initState = (TypeVariable RuntimeLoc 0, Set.empty, 0)
  in case State.evalState (runExceptT $ anno1 x) initState of
    Left _   -> False
    Right t' -> matchType t' t

instance Validity a => Validity (BasicExprF a)
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
                   initState = (TypeVariable RuntimeLoc startVar, Set.empty, startVar)
                   etb = \case
                     Right True -> True
                     _ -> False
                   getTypeLevel = flip State.evalState initState . runExceptT . liftAnno anno
                   matchLevel (a CofreeT.:< fx) = All (etb $ matchType a <$> getTypeLevel (fst <$> fx))
                     <> Data.Foldable.fold (snd <$> fx)
               in declare "grammar matches type annotations" . getAll $ para matchLevel x
instance Validity (Fix BasicExprF) where
  validate = error "fix Validity instance for StuckExpr"

instance GenValid a => GenValid (BasicExprF a) where
instance GenValid FunctionIndex
instance GenValid a => GenValid (StuckF a) where
instance GenValid a => GenValid (SuperPositionF a) where
instance GenValid a => GenValid (AbortableF a) where
instance GenValid UnsizedRecursionToken
instance GenValid SizedRecursion where
instance GenValid a => GenValid (UnsizedRecursionF a) where
instance GenValid a => GenValid (IndexedInputF a) where
instance GenValid a => GenValid (UnsizedExprF a) where
instance GenValid (Fix BasicExprF) where
  genValid = error "fix GenValid instance for StuckExpr"
  shrinkValid = error "fix GenValid instance for StuckExpr"

class GenValidAdj g where
  type Gennable g
  toGennable :: g -> Gennable g
  fromGennable :: Gennable g -> g

instance GenValid (Cofree UnsizedExprF PartialType) where
  genValid = genValid >>= (sized . genTypedTree Nothing . toPartialType)
  shrinkValid (a :< x) = (a :<) <$> filter (matchTypeHead a) (shrinkValidStructurally x)

instance GenValidAdj UnsizedExpr where
  type Gennable UnsizedExpr = Cofree UnsizedExprF PartialType
  toGennable x = case annotateTree x of
    Left z -> error ("UnsizedExpr toGennable mistyped expression: " <> show z <> "\nfrom\n" <> ppax) where
      annoTerm :: UnsizedExpr -> Either TypeCheckError (Gennable UnsizedExpr)
      annoTerm term = do
        (rt, resolver) <- partiallyAnnotate term
        let ca x = anno1 x >>= \a -> pure (resolve a :< x)
            resolve = \case
              t@(TypeVariable _ i) -> (fromMaybe t (resolver i))
            f = ca <=< sequence
            initState = (TypeVariable RuntimeLoc 0, Set.empty, 0)
        flip State.evalState initState . runExceptT $ cata f term
      ppax = case annoTerm x of
        Left z   -> "toGennable ppax bad: " <> show z
        Right x' -> prettyPrint x
    Right x -> x
  fromGennable x = cata f x where
    f (_ CofreeT.:< x) = embed x


genTypedTree :: Maybe PartialType -> PartialType -> Int -> Gen (Cofree UnsizedExprF PartialType)
genTypedTree ti t i = -- TODO generate UnsizedF sections?
  let optionEnv = if ti == Just t
                  then (pure (t :< embedS EnvSF) :)
                  else id
      optionGate = case t of
        ArrTypeP ZeroTypeP to -> ((ta . embedS <$> (GateSF <$> genTypedTree ti to half <*> genTypedTree ti to half)) : )
        _ -> id
      optionAbort = case t of
        ArrTypeP ZeroTypeP (ArrTypeP _ _) -> ((pure . ta $ embedA AbortF) : )
        _                                 -> id
      ta = (t :<)
      half = div i 2
      setEnvOption = genValid >>= makeSetEnv where
        makeSetEnv ti' = ta . embedS . SetEnvSF <$> genTypedTree ti (PairTypeP (ArrTypeP ti' t) ti') (i - 1)
      leftOption = genValid >>= makeLeft where
        makeLeft ti' = ta . embedS . LeftSF <$> genTypedTree ti (PairTypeP t ti') (i - 1)
      rightOption = genValid >>= makeRight where
        makeRight ti' = ta . embedS . RightSF <$> genTypedTree ti (PairTypeP ti' t) (i - 1)
      eitherOption = ta . embedP <$> (EitherPF <$> genValid <*> genTypedTree ti t half <*> genTypedTree ti t half)
      abortedOption = pure . ta . embedA . AbortedF . AbortUser $ s2b "Arbitrary Test Data"
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

-}
