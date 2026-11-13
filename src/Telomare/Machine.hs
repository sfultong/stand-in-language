{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- |The shared small-step abstract machine: composable step algebras over
-- any IR built from the base functors. Each @*Step@ handles one functor
-- (basic pairs, stuck/defer forms, aborts, superpositions, indexed
-- inputs, unsized-recursion markers) and defers the rest to the next
-- handler, so the sizing pass, the reference evaluator and the partial
-- evaluators all assemble their interpreters from the same parts.
module Telomare.Machine where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader (MonadReader, asks, local)
import Data.Functor.Classes (Eq1 (..))
import Data.Functor.Foldable
import qualified Data.Map.Strict as Map
-- import Data.SBV ((.<), (.>))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import Telomare.IR.Base
import Telomare.PrettyPrint
import Telomare.Size.IR

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

basicStep :: (Base g ~ f, BasicBase f, Corecursive g, Recursive g) => (f g -> g) -> f g -> g
basicStep handleOther = \case
  -- stuck values
  x@(BasicFW ZeroSF)                       -> embed x
  x@(BasicFW (PairSF _ _))                 -> embed x
  x                                        -> handleOther x

{-# INLINABLE basicStepM #-}
basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, PrettyPrintable g, Monad m) => (f g -> m g) -> f g -> m g
basicStepM handleOther x = f x where
  f = \case
    -- stuck values
    x'@(BasicFW ZeroSF)                      -> pure $ embed x'
    x'@(BasicFW (PairSF _ _))                -> pure $ embed x'

    _                                        -> handleOther x

transformNoDefer :: (Base g ~ f, StuckBase f, Recursive g) => (f g -> g) -> g -> g
transformNoDefer f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> s
    x                         -> fmap c x

{-# INLINABLE transformNoDeferM #-}
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

-- | A gate's result once gates distribute over superpositions: a branch
-- selector, or a superposition of them (an aborted gate stays aborted).
-- Choosing a branch with one runs no code, so it needs no environment
-- restricted to the inputs that make each choice.
isSelectorTree :: (Base g ~ f, StuckBase f, SuperBase f, AbortBase f, Recursive g, Corecursive g) => g -> Bool
isSelectorTree x = case x of
  SuperEE (EitherPF _ a b) -> isSelectorTree a && isSelectorTree b
  AbortEE _                -> True
  _                        -> isGateSelector x

stuckStep :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF _fid d)) e) -> db $ transformNoDefer (basicStep (stuckStep handleOther) . replaceEnv) d where
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


{-# INLINABLE stuckStepM #-}
stuckStepM :: (Base a ~ f, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
stuckStepM handleOther x = f x where
  f = \case
    FillFunction (StuckEE (DeferSF _fid d)) e -> transformNoDeferM runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = project e
      replaceEnv = \case
        StuckFW EnvSF -> e'
        x'            -> x'
    StuckFW (LeftSF z@(BasicEE ZeroSF))      -> pure z
    StuckFW (LeftSF (BasicEE (PairSF l _)))  -> pure l
    StuckFW (RightSF z@(BasicEE ZeroSF))     -> pure z
    StuckFW (RightSF (BasicEE (PairSF _ r))) -> pure r
    FillFunction GateB ZeroB                 -> pure doLeft
    FillFunction GateB (PairB _ _)           -> pure doRight
    -- stuck value
    x'@(StuckFW (DeferSF _ _)) -> pure $ embed x'
    x'@(StuckFW GateSF)                 -> pure $ embed x'
    _ -> handleOther x



{-# INLINABLE gateBasicResult #-}
gateBasicResult :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateBasicResult handleOther = \case
  BasicEE ZeroSF -> GateResult True False Nothing
  BasicEE (PairSF _ _) -> GateResult False True Nothing
  x -> handleOther x

{-# INLINABLE gateSuperResult #-}
gateSuperResult :: (Base g ~ f, SuperBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> (g -> GateResult g) -> g -> GateResult g
gateSuperResult step handleOther = \case
  SuperEE (EitherPF n a b) -> let GateResult la ra ba = step a
                                  GateResult lb rb bb = step b
                                  co = case (ba, bb) of
                                    (Just ba', Just bb') -> pure . superEE $ EitherPF n ba' bb'
                                    _ -> ba <|> bb
                              in GateResult (la || lb) (ra || rb) co
  x -> handleOther x

{-# INLINABLE gateAbortResult #-}
gateAbortResult :: (Base g ~ f, AbortBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateAbortResult handleOther = \case
  a@(AbortEE _) -> GateResult False False $ Just a
  x -> handleOther x

{-# INLINABLE gateIndexedResult #-}
gateIndexedResult :: (Base g ~ f, IndexedInputBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateIndexedResult handleOther = \case
  -- IndexedEE (IVarF n) -> GateResult True False Nothing -- wait, why lb but no rb?
  IndexedEE (IVarF _n) -> GateResult True True Nothing
  IndexedEE (BoundedF _ _) -> GateResult True True Nothing
  x -> handleOther x

{-# INLINABLE mergeShallow #-}
mergeShallow :: (Base g ~ f, BasicBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g) => Maybe Integer -> g -> g -> g
mergeShallow n a b
  -- a stuck path has no value to contribute: it does not exist, or the run
  -- stops there ('stuckSizingStepM')
  | stuck a   = b
  | stuck b   = a
  -- nor has a path the program aborts on: what follows an aborted value only
  -- passes it on, so it needs no count, and kept as an alternative the abort
  -- multiplies through all that follows (a case with no default yields it
  -- beside every value it matches)
  | programAbort a = b
  | programAbort b = a
  | same      = debugTrace ("mergeShallow found same pair\n" <> prettyPrint a <> "\nand\n" <> prettyPrint b) a
  | otherwise = superEE $ EitherPF n a b
  where
    -- the sizing analysis's aborts carry its verdict in their messages, so
    -- two of them are the same only when the messages are
    same = case (a, b) of
      (AbortEE (AbortF o m), AbortEE (AbortF o' m'))
        | sizing o || sizing o' -> sizing o && sizing o' && messageData m == messageData m'
      _ -> shallowEq1 (project a) (project b)
    sizing = (== SizingAbort) . abortKind
    stuck = \case
      AbortEE (AbortF o m) | sizing o, AbortStuck <- messageData m -> True
      _                                                            -> False
    programAbort = \case
      AbortEE (AbortF o _) -> not (sizing o)
      _                    -> False

{-# INLINABLE foldGateResult #-}
foldGateResult :: forall g f. (Base g ~ f, SuperBase f, BasicBase f, StuckBase f, AbortBase f, Recursive g, Corecursive g) => Maybe Integer -> GateResult g -> g
foldGateResult n (GateResult doL doR o) =
  let branchPart = case (doL, doR) of
        (True, True) -> pure . superEE $ EitherPF n doLeft doRight
        (True, _)    -> pure doLeft
        (_, True)    -> pure doRight
        _            -> Nothing
  in case (o, branchPart) of
    -- a gate on a value the program aborts on selects nothing worth sizing
    -- ('mergeShallow')
    (Just (AbortEE (AbortF ao _)), Just bp) | abortKind ao /= SizingAbort -> bp
    (Just o', Just bp) -> superEE $ EitherPF Nothing o' bp
    (Just x, _)        -> x
    (_, Just x)        -> x
    _                  -> error "foldGateResult: no results"

-- |A gate on @EitherPF n a b@: the gate on @a@ where position @n@ is
-- Zero, and the gate on @b@ where it is a pair. Each side's own result is
-- flattened to the choices it can make (a branch selector, an abort, or an
-- unknown choice between them), so a gate's result is never more than two
-- levels deep however deep its scrutinee.
--
-- Flattening a whole superposition into one choice tagged @n@, as this
-- once did, says the left branch is taken where @n@ is Zero, which is
-- wrong when @a@ goes right or both ways. A branch's code then saw its
-- environment restricted the wrong way and missed values it meets
-- (test/programs/mislabeled-size.tel). A side's unknown choice is sound,
-- and the combinations that never happen that it lets through end in
-- 'AbortStuck' ('stuckSizingStepM').
gateSuper :: (Base g ~ f, SuperBase f, BasicBase f, StuckBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g)
  => (g -> GateResult g) -> Maybe Integer -> g -> g -> g
gateSuper gateResult n a b = mergeShallow n (side a) (side b) where
  side = foldGateResult Nothing . gateResult

superStep :: forall a f. (Base a ~ f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
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
    FillFunction GateB (SuperEE (EitherPF n a b)) -> gateSuper gateResult n a b
    FillFunction (SuperEE (EitherPF n sca scb)) e | isSelectorTree sca && isSelectorTree scb -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE $ PairSF sca e)
      (step . embedS . SetEnvSF . BasicEE $ PairSF scb e)
    (FillFunction (SuperEE (EitherPF n sca scb)) e) -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
      (step . embedS . SetEnvSF . BasicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> embed x
    x -> handleOther x

{-# INLINABLE superStepM #-}
superStepM :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (a -> GateResult a) -> (f a -> m a) -> (f a -> m a) -> f a -> m a
superStepM gateResult step handleOther x = f x where
  pbStep bf = step . embedS . bf
  filterLeft :: Maybe Integer -> f a -> a
  filterLeft n = \case
        _s@(SuperFW (EitherPF nt a _)) | (decendant <$> nt <*> n) == Just True -> a
        x' -> embed x'
  filterRight :: Maybe Integer -> f a -> a
  filterRight n = \case
        _s@(SuperFW (EitherPF nt _ b)) | (decendant <$> n <*> nt) == Just True -> b
        x' -> embed x'
  f = \case
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) ->  mergeShallow n <$> pbStep LeftSF a <*> pbStep LeftSF b
    StuckFW (RightSF (SuperEE (EitherPF n a b))) ->  mergeShallow n <$> pbStep RightSF a <*> pbStep RightSF b
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep SetEnvSF a <*> pbStep SetEnvSF b
    FillFunction GateB (SuperEE (EitherPF n a b)) -> pure $ gateSuper gateResult n a b
    FillFunction (SuperEE (EitherPF n sca scb)) e ->
      let fl = if null n || isSelectorTree sca then id else cata (filterLeft n)
          fr = if null n || isSelectorTree scb then id else cata (filterRight n)
      in mergeShallow n
       <$> (pbStep SetEnvSF . BasicEE . PairSF sca $ fl e)
       <*> (pbStep SetEnvSF . BasicEE . PairSF scb $ fr e)
    -- stuck values
    x'@(SuperFW (EitherPF _ _ _)) -> pure $ embed x'

    _ -> handleOther x

-- |What a branch of an exact run knows of the input: positions known to
-- be Zero (with everything below them), and positions known to be pairs
-- (kept with every position above them, which are pairs too).
data InputPath = InputPath
  { knownZero :: Set Integer
  , knownPair :: Set Integer
  }

-- |A path knowing only that the given positions are Zero.
zeroPath :: Set Integer -> InputPath
zeroPath zeros = InputPath zeros Set.empty

-- |Just True when the path says position @m@ is Zero, Just False when a
-- pair.
pathDecides :: InputPath -> Integer -> Maybe Bool
pathDecides (InputPath zs ps) m
  | Set.member m ps                    = Just False
  | any (`Set.member` zs) (ancestry m) = Just True
  | otherwise                          = Nothing
  where
    ancestry x = x : if x <= 0 then [] else ancestry ((x - 1) `div` 2)

-- |The path extended with position @n@ being Zero (True) or a pair.
withLiteral :: Bool -> Integer -> InputPath -> InputPath
withLiteral isZero n (InputPath zs ps)
  | isZero    = InputPath (Set.insert n zs) ps
  | otherwise = InputPath zs (ps <> Set.fromList (ancestry n))
  where
    ancestry x = x : if x <= 0 then [] else ancestry ((x - 1) `div` 2)

-- |'superStepM' where a superposition is exact: @EitherPF (Just n) a b@ is
-- @a@ when input position @n@ is Zero and @b@ when it is a pair, and
-- @EitherPF Nothing a b@ is an unknown choice between the two. Each branch
-- remembers the path that led to it, the 'InputPath' its code runs under
-- ('local'), and a superposition or input gate it uses is decided by that
-- path when the path knows its position. So two uses of one superposed
-- value pick matching branches rather than every combination of them, and
-- what the branches build stays shared, since nothing is rewritten until
-- it is used. A gate on a superposition is a superposition of gates,
-- never a flattening of their results.
--
-- This step decides gates on the input itself, so it goes in place of
-- 'indexedSuperStepM'. Branches merge only when equal ('mergeExact'), which
-- costs size, so this is for the analyses that need the precision rather
-- than for sizing.
{-# INLINABLE exactSuperStepM #-}
exactSuperStepM :: forall a f m. (Base a ~ f, Traversable f, Eq1 f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, MonadReader InputPath m)
  => (f a -> m a) -> (f a -> m a) -> f a -> m a
exactSuperStepM step handleOther x = f x where
  pbStep bf = step . embedS . bf
  -- run each side under what it knows, unless the path already decides
  branch n onZero onPair = do
    known <- asks (\p -> n >>= pathDecides p)
    case known of
      Just True  -> onZero
      Just False -> onPair
      Nothing    -> case n of
        Just n' -> mergeExact n <$> local (withLiteral True n') onZero
                                <*> local (withLiteral False n') onPair
        Nothing -> mergeExact n <$> onZero <*> onPair
  f = \case
    FillFunction GateB (IndexedEE (IVarF n)) -> asks (`pathDecides` n) >>= \case
      Just True  -> pure doLeft
      Just False -> pure doRight
      Nothing    -> pure . superEE $ EitherPF (pure n) doLeft doRight
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) -> branch n (pbStep LeftSF a) (pbStep LeftSF b)
    StuckFW (RightSF (SuperEE (EitherPF n a b))) -> branch n (pbStep RightSF a) (pbStep RightSF b)
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> branch n (pbStep SetEnvSF a) (pbStep SetEnvSF b)
    FillFunction GateB s@(SuperEE (EitherPF n a b)) -> asks (`dataDecisionDepth` s) >>= \case
      Just depth | depth > deepDecision -> pure . superEE $ EitherPF Nothing doLeft doRight
      _ -> branch n (step $ FillFunction GateB a) (step $ FillFunction GateB b)
    FillFunction (SuperEE (EitherPF n sca scb)) e ->
      branch n (pbStep SetEnvSF . BasicEE $ PairSF sca e) (pbStep SetEnvSF . BasicEE $ PairSF scb e)
    -- stuck values
    x'@(SuperFW (EitherPF _ _ _)) -> pure $ embed x'
    _ -> handleOther x

-- |How many input positions deep a superposition may decide a gate before
-- the gate is taken as an unknown choice ('exactSuperStepM').
deepDecision :: Int
deepDecision = 8

-- |How deep a superposition's choices go on a path, when every outcome of
-- it there is plain data: Zero or a pair, so a gate on it only selects a
-- branch. Choices the path decides are followed, not counted. Nothing when
-- an outcome is something else, such as an aborted value, or the walk runs
-- past its budget. A gate on a deep such superposition is one decision of
-- many input positions, as an equality test with a literal makes;
-- following each of its outcomes apart would run what follows once per
-- position the test read.
dataDecisionDepth :: (Base g ~ f, BasicBase f, SuperBase f, Recursive g, Corecursive g)
                  => InputPath -> g -> Maybe Int
dataDecisionDepth path = fmap fst . go (4096 :: Int) where
  go budget v
    | budget <= 0 = Nothing
    | otherwise = case v of
        SuperEE (EitherPF (Just m) l r) | Just pick <- pathDecides path m ->
          go (budget - 1) (if pick then l else r)
        SuperEE (EitherPF _ l r) -> do
          (dl, budget') <- go (budget - 1) l
          (dr, budget'') <- go budget' r
          pure (1 + max dl dr, budget'')
        ZeroB     -> Just (0, budget - 1)
        PairB _ _ -> Just (0, budget - 1)
        _         -> Nothing

-- |@EitherPF n a b@, kept as small as exactness allows. What @n@ decides
-- of the branches' own superpositions is taken, and the choice is pushed
-- down past the structure the branches share: choosing by an input
-- position commutes with pairing, so @EitherPF n (a, b) (c, d)@ is
-- @(EitherPF n a c, EitherPF n b d)@, and a superposition is left only
-- where the branches differ in shape. A closure merged so stays one
-- closure, with its environment superposed, and applying it runs its code
-- once. An unknown choice (@Nothing@) is not pushed down, since its two
-- uses would no longer be the same choice.
mergeExact :: (Base g ~ f, Eq1 f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, Recursive g, Corecursive g) => Maybe Integer -> g -> g -> g
mergeExact n a b = case n of
  Nothing -> if exactEq a b then a else superEE $ EitherPF n a b
  Just n' -> go n' a b
  where
    -- what is known on each side is the one literal, so it is tested
    -- directly rather than through an 'InputPath'
    go n' x y =
      let x' = peel True n' x
          y' = peel False n' y
      in if isTrue# (reallyUnsafePtrEquality# x' y') then x' else case (x', y') of
        (PairB xl xr, PairB yl yr) -> PairB (go n' xl yl) (go n' xr yr)
        (AbortEE (AbortF o xm), AbortEE (AbortF o' ym)) | o == o' -> AbortB o (go n' xm ym)
        _ | exactEq x' y' -> x'
          | otherwise     -> superEE $ EitherPF n x' y'
    peel isZero n' v = case v of
      SuperEE (EitherPF (Just m) l r) | Just pick <- literalDecides isZero n' m ->
        peel isZero n' (if pick then l else r)
      _ -> v

-- |What knowing input position @n@ to be Zero (True) or a pair says of
-- position @m@: Just True when @m@ is Zero, Just False when a pair. Below
-- a Zero is all Zero; above a pair is all pairs.
literalDecides :: Bool -> Integer -> Integer -> Maybe Bool
literalDecides isZero n m
  | isZero && decendant m n     = Just True
  | not isZero && decendant n m = Just False
  | otherwise                   = Nothing

-- |A value as its path knows it: every superposition the path decides is
-- resolved, and every input position it knows to be Zero is Zero. For
-- what leaves the run, such as a check's result, rather than for values
-- still being computed with.
resolvePath :: (Base g ~ f, SuperBase f, BasicBase f, IndexedInputBase f, Recursive g, Corecursive g) => InputPath -> g -> g
resolvePath p = cata $ \case
  SuperFW (EitherPF (Just m) l r) | Just pick <- pathDecides p m -> if pick then l else r
  IndexedFW (IVarF m) | pathDecides p m == Just True -> ZeroB
  x -> embed x

-- |Structural equality that, unlike '==', compares code by its body and
-- not only its function index. Branches share what they did not change,
-- so the same node is recognized without a walk.
exactEq :: (Base g ~ f, Eq1 f, StuckBase f, Recursive g) => g -> g -> Bool
exactEq a b = isTrue# (reallyUnsafePtrEquality# a b) || case (project a, project b) of
  (StuckFW (DeferSF i x), StuckFW (DeferSF j y)) -> i == j && exactEq x y
  (fa, fb)                                       -> liftEq exactEq fa fb

indexedSuperStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedSuperStep handleOther = \case
  FillFunction GateB (IndexedEE (IVarF n)) -> superEE $ EitherPF (pure n) doLeft doRight
  x -> handleOther x

{-# INLINABLE indexedSuperStepM #-}
indexedSuperStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedSuperStepM handleOther = \case
  FillFunction GateB (IndexedEE (IVarF n)) -> pure . superEE $ EitherPF (pure n) doLeft doRight
  FillFunction GateB (IndexedEE (BoundedF _ n)) -> pure . superEE $ EitherPF (pure n) doLeft doRight

  x -> handleOther x

-- | Aborted values: the children are already evaluated, so any 'AbortF'
-- among them has fired, and it propagates to whatever would use it.
abortStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, PrettyPrintable a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    StuckFW (LeftSF a@(AbortEE _)) -> a
    StuckFW (RightSF a@(AbortEE _)) -> a
    StuckFW (SetEnvSF a@(AbortEE _)) -> a
    FillFunction a@(AbortEE _) _ -> a
    FillFunction GateB a@(AbortEE _) -> a
    -- an abort in the message is the one that counts
    AbortFW (AbortF _ a@(AbortEE _)) -> a
    -- an aborted value keeps only its message's data
    AbortFW (AbortF o m) | not (isData m) -> AbortB o (dataB (messageData m))
    -- stuck values
    x@(AbortFW _) -> embed x
    x -> handleOther x

{-# INLINABLE abortStepM #-}
abortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
abortStepM handleOther x = f x where
  f = \case
    StuckFW (LeftSF a@(AbortEE _)) -> pure a
    StuckFW (RightSF a@(AbortEE _)) -> pure a
    StuckFW (SetEnvSF a@(AbortEE _)) -> pure a
    FillFunction a@(AbortEE _) _ -> pure a
    FillFunction GateB a@(AbortEE _) -> pure a
    AbortFW (AbortF _ a@(AbortEE _)) -> pure a
    AbortFW (AbortF o m) | not (isData m) -> pure $ AbortB o (dataB (messageData m))
    -- stuck values
    x'@(AbortFW _) -> pure $ embed x'
    _ -> handleOther x

-- list of defer indexes for functions generated during eval. Need to be unique (grammar under defer n should always be the same)
twiddleInd, leftGateInd, rightGateInd, unsizedStepMEInd, unsizedStepMTInd, unsizedStepMa, unsizedStepMrfa, unsizedStepMrfb, unsizedStepMw, removeRefinementWrappersTC, refinementGateInd, refinementPassInd, inputPrologueInd, stepProgramInd, stepNextInd :: Int
twiddleInd = -1
leftGateInd = -2
rightGateInd = -3
unsizedStepMEInd = -4
unsizedStepMTInd = -5
unsizedStepMa = -6
unsizedStepMrfa = -7
unsizedStepMrfb = -8
unsizedStepMw = -9
removeRefinementWrappersTC = -10
refinementGateInd = -11
refinementPassInd = -12
inputPrologueInd = -13
stepProgramInd = -14
stepNextInd = -15

deferB :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
deferB n = StuckEE . DeferSF (toEnum n)

lamB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
lamB n x = PairB (deferB n x) EnvB

twiddleB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
twiddleB = deferB twiddleInd $ PairB (LeftB (RightB EnvB)) (PairB (LeftB EnvB) (RightB (RightB EnvB)))

appB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
appB c i = SetEnvB (SetEnvB (PairB twiddleB (PairB i c)))

-- | Lazy if-then-else, the default conditional encoding: each branch is
-- wrapped in a defer, the gate selects one closure, and the selection is
-- applied to the current env — so the unselected branch is never evaluated
-- (in the IC runtime it is erased without ever being instantiated).
iteB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g -> g
iteB i t e = FillFunctionEE (FillFunctionEE (FillFunctionEE GateB i) (PairB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t))) EnvB

argOneB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argOneB = LeftB EnvB
argTwoB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argTwoB = LeftB (RightB EnvB)
argThreeB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argThreeB = LeftB (RightB (RightB EnvB))
argFourB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argFourB = LeftB (RightB (RightB (RightB EnvB)))
argFiveB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argFiveB = LeftB (RightB (RightB (RightB (RightB EnvB))))

-- | A number as bare pair data (no annotation constraints, unlike 'i2B').
intB :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => Int -> g
intB 0 = ZeroB
intB n = PairB (intB (n - 1)) ZeroB

-- | One unfolding of a sized recursion during abstract evaluation. The env
-- at execution is @(i, (tWrap, (r, (b, 0))))@; the recur position holds the
-- stub that expands into the next unfolding on demand (it sits inside the
-- lazy ite's branch defer, so it only expands when the test passes).
--
-- The test records that the recursion reached depth @n@, whatever it
-- decides. A sized chain has one link per depth recorded, and its base
-- calls the base case without a test (see 'sizedRecursionChain'), so
-- every test a run can evaluate must have a link of its own: recording
-- only the depths where the recursion stops would miss a test that aborts
-- below them.
unsizedStepBody :: (Base g ~ f, BasicBase f, StuckBase f, UnsizedBase f, Recursive g, Corecursive g)
  => UnsizedRecursionToken -> Int -> g
unsizedStepBody tok n = iteB
  (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure n) $
    appB argTwoB argOneB)
  (appB (appB argThreeB (unsizedEE $ SizeStepStubF tok n EnvB)) argOneB)
  (appB argFourB argOneB)

-- | The n-fold approximant chain a solved recursion hole becomes: the
-- textbook elementary-affine treatment of bounded recursion, replacing the
-- old self-applying repeat frame (which was outside the EAL fragment).
-- Sits where @Env = (trb, _)@ with @trb = (tWrap, (r, (b, 0)))@; each link
-- is a closure @(step, (previous approximant, trb))@ executing with env
-- @(i, (recur, (tWrap, (r, (b, 0)))))@.
--
-- Below the innermost link is the base: a closure, executing with env
-- @(i, (tWrap, (r, (b, 0))))@, that applies the base case without
-- testing. Sizing gives a chain a link for every depth whose test a run
-- can reach ('chainLinks'), so the innermost link's test never passes and
-- a run reaches the base only speculatively (the IC runtime evaluates
-- both branches of a strict gate). The chain is then a plain total
-- function: no abort for exhausting it, since sound sizing never does.
sizedRecursionChain :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g)
  => Int -> g
sizedRecursionChain n = iterate link base !! n where
  trbE = LeftB EnvB
  base = PairB (deferB unsizedStepMw (appB argFourB argOneB)) trbE
  link prev = PairB (deferB unsizedStepMrfb approxBody) (PairB prev trbE)
  -- env: (i, (recur, (tWrap, (r, (b, 0))))). The conditional is the STRICT
  -- gate-switch shape, deliberately: lazy branches capture the whole env in
  -- branch closures, whose whole-and-part contraction forces a box per
  -- chain link (levels then grow with n, and curried recursion becomes
  -- unsatisfiable). Strict branches keep every env path linear, so the
  -- chain is level-flat; the speculation cost is bounded by the chain, and
  -- both the lazy reference evaluator and the stuck/abort-tolerant IC
  -- runtime discard the unselected branch's value harmlessly. This is the
  -- planned post-sizing strictification applied by the compiler itself.
  approxBody = SetEnvB (PairB (SetEnvB (PairB (StuckEE GateSF) (appB argThreeB argOneB)))
    (PairB (appB argFiveB argOneB)
           (appB (appB argFourB argTwoB) argOneB)))

-- | How many links sizing gives a recursion site's chain: one per depth
-- whose test the abstract run reached ('unsizedStepBody'), and a single
-- link to a site sizing found no size for.
chainLinks :: SizedRecursion -> UnsizedRecursionToken -> Int
chainLinks (SizedRecursion sm) tok = case Map.lookup tok sm of
  Just (Just n) -> n
  _noSize       -> 1

-- | What a refinement wrapper around @c@ with predicate @tc@ compiles
-- to once sizing is done: @let r = tc c in (if r then id else abort (1, c)) c@:
-- the check passes where the predicate gives anything but Zero, and a failing
-- check aborts with the value that failed it, as @abort@ does with a message.
-- The outer defer (env @(tc, c)@) computes @r@ once and hands @(r, c)@ to
-- the gate, whose branches have the strict gate-switch shape (see
-- 'sizedRecursionChain'): a passing check builds an aborted value and
-- drops it, so the aborted value's message is itself gated: Zero where the
-- check passes, which is how the check analysis ('Telomare.Size.analyzeChecks')
-- tells a failing run from a passing one.
--
-- The gate picks a function to apply to @c@ rather than picking @c@
-- itself, for sizing: when @r@ is a superposition, so is the function, and
-- applying a superposed function filters its argument per branch
-- ('superStep'), so @c@ goes on narrowed to the inputs that pass the
-- check. Gate branches are deliberately not filtered (see
-- 'isGateSelector'), and without the narrowing a check on the input no
-- longer bounds the recursion that follows it.
--
-- Every check shares the defer indexes 'removeRefinementWrappersTC' and
-- 'refinementGateInd', and its bodies differ only in the abort's origin.
-- That is metadata: analyses keyed by index see the same structure for
-- each, and those keyed by content keep them apart.
refinementCheckB :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive g, Corecursive g)
  => AbortOrigin -> g -> g -> g
refinementCheckB o tc c = SetEnvB $ PairB performTC (PairB tc c) where
  innerTC = appB (LeftB EnvB) (RightB EnvB)
  performTC = deferB removeRefinementWrappersTC . SetEnvB $
    PairB (deferB refinementGateInd gate) (PairB innerTC (RightB EnvB))
  -- env: (r, c)
  failure = GateSwitchEE (PairB (PairB ZeroB ZeroB) (RightB EnvB)) ZeroB (LeftB EnvB)
  gate = SetEnvB $ PairB
    (GateSwitchEE (AbortB o failure) (deferB refinementPassInd EnvB) (LeftB EnvB))
    (RightB EnvB)

-- | The origin of a compiled refinement check's outer body
-- ('refinementCheckB'): the one abort in it.
refinementCheckOrigin :: (Base g ~ f, AbortBase f, Foldable f, Recursive g) => g -> Maybe AbortOrigin
refinementCheckOrigin = cata $ \case
  AbortFW (AbortF o _) -> Just o
  x                    -> foldr (<|>) Nothing x

-- | Remove the compiled refinement checks whose origins pass the test:
-- each becomes the value it guards.
eraseChecks :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Foldable f, Recursive g, Corecursive g)
  => (AbortOrigin -> Bool) -> g -> g
eraseChecks erase = cata $ \case
  StuckFW (SetEnvSF (PairB (StuckEE (DeferSF fi body)) (PairB _ c)))
    | fi == toEnum removeRefinementWrappersTC
    , Just o <- refinementCheckOrigin body
    , erase o -> c
  x -> embed x

unsizedTestIndexed ::(Base g ~ f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive g, Corecursive g)
  => Set Integer -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestIndexed zeroes handleOther ri = \case
  iv@(IndexedEE (IVarF n)) -> debugTrace ("evalRecursionTest ivar " <> show n) $ if isUnbounded zeroes n
    then debugTrace ("evalRecursion punted to abort on " <> show n) AbortB sizingOrigin . dataB . AbortUnsizeable . i2B . fromEnum $ ri
    else if Set.member n zeroes
    then debugTrace ("unsizedTestIndexed resolved to zero for var " <> show n) ZeroB
    else iv
  bv@(IndexedEE (BoundedF zs n)) -> if isUnbounded zs n
    then AbortB sizingOrigin . dataB . AbortUnsizeable . i2B . fromEnum $ ri
    else bv
  x -> handleOther ri x

unsizedTestSuper :: (Base g ~ f, BasicBase f, SuperBase f, AbortBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestSuper reTest handleOther ri = \case
  SuperEE (EitherPF n a b) -> let getAU = \case
                                    a'@(AbortEE (AbortF o m)) | abortKind o == SizingAbort, AbortUnsizeable _ <- messageData m -> Just a'
                                    _ -> Nothing
                                  na = reTest a
                                  nb = reTest b
                                  r = case getAU na <|> getAU nb <|> (Just . superEE $ EitherPF n na nb) of
                                    Just r' -> r'
                                    Nothing -> error "Telomare.Machine.unsizedTestSuper: unexpected Nothing"
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

unsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f
                           , Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => Int -> (UnsizedRecursionToken -> a -> a)
  -> (f a -> a) -> (f a -> a) -> f a -> a
unsizedStep _maxSize recursionTest fullStep handleOther =
  let combineSizes :: SizedRecursion -> a -> a
      combineSizes sm = \case
        UnsizedEE (SizeStageF smb x) -> unsizedEE $ SizeStageF (smb <> sm) x
        x -> unsizedEE $ SizeStageF sm x
  in \case
    UnsizedFW (SizeStepStubF tok n (BasicEE (PairSF _ trb))) ->
      PairB (deferB unsizedStepMrfa (unsizedStepBody tok (n + 1))) trb
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

-- |The steps the real evaluator is stuck on ('Telomare.Fast' fails them
-- with 'FastStuck'), as the sizing analysis's 'AbortStuck': data applied
-- as a function, setenv of something that is not a pair, a gate on a
-- function, a projection out of one. A lossy superposition can bring
-- together values from different inputs that no real run combines; the
-- path through such a step does not exist, and one that does exist stops
-- there. Either way it needs no recursion counted after it. Anything else
-- unhandled is left to the caller, since it may be a step the analysis is
-- missing on a path that does exist.
{-# INLINABLE stuckSizingStepM #-}
stuckSizingStepM :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
stuckSizingStepM handleOther x = case x of
  FillFunction c _ | dataValue c             -> stuck
  StuckFW (SetEnvSF v) | notPair v           -> stuck
  FillFunction GateB (StuckEE (DeferSF _ _)) -> stuck
  StuckFW (LeftSF (StuckEE (DeferSF _ _)))   -> stuck
  StuckFW (RightSF (StuckEE (DeferSF _ _)))  -> stuck
  _                                          -> handleOther x
  where
    stuck = pure . AbortB sizingOrigin $ dataB AbortStuck
    -- the input is data too
    dataValue = \case
      ZeroB                -> True
      PairB _ _            -> True
      IndexedEE (IVarF _)  -> True
      IndexedEE (BoundedF _ _) -> True
      _                    -> False
    notPair = \case
      ZeroB                  -> True
      StuckEE (DeferSF _ _)  -> True
      _                      -> False

{-# INLINABLE unsizedStepM''' #-}
unsizedStepM''' :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a
                                   , Eq a, PrettyPrintable a, Monad m)
  => Int -> Set Integer -> (UnsizedRecursionToken -> a -> m a) -> (SizedRecursion -> m ()) -> (f a -> m a) -> f a -> m a
unsizedStepM''' maxSize _zeros recursionTest recordSizes handleOther x = f x where
  f = \case
    -- the oracle applied to trb = (tWrap, (r, (b, 0))): wrap the test thunk
    -- so its applications reach the input-boundedness machinery, and emit
    -- the first unfolding
    UnsizedFW (UnsizedStubF tok (BasicEE (PairSF trb _))) -> case trb of
      BasicEE (PairSF tw rest) -> case tw of
        BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
          let nt = PairB (StuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
          in pure $ PairB (deferB unsizedStepMrfa (unsizedStepBody tok 1))
                          (PairB nt rest)
        z -> error $ "unsizedStepM''' unexpected test shape:\n" <> prettyPrint z
      z -> error $ "unsizedStepM''' unexpected oracle operand:\n" <> prettyPrint z
    -- The payload names the recursion that ran out of budget. The depth
    -- reached is always `maxSize + 1`, so the caller reconstructs it from
    -- its settings.
    UnsizedFW (SizeStepStubF tok n _) | n > maxSize -> pure . AbortB sizingOrigin . dataB . AbortRecursion . i2B $ fromEnum tok
    UnsizedFW (SizeStepStubF tok n (BasicEE (PairSF _ trb))) ->
      pure $ PairB (deferB unsizedStepMrfa (unsizedStepBody tok (n + 1))) trb
    UnsizedFW (RecursionTestF ri x') -> recursionTest ri x'
    UnsizedFW (SizeStageF sr x') -> debugTrace ("Hit SizeStage: " <> show sr) $ x' <$ recordSizes sr
    UnsizedFW (TraceF s x') -> pure $ debugTrace ("Hit TraceF: " <> s <> "\n" <> prettyPrint x') x'
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
  -- an unknown run as code (e.g. an unsized recursion inside a refinement
  -- check) gives an unknown result, as in 'indexedInputStepM'
  StuckFW (SetEnvSF (IndexedEE AnyF)) -> indexedEE AnyF
  FillFunction (IndexedEE AnyF) _ -> indexedEE AnyF
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
  let res _s n = case (Set.member n zeroes, isUnbounded zeroes n) of
        (True, _) -> ZeroB
        (_, True) -> AbortB sizingOrigin (dataB AbortAny)
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

{-# INLINABLE indexedInputStepM #-}
indexedInputStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM zeroes handleOther x = f x where
  res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  f = \case
    StuckFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    StuckFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    StuckFW (LeftSF (IndexedEE (BoundedF zs n))) -> pure . boundedInput zs $ n * 2 + 1
    StuckFW (RightSF (IndexedEE (BoundedF zs n))) -> pure . boundedInput zs $ n * 2 + 2
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

{-# INLINABLE indexedInputIgnoreSwitchStepM #-}
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

-- |An input position under the zeros a refinement check requires ('BoundedF'):
-- Zero where one is required, unbounded where none is required at or below
-- it, and bounded otherwise.
boundedInput :: (Base g ~ f, BasicBase f, IndexedInputBase f, Recursive g, Corecursive g) => Set Integer -> Integer -> g
boundedInput zs n
  | Set.member n zs = ZeroB
  | isUnbounded zs n = indexedEE $ IVarF n
  | otherwise = indexedEE $ BoundedF zs n

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
