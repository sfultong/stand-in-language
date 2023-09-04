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
debug = True

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

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


newtype VarIndex = VarIndex { unVarIndex :: Int } deriving (Eq, Ord, Enum, Show)
newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show)

data BitsExprF f
  = ZeroB
  | PairB f f
  | FunctionB VarIndex f
  | SetEnvB f
  | GateB f f
  | VarB VarIndex
  | AbortB
  | RecursionTestB f
  | UnsizedChurchNumeralB
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Show1 BitsExprF where
  liftShowsPrec showsPrec showList prec = \case
    ZeroB -> shows "ZeroB"
    PairB a b -> shows "PairB (" . showsPrec 0 a . shows ", " . showsPrec 0 b . shows ")"
    FunctionB vi x -> shows "FunctionB " . shows vi . shows " (" . showsPrec 0 x  . shows ")"
    SetEnvB x -> shows "SetEnvB (" . showsPrec 0 x . shows ")"
    GateB l r -> shows "GateB (" . showsPrec 0 l . shows ", " . showsPrec 0 r . shows ")"
    VarB vi -> shows "VarB " . shows vi
--    UnusedBits -> shows "UnusedBits"
    AbortB -> shows "AbortB"
    RecursionTestB x -> shows "RecursionTestB (" . showsPrec 0 x . shows ")"
    UnsizedChurchNumeralB -> shows "UnsizedChurchNumeralB"


type BitsExpr = Fix BitsExprF

data BitsExprWMap = BitsExprWMap BitsExpr (Map VarIndex BitsExpr)

data EnvAnnotation a f
  = EnvAnnotation a f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type HalfBitsBase = SplitFunctor BitsExprF PartExprF

data NumberedEnvsF f
  = NDeferF VarIndex f
  | NEnv VarIndex
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type NumberedEnvsBase = BasicBase (SplitFunctor (SplitFunctor UnsizedRecursionF AbortableF) NumberedEnvsF)
type NumberedEnvsExpr = Fix NumberedEnvsBase

-- | takes an unsized church numeral expression and converts it to an expression where all defers are given a
-- unique varindex and every nenv below them is given that same varindex. Also returns the next unused varindex
convertEnvs :: UnsizedExpr VoidF -> (NumberedEnvsExpr, VarIndex)
convertEnvs = first (($ toEnum 0) . cata g) . flip State.runState (toEnum 0) . cata f where
  f :: (Base t ~ UnsizedBase t VoidF, t ~ UnsizedExpr VoidF) => Base t (State VarIndex NumberedEnvsExpr) -> State VarIndex NumberedEnvsExpr
  f = \case
    ZeroFW x -> embed . ZeroFW <$> sequence x
    OneFW (StuckF _ x) -> do
      nx <- cata f x
      ni <- nextVar
      pure . embed . OneFW $ NDeferF ni nx
    TwoFW x -> error "convertEnvs should not contain SuperF"
    ThreeFW x -> embed . TwoFW <$> sequence x
    FourFW x -> embed . sl . sl . sl <$> sequence x
  sl = SplitFunctor . Left
  g x n = case x of
    OneFW (NDeferF i x') -> embed . OneFW . NDeferF i $ x' i
    ZeroFW EnvSF -> embed . OneFW . NEnv $ n
    x' -> embed . ($ n) $ sequence x'
  nextVar = do
    i <- State.get
    State.put $ succ i
    pure i

convertToBits :: VarIndex -> NumberedEnvsExpr -> (BitsExpr, (VarIndex, Map VarIndex BitsExpr))
convertToBits startVar = flip State.runState (startVar, Map.empty) . cata f where
  f = fmap embed . g
  g = \case
    ZeroFW x -> case x of
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
    OneFW x -> case x of
      NDeferF ni x' -> FunctionB ni <$> x'
      NEnv vi -> pure $ VarB vi
    TwoFW AbortF -> trace "convertToBits doing abort now" pure AbortB
    SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left x))))) -> case x of
      RecursionTestF _ x' -> RecursionTestB <$> x'
      SizingResultsF _ _ -> pure UnsizedChurchNumeralB
  nextVar = do
    (i, m) <- State.get
    State.put (succ i, m)
    pure i
  lookupM :: VarIndex -> State (VarIndex, Map VarIndex BitsExpr) (Maybe BitsExpr)
  lookupM k = do
    (_, m) <- State.get
    pure $ Map.lookup k m
  addKey k v = State.modify (second (Map.insert k v))

cata3 :: Recursive t => (Base t (Base t (Base t a)) -> a) -> t -> a
cata3 f = c where c = f . fmap (fmap (fmap c . project) . project) . project

anaM' :: (Monad m, Corecursive t, x ~ Base t, Traversable x) => (a -> m (Base t a)) -> a -> m t
anaM' f = c where c = join . fmap (fmap embed . sequence . fmap c) . f

-- selective transform, stops at function boundaries
transformS :: (BitsExprF BitsExpr -> BitsExpr) -> BitsExpr -> BitsExpr
transformS f =
  let s = \case
        fu@(FunctionB _ _) -> fu
        x -> fmap c x
      c = f . s . project
  in c

evalB :: BitsExprWMap -> BitsExprWMap
evalB (BitsExprWMap x varMap) = showExpr BitsExprWMap (transformS f x) varMap where
  showExpr = debugTrace ("evalB BitsExprWMap\n" <> prettyPrint (BitsExprWMap x varMap))
  f = \case
    RecursionTestB x -> x
    SetEnvB (Fix (PairB df e)) -> case project df of
      GateB l r -> case project e of
        ZeroB -> l
        PairB _ _ -> r
      AbortB -> trace "doing abort here" $ case project e of
        ZeroB -> embed . FunctionB tempIndex . embed $ VarB tempIndex
        _ -> embed AbortB
      FunctionB vi dx -> showAssign transformS f $ transformS fillVars dx where
        fillVars = \case
          VarB vi' -> deepLookup boundMap vi'
          x -> embed x
        boundMap = assignInputVars (deepLookup varMap vi) e varMap
        showAssign x = if vi == toEnum 8
          then debugTrace ("assigning inputs for 8:\n" <> prettyPrint e) x
          else x
      z -> error ("evalB setenv pair f _, found unexpected f of " <> show z <> "\nalso, e is " <> prettyPrint e)
    x -> embed x
  assignInputVars :: BitsExpr -> BitsExpr -> Map VarIndex BitsExpr -> Map VarIndex BitsExpr
  assignInputVars vin vars = case (project vin, project vars) of
    (PairB a b, PairB c d) -> assignInputVars a c . assignInputVars b d
    -- (PairB a b, ZeroB) -> assignInputVars a (embed ZeroB) . assignInputVars b (embed ZeroB)
    (VarB k, v) -> Map.insert k $ embed v
    (za, zb) -> error $ "evalB assignInputVars got " <> prettyPrint za <> "\nand:\n" <> prettyPrint zb
  tempIndex = toEnum (-1)
  deepLookup vm vi = case Map.lookup vi vm of
    Nothing -> embed $ VarB vi
    (Just (Fix p@(PairB _ _))) -> embed $ fmap lookupIV p where
      lookupIV = \case
        Fix (VarB vi') -> deepLookup vm vi'
        x -> x
    Just x -> x

{-
findSwitches :: BitsExprWMap -> Set VarIndex
findSwitches (BitsExprWMap x varMap) = f x where
  f = \case
-}

-- evalBits :: 

-- buildConstraints :: Map VarIndex SBV.SBool ->
{-
buildConstraints :: BitsExprWMap -> SBV.Symbolic SBV.SBool
buildConstraints (BitsExprWMap bitsExpr varMap) = build bitsExpr where
  build = \case
-}

instance TelomareLike BitsExprWMap where
  fromTelomare = wrapUp . convertToBits' . convertEnvs . fromTelomare where
    convertToBits' (nee, vi) = convertToBits vi nee
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

type BasicBase f = SplitFunctor f PartExprF
type StuckBase g f = BasicBase (SplitFunctor f (StuckF g))
type SuperBase g f = StuckBase g (SplitFunctor f SuperPositionF)
type AbortBase g f = SuperBase g (SplitFunctor f AbortableF)
type UnsizedBase g f = AbortBase g (SplitFunctor f UnsizedRecursionF)

type StuckBase' f x = StuckBase x f x
type SuperBase' f x = SuperBase x f x
type AbortBase' f x = AbortBase x f x
type UnsizedBase' f x = UnsizedBase x f x

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
pattern OtherFW :: g x -> SplitFunctor g f x
pattern OtherFW x = SplitFunctor (Left x)

data StuckF g f
  = StuckF FunctionIndex g
  deriving (Functor, Foldable, Traversable)

instance (Show g) => Show1 (StuckF g) where
  liftShowsPrec showsPrec showList prec (StuckF ind x) = shows "StuckF " . shows (fromEnum ind) . shows " (" . shows x . shows " )"

instance (Eq g) => Eq1 (StuckF g) where
  liftEq test (StuckF ga _) (StuckF gb _) = ga == gb

pattern FillFunction :: (Base x ~ BasicBase f, Recursive x) => x -> x -> PartExprF x
pattern FillFunction c e <- SetEnvSF (ZeroEE (PairSF c e))
pattern GateSwitch :: (Base x ~ BasicBase f, Recursive x) => x -> x -> x -> PartExprF x
pattern GateSwitch l r s <- FillFunction (ZeroEE (GateSF l r)) s


fillFunction :: (Base f ~ BasicBase g, Corecursive f) => f -> f -> PartExprF f
fillFunction c e = SetEnvSF (embed $ ZeroFW (PairSF c e))

gateSwitch :: (Base f ~ BasicBase g, Corecursive f) => f -> f -> f -> PartExprF f
gateSwitch  l r s = fillFunction (embed $ ZeroFW (GateSF l r)) s

basicStep :: (Base b ~ BasicBase f, Corecursive b, Recursive b) => (Base b b -> b) -> Base b b -> b
basicStep handleOther = \case
  ZeroFW (LeftSF (ZeroEE ZeroSF)) -> embed $ ZeroFW ZeroSF
  ZeroFW (LeftSF (ZeroEE (PairSF l _))) -> l
  ZeroFW (RightSF (ZeroEE ZeroSF)) -> embed $ ZeroFW ZeroSF
  ZeroFW (RightSF (ZeroEE (PairSF _ r))) -> r
  ZeroFW (GateSwitch l _ (ZeroEE ZeroSF)) -> l
  ZeroFW (GateSwitch _ r (ZeroEE (PairSF _ _))) -> r
  -- stuck values
  x@(ZeroFW ZeroSF) -> embed x
  x@(ZeroFW (PairSF _ _)) -> embed x
  x@(ZeroFW (GateSF _ _)) -> embed x
  x -> handleOther x

newtype StuckExpr f = StuckExpr {unStuckExpr :: StuckBase (StuckExpr f) f (StuckExpr f)}
type instance Base (StuckExpr f) = StuckBase (StuckExpr f) f
instance Functor f => Recursive (StuckExpr f) where
  project = unStuckExpr
instance Functor f => Corecursive (StuckExpr f) where
  embed = StuckExpr
instance Show1 f => Show (StuckExpr f) where
  show = ($ "") . showsPrec1 0 . unStuckExpr
instance Eq1 f => Eq (StuckExpr f) where
  (==) (StuckExpr a) (StuckExpr b) = eq1 a b
instance (Functor f, PrettyPrintable1 f) => PrettyPrintable (StuckExpr f) where
  showP = showP . project

{-
transformStuck :: (Functor f, Functor g) => (StuckBase (StuckExpr f) f (StuckExpr g) -> StuckExpr g)
  -> StuckExpr f -> StuckExpr g
-}
transformStuck f = cata f' where
  f' = \case
    OneFW (StuckF fid x) -> embed . OneFW . StuckF fid $ cata f' x
    -- OneFW (StuckF x) -> f' . OneFW . StuckF $ cata f' x
    x -> f x

{-
transformStuckM :: (Functor f, Functor g, Monad m) => (StuckBase (StuckExpr f) f (m (StuckExpr g)) -> m (StuckExpr g))
  -> StuckExpr f -> m (StuckExpr g)
-}
transformStuckM f = cata f' where
  f' = \case
    OneFW (StuckF fid x) -> embed . OneFW . StuckF fid <$> cata f' x
    x -> f x

stuckStep :: (Base a ~ StuckBase a g2, Recursive a, Corecursive a, PrettyPrintable a) => (Base a a -> a) -> Base a a -> a
stuckStep handleOther = \case
  ZeroFW (FillFunction (OneEE (StuckF fid d)) e) -> db $ cata (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db x = if fid == toEnum 5
      then debugTrace ("stuckstep dumping output at 6:\n" <> prettyPrint e) x
      else x
    replaceEnv = \case
      ZeroFW EnvSF -> e'
      x -> x
  -- stuck value
  x@(OneFW (StuckF _ _)) -> embed x
  x -> handleOther x

evalBottomUp :: (Base t ~ BasicBase f, Corecursive t, Recursive t, Recursive t) => (Base t t -> t) -> t -> t
evalBottomUp handleOther = cata (basicStep handleOther)

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

superStep :: (Base a ~ SuperBase a g2, Recursive a, Corecursive a, PrettyPrintable a) => (a -> a -> a) -> (Base a a -> a) -> Base a a -> a
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

abortStep :: (Base a ~ AbortBase a g2, Recursive a, Corecursive a) => (Base a a -> a) -> Base a a -> a
abortStep handleOther =
  \case
    ZeroFW (LeftSF a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (RightSF a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (SetEnvSF a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (FillFunction a@(ThreeEE (AbortedF _)) _) -> a
    ZeroFW (GateSwitch _ _ a@(ThreeEE (AbortedF _))) -> a
    ZeroFW (FillFunction (ThreeEE AbortF) (ZeroEE ZeroSF)) -> embed . OneFW . StuckF i . embed . ZeroFW $ EnvSF where
      i = toEnum (-1)
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

anyFunctionStep :: (Base a ~ SuperBase a g2, Recursive a, Corecursive a) => (Base a a -> a) -> Base a a -> a
anyFunctionStep handleOther =
  \case
    ZeroFW (FillFunction (TwoEE AnyPF) _) -> embed $ TwoFW AnyPF
    x -> handleOther x

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

unsizedStep :: (Base a ~ UnsizedBase a g2, Recursive a, Corecursive a, Eq a, Show a, PrettyPrintable a) => (Base a a -> a) -> Base a a -> a
unsizedStep handleOther =
  let recur = unsizedStep handleOther
      unsizedMerge = mergeSuper (mergeAbort (mergeUnsized mergeUnknown))
      fullStep = basicStep (stuckStep (superStep unsizedMerge (abortStep (unsizedStep handleOther))))
      recurStep = fullStep . ZeroFW . SetEnvSF
  in \case
    ZeroFW (FillFunction (FourEE (SizingResultsF cts crl)) (FourEE (SizingResultsF ets erl))) ->
      embed . FourFW . SizingResultsF (cts <> ets) . map (fullStep . ZeroFW) $ zipWith fillFunction crl erl
    ZeroFW (LeftSF (FourEE sr@(SizingResultsF _ _))) -> embed . FourFW $ fmap (fullStep . ZeroFW . LeftSF) sr
    ZeroFW (RightSF (FourEE sr@(SizingResultsF _ _))) ->embed . FourFW $ fmap (fullStep . ZeroFW . RightSF) sr
    ZeroFW (SetEnvSF (FourEE sr@(SizingResultsF _ _))) -> embed . FourFW $ fmap (fullStep . ZeroFW . SetEnvSF) sr
    ZeroFW (FillFunction (FourEE sr@(SizingResultsF _ _)) e) -> embed . FourFW $ fmap (fullStep . ZeroFW . (\c -> fillFunction c e)) sr
    ZeroFW (GateSwitch l r (FourEE sr@(SizingResultsF _ _))) -> embed . FourFW $ fmap (fullStep . ZeroFW . gateSwitch l r) sr
    FourFW (UnsizedStubF t e) -> embed . FourFW . SizingResultsF (Set.singleton t) $ iterate recurStep e
    FourFW (RecursionTestF ri x) ->
      let test = \case
            z@(ZeroEE ZeroSF) -> z
            p@(ZeroEE (PairSF _ _)) -> p
            TwoEE AnyPF -> embed . ThreeFW . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
            TwoEE (EitherPF a b) -> embed . TwoFW $ EitherPF (test a) (test b)
            a@(ThreeEE (AbortedF _)) -> a
            FourEE sr@(SizingResultsF _ _) -> embed . FourFW $ fmap test sr
            z -> error ("evalRecursionTest checkTest unexpected " <> show z)
      in test x
    -- stuck values
    x@(FourFW (SizingResultsF _ _)) -> embed x
    x -> handleOther x

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
    -- (OneEE (StuckF ba), OneEE (StuckF bb)) -> embed . OneFW . StuckF $ reMerge ba bb
    (OneEE (StuckF fida ba), OneEE (StuckF fidb _)) | fida == fidb -> embed . OneFW . StuckF fida $ ba
    (TwoEE AnyPF, _) -> embed $ TwoFW AnyPF
    (_, TwoEE AnyPF) -> embed $ TwoFW AnyPF
    (TwoEE (EitherPF a b), TwoEE (EitherPF c d)) -> embed . TwoFW $ EitherPF (reMerge a c) (reMerge b d)
    _ -> mergeOther a b

mergeAbort :: (Base x ~ AbortBase x f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeAbort mergeOther a b =
  case (a,b) of
    (ThreeEE (AbortedF x), ThreeEE (AbortedF y)) | x == y -> embed . ThreeFW $ AbortedF x
    (ThreeEE AbortF, ThreeEE AbortF) -> embed $ ThreeFW AbortF
    _ -> mergeOther a b

mergeUnsized :: (Base x ~ UnsizedBase x f, Eq x, Corecursive x, Recursive x) => (x -> x -> x) -> x -> x -> x
mergeUnsized mergeOther a b =
  let mergeDown = mergeSuper (mergeAbort (mergeUnsized mergeOther))
  in case (a,b) of
    (FourEE aa, FourEE bb) -> case (aa,bb) of
      (RecursionTestF ta x, RecursionTestF tb y) | ta == tb -> embed . FourFW . RecursionTestF ta $ mergeDown x y
      (SizingResultsF ta x, SizingResultsF tb y) | ta == tb -> embed . FourFW . SizingResultsF ta $ zipWith mergeDown x y
    _ -> mergeOther a b

mergeUnknown :: (Base x ~ SuperBase x f, Eq x, Corecursive x, Recursive x) => x -> x -> x
mergeUnknown a b = if a == b
  then a
  else embed . TwoFW $ EitherPF a b

data UnsizedRecursionF f
  = RecursionTestF UnsizedRecursionToken f
  | UnsizedStubF UnsizedRecursionToken f
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
    GateSF l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    LeftSF x   -> indentWithOneChild' "L" $ showP x
    RightSF x  -> indentWithOneChild' "R" $ showP x

instance PrettyPrintable f => PrettyPrintable1 (StuckF f) where
  showP1 :: (PrettyPrintable f, PrettyPrintable a) => StuckF f a -> State Int String
  showP1 = \case
    StuckF fid d -> indentWithOneChild' ("D" <> show (fromEnum fid)) $ showP d

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
    UnsizedStubF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("%" <> show ind) $ showP x
    SizingResultsF _ rl -> do
      i <- State.get
      start <- indentWithChildren' "[" . map showP $ take 2 rl
      pure $ start <> "]"

instance PrettyPrintable1 VoidF where
  showP1 _ = error "VoidF should never be inhabited, so should not be PrettyPrintable1"

instance PrettyPrintable1 BitsExprF where
  showP1 = \case
    ZeroB -> pure "Z"
    PairB a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    FunctionB vi x -> indentWithOneChild' ("F" <> show (fromEnum vi)) (showP x)
    SetEnvB x -> indentWithOneChild' "S" $ showP x
    GateB l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    VarB vi -> pure $ "V" <> (show $ fromEnum vi)
    AbortB -> pure "A"
    RecursionTestB x -> indentWithOneChild' "T" $ showP x
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

term3ToUnsizedExpr :: Functor f => Int -> Term3 -> UnsizedExpr f
term3ToUnsizedExpr maxSize (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag -> ZeroFW ZeroSF
        PairFrag a b -> ZeroFW $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag -> ZeroFW EnvSF
        SetEnvFrag x -> ZeroFW . SetEnvSF $ convertFrag' x
        DeferFrag ind -> OneFW . StuckF (toEnum $ fromEnum ind) . convertFrag' . unFragExprUR $ fragLookup ind
        AbortFrag -> ThreeFW AbortF
        GateFrag l r -> ZeroFW $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x -> ZeroFW . LeftSF $ convertFrag' x
        RightFrag x -> ZeroFW . RightSF $ convertFrag' x
        TraceFrag -> ZeroFW EnvSF
        AuxFrag (RecursionTest tok (FragExprUR x)) -> FourFW . RecursionTestF tok $ convertFrag' x
        -- AuxFrag (NestedSetEnvs t) -> FourFW . SizingResultsF (Set.singleton t) . take maxSize . iterate (embed . ZeroFW . SetEnvSF) . embed $ ZeroFW EnvSF
        AuxFrag (NestedSetEnvs t) -> FourFW . UnsizedStubF t . embed $ ZeroFW EnvSF
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

sizeTerm :: (Traversable f, Show1 f, Eq1 f, PrettyPrintable1 f) => Int -> UnsizedExpr f -> Either UnsizedRecursionToken (AbortExpr f)
sizeTerm maxSize = tidyUp . findSize . sizeF where
  sizeF = transformStuckM $ \case
    ur@(FourFW (RecursionTestF t (tm, x))) -> (aggTest t <> tm, embed . FourFW $ RecursionTestF t x)
    ZeroFW (PairSF (tmc, c@(OneEE _)) (tme, e@(ZeroEE ZeroSF))) | readyForSizing (tmc <> tme) ->
                                        findSize (tmc <> tme, embed . ZeroFW $ PairSF c e)
    x -> embed <$> sequence x
  findSize (tm, x) =
    let evaled = evalPossible testG
        sizingResults = map (second foldAborted) . recursionResults' $ evaled
        testG = case x of -- hacky, to handle many situations
          OneEE (StuckF _ _) -> embed . ZeroFW $ fillFunction x (embed $ TwoFW AnyPF) -- from sizeF
          ZeroEE (PairSF d@(OneEE (StuckF _ _)) _) -> trace "doing 'main' testG" embed . ZeroFW $ fillFunction d (embed $ TwoFW AnyPF) -- compiling main
          _ -> trace "doing 'test' testG" embed . ZeroFW $ fillFunction (embed $ OneFW (StuckF twfid x)) (embed $ TwoFW AnyPF) -- compiling test expression
        selectResult (n, r) alt = case r of
          Just (UnsizableSR _) -> (tm, x)
          -- Nothing -> trace ("after setting sizes is\n" <> prettyPrint (setSizes n x)) (mempty, setSizes n x)
          Nothing -> (mempty, setSizes n x)
          _ -> alt
        twfid = toEnum (-1)
    in foldr selectResult (tm, x) sizingResults
  tidyUp = \case
    (UnsizedAggregate uam, _) | not (null uam) -> case Map.minViewWithKey uam of
                                  Just ((urt, _), _) -> Left urt
    (_, x) -> pure . clean $ x
  clean :: Functor f => UnsizedExpr f -> AbortExpr f
  clean = transformStuck (embed . f) where
    f = \case
      ZeroFW x  -> ZeroFW x
      TwoFW x   -> TwoFW x
      ThreeFW x -> ThreeFW x
      z         -> error "sizeTerm clean should be impossible"
  setSizes n = transformStuck $ \case
    -- FourFW (SizingResultsF _ rl) -> rl !! n
    FourFW (UnsizedStubF _ _) -> iterate (embed . ZeroFW . SetEnvSF) (embed $ ZeroFW EnvSF) !! n

    FourFW (RecursionTestF _ x) -> x
    x -> embed x
  recursionResults' x = map (\n -> (n, cata (f n) x)) [1..maxSize] where
    f n = \case
      FourFW (SizingResultsF _ rl) -> rl !! n
      x -> embed x
  foldAborted :: (Functor f, Foldable f) => UnsizedExpr f -> Maybe SizedResult
  foldAborted = cata f where
    f = \case
      ThreeFW (AbortedF AbortRecursion) -> Just AbortedSR
      ThreeFW (AbortedF (AbortUnsizeable t)) -> Just . UnsizableSR . toEnum . g2i $ t
      x                                 -> Data.Foldable.fold x
  unsizedMerge = mergeSuper (mergeAbort (mergeUnsized mergeUnknown))
  evalPossible = evalBottomUp (stuckStep (superStep unsizedMerge (abortStep (unsizedStep unhandledError))))
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)

instance (Functor o, Traversable o) => TelomareLike (StuckExpr o) where
  fromTelomare = flip State.evalState (toEnum 0) . anaM' f where
    f = \case
      Zero -> pure $ ZeroFW ZeroSF
      Pair a b -> pure . ZeroFW $ PairSF a b
      Env -> pure $ ZeroFW EnvSF
      SetEnv x -> pure . ZeroFW $ SetEnvSF x
      Defer x -> OneFW <$> (StuckF <$> nextVar <*> anaM' f x)
      Gate l r -> pure . ZeroFW $ GateSF l r
      PLeft x -> pure . ZeroFW $ LeftSF x
      PRight x -> pure . ZeroFW $ RightSF x
      Trace    -> error "EnhancedExpr trace"
    nextVar = do
      i <- State.get
      State.put $ succ i
      pure i
  toTelomare = \case
    ZeroEE x -> case x of
      ZeroSF     -> pure Zero
      PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
      EnvSF      -> pure Env
      SetEnvSF p -> SetEnv <$> toTelomare p
      GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
      LeftSF x   -> PLeft <$> toTelomare x
      RightSF x  -> PRight <$> toTelomare x
    OneEE (StuckF _ x) -> Defer <$> toTelomare x
    _ -> Nothing

instance (Functor f, Traversable f) => TelomareLike (UnsizedExpr f) where
  fromTelomare = flip State.evalState (toEnum 0) . anaM' f where
    f = \case
      Zero -> pure $ ZeroFW ZeroSF
      Pair a b -> pure . ZeroFW $ PairSF a b
      Env -> pure $ ZeroFW EnvSF
      SetEnv x -> pure . ZeroFW $ SetEnvSF x
      Defer x -> OneFW <$> (StuckF <$> nextVar <*> anaM' f x)
      Gate l r -> pure . ZeroFW $ GateSF l r
      PLeft x -> pure . ZeroFW $ LeftSF x
      PRight x -> pure . ZeroFW $ RightSF x
      Trace -> error "fromTelomare Telomarelike UnsizedExpr -- trace"
    nextVar = do
      i <- State.get
      State.put $ succ i
      pure i
  toTelomare = cata f where
    f = \case
      ZeroFW x -> case x of
        ZeroSF -> pure Zero
        PairSF a b -> Pair <$> a <*> b
        EnvSF -> pure Env
        SetEnvSF x -> SetEnv <$> x
        GateSF l r -> Gate <$> l <*> r
        LeftSF x -> PLeft <$> x
        RightSF x -> PRight <$> x
      OneFW (StuckF _ x) -> Defer <$> cata f x
      _ -> Nothing

evalBU :: IExpr -> Maybe IExpr
evalBU = toIExpr . ebu . fromTelomare where
  toIExpr = toTelomare
  ebu :: StuckExpr VoidF -> StuckExpr VoidF
  ebu = evalBottomUp (stuckStep undefined) . (\x -> debugTrace ("evalBU starting expr:\n" <> prettyPrint x) x)

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
        DeferFrag ind -> OneFW . StuckF (toEnum . fromEnum $ ind) . convertFrag' $ termMap Map.! ind
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
    convert = \case
      ZeroFW ZeroSF       -> pure ZeroFrag
      ZeroFW (PairSF a b) -> PairFrag <$> a <*> b
      ZeroFW EnvSF        -> pure EnvFrag
      ZeroFW (SetEnvSF x) -> SetEnvFrag <$> x
      OneFW (StuckF _ x)    -> deferF $ cata convert x
      ThreeFW AbortF      -> pure AbortFrag
      ZeroFW (GateSF l r) -> GateFrag <$> l <*> r
      ZeroFW (LeftSF x)   -> LeftFrag <$> x
      ZeroFW (RightSF x)  -> RightFrag <$> x
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
                      eval' = evalBottomUp (stuckStep (superStep (mergeSuper (mergeAbort mergeUnknown)) (abortStep unhandledError)))
                  in eval' . deheadMain $ term4toAbortExpr t
      -- hack to check main functions as well as unit tests
      deheadMain = \case
        ZeroEE (PairSF (OneEE (StuckF _ f)) _) -> f
        x                                      -> x
      getAborted = \case
        ThreeFW (AbortedF e) -> Just e
        TwoFW (EitherPF a b) -> combine a b
        x                    -> foldr (<|>) Nothing x
  -- in flip combine base . cata getAborted $ trace ("evalA runResult is\n" <> prettyPrint runResult) runResult
  in flip combine base . cata getAborted $ runResult
