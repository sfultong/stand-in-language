{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
module Telomare.Possible where

import           Control.Applicative
import           Control.Lens.Plated
import           Control.Lens.Setter
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader      (Reader, ReaderT)
import qualified Control.Monad.Reader      as Reader
import           Control.Monad.State       (State, StateT)
import qualified Control.Monad.State       as State
import           Control.Monad.Trans.Class
import           Data.DList                (DList)
import qualified Data.DList                as DList
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.List                 (sortBy)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Monoid
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Void
import           Debug.Trace
import           PrettyPrint
import           Telomare                  (FragExpr (..), FragExprUR (..),
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
                                            sindent)
import           Telomare.TypeChecker

data PartExprF f
  = ZeroSF
  | PairSF f f
  | EnvSF
  | SetEnvSF f
  | DeferSF f
  | GateSF f f
  | LeftSF f
  | RightSF f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data SizeExpr
  = ZeroS
  | PairS SizeExpr SizeExpr
  | EnvS
  | SetEnvS SizeExpr
  | DeferS SizeExpr
  | GateS SizeExpr SizeExpr
  | LeftS SizeExpr
  | RightS SizeExpr
--  | StuckEnvS SizeExpr
  | EitherS SizeExpr SizeExpr
  | AnyS
  | AbortS
  | AbortedS IExpr
  -- | UnsizedRecursionS UnsizedRecursionToken
  | NestedSetEnvsS UnsizedRecursionToken SizeExpr
  | RecursionTestS UnsizedRecursionToken SizeExpr
  | SizingResultsS [SizeExpr]
  | UnsizeableS UnsizedRecursionToken
  deriving (Eq, Ord, Show)

pattern FillFunctionS :: SizeExpr -> SizeExpr -> SizeExpr
pattern FillFunctionS c e = SetEnvS (PairS c e)

pattern GateSwitchS :: SizeExpr -> SizeExpr -> SizeExpr -> SizeExpr
pattern GateSwitchS l r s = FillFunctionS (GateS l r) s


instance Plated SizeExpr where
  plate f = \case
    PairS a b -> PairS <$> f a <*> f b
    SetEnvS x -> SetEnvS <$> f x
    -- DeferS x -> DeferS <$> f x
    GateS l r -> GateS <$> f l <*> f r
    LeftS x -> LeftS <$> f x
    RightS x -> RightS <$> f x
    EitherS a b -> EitherS <$> f a <*> f b
    RecursionTestS t x -> RecursionTestS t <$> f x
    NestedSetEnvsS t x -> NestedSetEnvsS t <$> f x
    SizingResultsS x -> SizingResultsS <$> traverse f x
    x -> pure x

newtype SizeExprSkippingDefer = SizeExprSkippingDefer { unSizeExprSkippingDefer :: SizeExpr }

instance Plated SizeExprSkippingDefer where
  plate f = let f' = fmap unSizeExprSkippingDefer . f . SizeExprSkippingDefer
                p = \case
                  PairS a b -> PairS <$> f' a <*> f' b
            in fmap SizeExprSkippingDefer . p . unSizeExprSkippingDefer

data TExpr
  = TThing Int
  | TGo TExpr
  | TStop Int TExpr
  deriving (Eq, Ord, Show)

instance Plated TExpr where
  plate f = \case
    TGo x -> TGo <$> f x
    --TStop
    x -> pure x

tIncrement = \case
  TThing x -> TThing $ x + 1
  TStop n x -> TStop (n + 1) x
  x -> x

-- tSum :: TExpr -> Bool
-- tSum = 


-- type ASetter s t a b = (a -> Identity b) -> s -> Identity t
-- tSetter :: ASetter TExpr Bool TExpr Bool
-- tSetter =  plate

-- >>> transform tIncrement $ TStop 1 (TThing 1)
-- TStop 2 (TThing 1)

-- >>> transform tIncrement $ TGo (TThing 1)
-- TGo (TThing 2)

-- >>> join ([Just 1], ([Nothing, Just 2], 0))
-- ([Just 1,Nothing,Just 2],0)

-- >>> [Just 1] <> [Nothing, Just 2]
-- [Just 1,Nothing,Just 2]

instance Eq1 PartExprF where
  liftEq test a b = case (a,b) of
    (ZeroSF, ZeroSF)         -> True
    (EnvSF, EnvSF)           -> True
    (PairSF a b, PairSF c d) -> test a c && test b d
    (SetEnvSF x, SetEnvSF y) -> test x y
    (DeferSF x, DeferSF y)   -> test x y
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
    DeferSF x -> shows "DeferSF (" . showsPrec 0 x . shows ")"
    GateSF l r -> shows "GateSF (" . showsPrec 0 l . shows ", " . showsPrec 0 r . shows ")"
    LeftSF x -> shows "LeftSF (" . showsPrec 0 x . shows ")"
    RightSF x -> shows "RightSF (" . showsPrec  0 x . shows ")"

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

type BasicBase f = SplitFunctor f PartExprF
type StuckBase r g f = BasicBase (SplitFunctor f (StuckF r g))
type SuperBase r g f = StuckBase r g (SplitFunctor f SuperPositionF)
type AbortBase r g f = SuperBase r g (SplitFunctor f AbortableF)
type UnsizedBase r g f = AbortBase r g (SplitFunctor f UnsizedRecursionF)

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
pattern ZeroEE :: PartExprF (EnhancedExpr f) -> EnhancedExpr f
pattern ZeroEE g = EnhancedExpr (ZeroFW g)
pattern OneEE :: g (EnhancedExpr (SplitFunctor f g)) -> EnhancedExpr (SplitFunctor f g)
pattern OneEE g = EnhancedExpr (OneFW g)
pattern TwoEE :: g (EnhancedExpr (SplitFunctor (SplitFunctor f g) h)) -> EnhancedExpr (SplitFunctor (SplitFunctor f g) h)
pattern TwoEE g = EnhancedExpr (TwoFW g)
pattern ThreeEE :: g (EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i))
  -> EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i)
pattern ThreeEE g = EnhancedExpr (ThreeFW g)
pattern FourEE :: g (EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i) j))
  -> EnhancedExpr (SplitFunctor (SplitFunctor (SplitFunctor (SplitFunctor f g) h) i) j)
pattern FourEE g = EnhancedExpr (FourFW g)

bareEnv :: (Functor f, Foldable f) => EnhancedExpr f -> Bool
bareEnv = cata bareF where
  bareF = \case
    ZeroFW EnvSF       -> True
    ZeroFW (DeferSF _) -> False
    x                  -> getAny $ foldMap Any x

data StuckF r g f
  = StuckF r g
  deriving (Functor, Foldable, Traversable)

instance (Show r, Show g) => Show1 (StuckF r g) where
  liftShowsPrec showsPrec showList prec (StuckF r x) = shows "StuckF (" . shows r . shows " - " . shows x . shows " )"

instance (Eq r, Eq g) => Eq1 (StuckF r g) where
  liftEq test (StuckF ra ga) (StuckF rb gb) = ra == rb && ga == gb

data StuckNeedsEnv = StuckNeedsEnv deriving (Eq, Show)
data StuckNeedsSizing = StuckNeedsSizing deriving (Eq, Show)

type SetStuck x = Either x StuckNeedsEnv
type SizeStuck x = SetStuck (Either x StuckNeedsSizing)

newtype StuckExpr s f = StuckExpr { unStuckExpr :: EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f)))}
  deriving (Eq, Show)
  deriving newtype (PrettyPrintable)

pattern StuckFW :: StuckF r g a -> StuckBase r g f a
pattern StuckFW x = SplitFunctor (Left (SplitFunctor (Right x)))
pattern EnhancedStuck :: r -> EnhancedExpr (SplitFunctor f (StuckF r (StuckExpr r f)))
  -> EnhancedExpr (SplitFunctor f (StuckF r (StuckExpr r f)))
pattern EnhancedStuck r x = EnhancedExpr (StuckFW (StuckF r (StuckExpr x)))
pattern EnvStuck :: EnhancedExpr (SplitFunctor f (StuckF (SetStuck es) (StuckExpr (SetStuck es) f)))
  -> EnhancedExpr (SplitFunctor f (StuckF (SetStuck es) (StuckExpr (SetStuck es) f)))
pattern EnvStuck x = EnhancedStuck (Right StuckNeedsEnv) x

pattern FillFunction :: EnhancedExpr f -> EnhancedExpr f -> PartExprF (EnhancedExpr f)
pattern FillFunction c e = SetEnvSF (ZeroEE (PairSF c e))
pattern GateSwitch :: EnhancedExpr f -> EnhancedExpr f -> EnhancedExpr f -> PartExprF (EnhancedExpr f)
pattern GateSwitch l r s = FillFunction (ZeroEE (GateSF l r)) s

liftStuck :: (EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f)))
             -> EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f))))
             -> StuckExpr s f -> StuckExpr s f
liftStuck f = StuckExpr . f . unStuckExpr

inStuck :: (EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f))) -> EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f))))
  -> (EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f))) -> EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f))))
inStuck f = unStuckExpr . liftStuck f . StuckExpr

-- simplest eval rules
basicEval :: (PartExprF (EnhancedExpr o) -> EnhancedExpr o) -> (PartExprF (EnhancedExpr o) -> EnhancedExpr o)
basicEval handleOther = \case
    LeftSF (ZeroEE ZeroSF)               -> ZeroEE ZeroSF
    LeftSF (ZeroEE (PairSF l _))         -> l
    RightSF (ZeroEE ZeroSF)              -> ZeroEE ZeroSF
    RightSF (ZeroEE (PairSF _ r))        -> r
    GateSwitch l _ (ZeroEE (ZeroSF))     -> l
    GateSwitch _ r (ZeroEE (PairSF _ _)) -> r
    x                                    -> handleOther x

type EnhancedSetStuck f s = EnhancedExpr (SplitFunctor f (StuckF (SetStuck s) (StuckExpr (SetStuck s) f)))

evalBottomUp' :: (PrettyPrintable1 o, Functor o) =>
  (StuckBase (SetStuck so) (StuckExpr (SetStuck so) o) o (EnhancedSetStuck o so) -> EnhancedSetStuck o so) ->
  (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so) ->
  StuckExpr (SetStuck so) o -> StuckExpr (SetStuck so) o
evalBottomUp' handleComplex handleOther = StuckExpr . cata evalF . unStuckExpr where
  stepTrace x = trace ("step\n" <> prettyPrint x) x
  recur = evalBottomUp' handleComplex handleOther
  {-
  debugWrap x = if getAny ( foldMap Any (fmap findThing x)) && not (findThing result) then
    trace ("evalBottomUp disappeared thing (before)\n" <> prettyPrint x <> "\nthen after:\n" <> prettyPrint result) result
    else result
    where result = basicEval evalS x
          findThing = elem '!' . prettyPrint
-}
  evalS = \case
    EnvSF -> EnvStuck $ ZeroEE EnvSF
    LeftSF (EnhancedStuck r lx) -> EnhancedStuck r . ZeroEE . LeftSF $ lx
    RightSF (EnhancedStuck r rx) -> EnhancedStuck r . ZeroEE . RightSF $ rx
    SetEnvSF (EnhancedStuck sr sp) -> EnhancedStuck sr . ZeroEE . SetEnvSF $ sp
    FillFunction (ZeroEE (DeferSF d)) e -> cata runStuck d False where
      runStuck x underDefer = case x of
        StuckFW (StuckF (Right StuckNeedsEnv) (StuckExpr s)) | not underDefer ->
          unStuckExpr . recur . StuckExpr . (\rs -> cata runStuck rs False) $ s
        StuckFW (StuckF r (StuckExpr s)) | not underDefer -> EnhancedStuck r (ZeroEE $ FillFunction (ZeroEE (DeferSF s)) e)
        ZeroFW (DeferSF d) -> embed . ZeroFW . DeferSF $ d True
        ZeroFW EnvSF -> e
        x -> embed . fmap ($ underDefer) $ x
    FillFunction (EnhancedStuck sr sc) e -> EnhancedStuck sr . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc e
    -- FillFunction sc (EnvStuck e) -> EnvStuck . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc e
    FillFunction sc (EnhancedStuck r e) -> EnhancedStuck r . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc e
    x -> handleOther x
  evalF = \case
    ZeroFW x -> basicEval evalS x
    -- ZeroFW x -> debugWrap x
    x        -> handleComplex x

evalBottomUp :: (PrettyPrintable1 o, Functor o) =>
  (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so) ->
  StuckExpr (SetStuck so) o -> StuckExpr (SetStuck so) o
evalBottomUp = evalBottomUp' embed

evalBasicDoNothing :: (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so)
  -> (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so)
evalBasicDoNothing handleOther x = let ex = ZeroEE x in case x of
  ZeroSF     -> ex
  PairSF _ _ -> ex
  DeferSF _  -> ex
  GateSF _ _ -> ex
  _          -> handleOther x

type SuperExpr s f = StuckExpr (SetStuck s) (SplitFunctor f SuperPositionF)
type EnhancedSuperStuck f s = EnhancedSetStuck (SplitFunctor f SuperPositionF) s

evalSuper :: (Eq s, Eq1 f, Show1 f, Functor f) =>
  (StuckExpr (SetStuck s) (SplitFunctor f SuperPositionF) -> StuckExpr (SetStuck s) (SplitFunctor f SuperPositionF))
  -> (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
  -> (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
evalSuper recur handleOther =
  let rEval = unStuckExpr . recur . StuckExpr
  in \case
    LeftSF (TwoEE x) -> case x of
      AnyPF -> TwoEE AnyPF
      EitherPF a b -> mergeSuper (rEval . ZeroEE . LeftSF $ a) (rEval . ZeroEE . LeftSF $ b)
    RightSF (TwoEE x) -> case x of
      AnyPF -> TwoEE AnyPF
      EitherPF a b -> mergeSuper (rEval . ZeroEE . RightSF $ a) (rEval . ZeroEE . RightSF $ b)
    SetEnvSF (TwoEE (EitherPF a b)) -> mergeSuper (rEval . ZeroEE . SetEnvSF $ a) (rEval . ZeroEE . SetEnvSF $ b)
    GateSwitch l r se@(TwoEE _) ->
      let getPaths = \case
            ZeroEE ZeroSF -> [Just leftPath, Nothing, Nothing]
            ZeroEE (PairSF _ _) -> [Nothing, Just rightPath, Nothing]
            TwoEE AnyPF -> [Just leftPath, Just rightPath, Nothing]
            TwoEE (EitherPF a b) -> (\[la,ra,oa] [lb,rb,ob] -> [la <|> lb, ra <|> rb, combineOthers oa ob])
              (getPaths a) (getPaths b)
            x -> [Nothing, Nothing, pure . handleOther $ SetEnvSF (ZeroEE (PairSF (ZeroEE (GateSF l r)) x))]
          leftPath = rEval l
          rightPath = rEval r
          combineOthers a b = case (a,b) of
            (Just ja, Just jb) -> pure $ mergeSuper ja jb
            _                  -> a <|> b
      in case foldr combineOthers Nothing $ getPaths se of
        Nothing -> error "evalSuper gates getPaths should be impossible to have no alternatives"
        Just r -> r
    FillFunction (TwoEE (EitherPF sca scb)) se -> mergeSuper
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF sca se)
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF scb se)
    FillFunction sc (TwoEE (EitherPF sea seb)) -> mergeSuper
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc sea)
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc seb)
    x -> handleOther x

type AbortExpr s f = SuperExpr s (SplitFunctor f AbortableF)
type EnhancedAbortStuck f s = EnhancedSuperStuck (SplitFunctor f AbortableF) s

evalAbort :: (Show1 f, Functor f) => (PartExprF (EnhancedAbortStuck f s) -> EnhancedAbortStuck f s)
  -> (PartExprF (EnhancedAbortStuck f s) -> EnhancedAbortStuck f s)
evalAbort handleOther =
  \case
    LeftSF (a@(ThreeEE (AbortedF _))) -> a
    RightSF (a@(ThreeEE (AbortedF _))) -> a
    SetEnvSF (a@(ThreeEE (AbortedF _))) -> a
    FillFunction a@(ThreeEE (AbortedF _)) _ -> a
    FillFunction _ a@(ThreeEE (AbortedF _)) -> a
    FillFunction (ThreeEE AbortF) (ZeroEE ZeroSF) -> ZeroEE . DeferSF . ZeroEE $ EnvSF
    FillFunction (ThreeEE AbortF) e@(ZeroEE (PairSF _ _)) -> ThreeEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        ZeroFW ZeroSF        -> Zero
        ZeroFW (PairSF a b)  -> Pair a b
        TwoFW (EitherPF a _) -> a
        TwoFW AnyPF          -> Zero
        z                    -> error ("evalAbort truncF unexpected thing")
    FillFunction (ThreeEE AbortF) (TwoEE AnyPF) -> ThreeEE . AbortedF $ AbortAny
    x -> handleOther x

evalAnyFunction :: (Eq s, Eq1 f, Show1 f, Functor f)
  => (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
  -> (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
evalAnyFunction handleOther =
  \case
    FillFunction (TwoEE AnyPF) _ -> TwoEE AnyPF
    x                            -> handleOther x

type UnsizedExpr s f = AbortExpr (Either s StuckNeedsSizing) (SplitFunctor f UnsizedRecursionF)
type EnhancedUnsizedStuck f s = EnhancedAbortStuck (SplitFunctor f UnsizedRecursionF) s

type StuckAbortBase f = SplitFunctor (SplitFunctor f AbortableF) SuperPositionF
type StuckUnsizedBase f = StuckAbortBase (SplitFunctor f UnsizedRecursionF)

evalRecursionTest' :: (Show s, Show1 f, Functor f) => Base (EnhancedUnsizedStuck f s)  (EnhancedUnsizedStuck f s) -> EnhancedUnsizedStuck f s
evalRecursionTest' = \case
  FourFW (RecursionTestF ri x) -> case x of
    z@(ZeroEE ZeroSF) -> z
    p@(ZeroEE (PairSF _ _)) -> p
    EnvStuck e -> EnvStuck . FourEE $ RecursionTestF ri e
    TwoEE AnyPF -> FourEE $ UnsizableF ri
    TwoEE (EitherPF a b) -> TwoEE $ EitherPF (evalRecursionTest' $ FourFW (RecursionTestF ri a)) (evalRecursionTest' $ FourFW (RecursionTestF ri b))
    a@(ThreeEE (AbortedF _)) -> a
    u@(FourEE (UnsizableF _)) -> u
    z -> error ("evalRecursionTest checkTest unexpected " <> show z)
  x -> embed x

evalRecursionTest :: (Eq s, Show s, Eq1 f, Show1 f, Functor f) =>
  (StuckExpr (SetStuck s) (StuckUnsizedBase f) -> StuckExpr (SetStuck s) (StuckUnsizedBase f))
  -> (PartExprF (EnhancedUnsizedStuck f s) -> EnhancedUnsizedStuck f s)
  -> (PartExprF (EnhancedUnsizedStuck f s) -> EnhancedUnsizedStuck f s)
evalRecursionTest recur handleOther =
  let checkTest ri = \case
        z@(ZeroEE ZeroSF) -> z
        p@(ZeroEE (PairSF _ _)) -> p
        EnvStuck e -> EnvStuck . FourEE $ RecursionTestF ri e
        TwoEE AnyPF -> FourEE $ UnsizableF ri
        TwoEE (EitherPF a b) -> TwoEE $ EitherPF (checkTest ri a) (checkTest ri b)
        a@(ThreeEE (AbortedF _)) -> a
        u@(FourEE (UnsizableF _)) -> u
        z -> error ("evalRecursionTest checkTest unexpected " <> show z)
      recur' = unStuckExpr . recur . StuckExpr
  in \case
    LeftSF (u@(FourEE (UnsizableF _))) -> u
    RightSF (u@(FourEE (UnsizableF _))) -> u
    SetEnvSF (u@(FourEE (UnsizableF _))) -> u
    FillFunction u@(FourEE (UnsizableF _)) _ -> u
    GateSwitch _ _ u@(FourEE (UnsizableF _)) -> u
    LeftSF (FourEE (RecursionTestF ri x)) -> recur' . ZeroEE . LeftSF $ checkTest ri x
    RightSF (FourEE (RecursionTestF ri x)) -> recur' . ZeroEE .RightSF $ checkTest ri x
    -- FillFunction (FourEE (RecursionTestF t c)) e -> checkTest t . recur' . ZeroEE $ FillFunction c e
    GateSwitch l r (FourEE (RecursionTestF ri s)) -> recur' . ZeroEE . GateSwitch l r $ checkTest ri s
    x -> handleOther x

-- evalNatural ::

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

mergeSuper :: (Eq s, Eq1 f, Functor f) => EnhancedSuperStuck f s -> EnhancedSuperStuck f s -> EnhancedSuperStuck f s
mergeSuper a b =
  let mergeZero pa pb = case (pa,pb) of
        (ZeroSF, ZeroSF)                  -> ZeroEE ZeroSF
        (EnvSF, EnvSF)                    -> ZeroEE EnvSF
        (PairSF a b, PairSF c d) | a == c -> ZeroEE $ PairSF a (mergeSuper b d)
        (PairSF a b, PairSF c d) | b == d -> ZeroEE $ PairSF (mergeSuper a c) b
        (SetEnvSF x, SetEnvSF y)          -> ZeroEE $ SetEnvSF (mergeSuper x y)
        (DeferSF x, DeferSF y)            -> ZeroEE $ DeferSF (mergeSuper x y)
        (GateSF a b, GateSF c d) | a == c -> ZeroEE $ GateSF a (mergeSuper b d)
        (GateSF a b, GateSF c d) | b == d -> ZeroEE $ GateSF (mergeSuper a c) b
        (LeftSF x, LeftSF y)              -> ZeroEE $ LeftSF (mergeSuper x y)
        (RightSF x, RightSF y)            -> ZeroEE $ RightSF (mergeSuper x y)
  {-
        (ZeroSF, PairSF a b)              -> TwoEE $ AlsoZeroPF a b
        (PairSF a b, ZeroSF)              -> TwoEE $ AlsoZeroPF a b
-}
        _                                 -> TwoEE $ EitherPF (ZeroEE pa) (ZeroEE pb)
  in case (a,b) of
    (ZeroEE ba, ZeroEE bb) -> mergeZero ba bb
    (TwoEE AnyPF, _) -> TwoEE AnyPF
    (_, TwoEE AnyPF) -> TwoEE AnyPF
    (TwoEE (EitherPF a b), TwoEE (EitherPF c d)) -> TwoEE $ EitherPF (mergeSuper a c) (mergeSuper b d)
    _ -> TwoEE $ EitherPF a b
{-
mergeSuper a b = if liftEq (\_ _ -> True) (project a) (project b)
  then embed $ fmap mergeSuper (project a) <*> (project b)
  else undefined
-}

data UnsizedRecursionF f
  = UnsizedRecursionF UnsizedRecursionToken
  | RecursionTestF UnsizedRecursionToken f
  | UnsizableF UnsizedRecursionToken -- TODO change to AbortedF ?
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data NaturalNumberF f
  = NatF Int
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (UnsizedRecursionF a, UnsizedRecursionF b) -> a == b
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    _                                          -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec showList prec x = case x of
    UnsizedRecursionF be -> shows "UnsizedRecursionF (" . shows be . shows ")"
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec 0 x . shows ")"

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
    DeferSF x  -> indentWithOneChild' "D" $ showP x
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
    UnsizedRecursionF (UnsizedRecursionToken ind) -> pure $ "?" <> show ind
    RecursionTestF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("T(" <> show ind <> ")") $ showP x
    UnsizableF ind -> pure $ "(unsizable) " <> show ind

instance PrettyPrintable1 NaturalNumberF where
  showP1 (NatF i) = pure $ "(" <> show i <> ")"

{-
instance (Show r, PrettyPrintable gx) => PrettyPrintable1 (StuckF r gx) where
  showP1 (StuckF r x) = indentWithOneChild' ("#(" <> show r <> ")") $ showP x
-}
instance (PrettyPrintable r, PrettyPrintable gx) => PrettyPrintable1 (StuckF r gx) where
  showP1 (StuckF r x) = showP r >>= (\s -> indentWithOneChild' s $ showP x)

{-
instance PrettyPrintable StuckNeedsEnv where
  showP _ = pure "#"

instance PrettyPrintable StuckNeedsSizing where
  showP _ = pure "%"
-}
{-
instance (PrettyPrintable s) => PrettyPrintable (SizeStuck s) where
  showP = \case
    Right _ -> pure "#"
    Left (Right _) -> pure "%"
-}

-- instance {-# Overlapping #-} (PrettyPrintable s) => PrettyPrintable (SetStuck s) where
instance {-# Overlapping #-} PrettyPrintable (SetStuck s) where
  showP = \case
    Right _ -> pure "#"
    _ -> pure "%"

instance PrettyPrintable Void where
  showP _ = error "Void should never be inhabited, so should not be PrettyPrintable"

instance PrettyPrintable1 VoidF where
  showP1 _ = error "VoidF should never be inhabited, so should not be PrettyPrintable1"

term3ToUnsizedExpr :: Term3 -> UnsizedExpr s f
term3ToUnsizedExpr (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag = \case
        ZeroFrag -> ZeroEE ZeroSF
        PairFrag a b -> ZeroEE $ PairSF (convertFrag a) (convertFrag b)
        EnvFrag -> ZeroEE EnvSF
        SetEnvFrag x -> ZeroEE . SetEnvSF $ convertFrag x
        DeferFrag ind -> ZeroEE . DeferSF . convertFrag . unFragExprUR $ fragLookup ind
        AbortFrag -> ThreeEE AbortF
        GateFrag l r -> ZeroEE $ GateSF (convertFrag l) (convertFrag r)
        LeftFrag x -> ZeroEE . LeftSF $ convertFrag x
        RightFrag x -> ZeroEE . RightSF $ convertFrag x
        TraceFrag -> ZeroEE EnvSF
        AuxFrag (RecursionTest tok (FragExprUR x)) -> FourEE . RecursionTestF tok $ convertFrag x
        AuxFrag (NestedSetEnvs x) -> EnhancedStuck (Left (Right StuckNeedsSizing)) .
          FourEE $ UnsizedRecursionF x
  in StuckExpr . convertFrag . unFragExprUR $ rootFrag termMap

unsizedTermToSizeTerm :: (PrettyPrintable1 f, Functor f) => StuckExpr (SizeStuck s) (StuckUnsizedBase f) -> SizeExpr
unsizedTermToSizeTerm = cata tr . unStuckExpr where
  tr = \case
    ZeroFW x -> case x of
      ZeroSF -> ZeroS
      PairSF a b -> PairS a b
      EnvSF -> EnvS
      SetEnvSF x -> SetEnvS x
      DeferSF x -> DeferS x
      GateSF l r -> GateS l r
      LeftSF x -> LeftS x
      RightSF x -> RightS x
    StuckFW (StuckF r (StuckExpr x)) -> case r of
      Left (Right StuckNeedsSizing) -> cata tr x
    ThreeFW x -> case x of
      AbortF -> AbortS
    FourFW x -> case x of
      RecursionTestF t x -> RecursionTestS t x
      UnsizedRecursionF t -> NestedSetEnvsS t EnvS
    z -> error (prettyPrint z)

instance PrettyPrintable SizeExpr where
  showP x = pure $ show x


sizeTermToUnsizedTerm :: Functor f => SizeExpr -> StuckExpr (SizeStuck s) (StuckUnsizedBase f)
sizeTermToUnsizedTerm = StuckExpr . ana tr where
  tr = \case
    ZeroS -> ZeroFW ZeroSF
    PairS a b -> ZeroFW $ PairSF a b
    EnvS -> ZeroFW EnvSF
    SetEnvS x -> ZeroFW $ SetEnvSF x
    DeferS x -> ZeroFW $ DeferSF x
    GateS l r -> ZeroFW $ GateSF l r
    LeftS x -> ZeroFW $ LeftSF x
    RightS x -> ZeroFW $ RightSF x
    AbortS -> ThreeFW AbortF
    RecursionTestS t x -> FourFW $ RecursionTestF t x
    NestedSetEnvsS t EnvS -> FourFW $ UnsizedRecursionF t

term3ToSizedExpr :: Term3 -> SizeExpr
term3ToSizedExpr (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag = \case
        ZeroFrag -> ZeroS
        PairFrag a b -> PairS (convertFrag a) (convertFrag b)
        EnvFrag -> EnvS
        SetEnvFrag x -> SetEnvS $ convertFrag x
        DeferFrag ind -> DeferS . convertFrag . unFragExprUR $ fragLookup ind
        AbortFrag -> AbortS
        GateFrag l r -> GateS (convertFrag l) (convertFrag r)
        LeftFrag x -> LeftS $ convertFrag x
        RightFrag x -> RightS $ convertFrag x
        TraceFrag -> EnvS
        AuxFrag (RecursionTest tok (FragExprUR x)) -> RecursionTestS tok $ convertFrag x
        AuxFrag (NestedSetEnvs t) -> NestedSetEnvsS t EnvS
  in convertFrag . unFragExprUR $ rootFrag termMap

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
sizeTerm recursionLimit = tidyUp . findSize . sizeF . unStuckExpr . evalPossibleTop . showBeginning where
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
    let sized = foldr combine (Left Nothing) . map (toTriple testG) . takeWhile (<= fromInteger recursionLimit) $ iterate (*2) 1 -- TODO relocate fromInteger
        testG = case x of -- hacky, to handle many situations
          ZeroEE (DeferSF _) -> ZeroEE $ FillFunction x (TwoEE AnyPF) -- from sizeF
          ZeroEE (PairSF d@(ZeroEE (DeferSF _)) _) -> ZeroEE $ FillFunction d (TwoEE AnyPF) -- compiling main
          _ -> ZeroEE $ FillFunction (ZeroEE (DeferSF x)) (TwoEE AnyPF) -- compiling test expression
        combine (n, ru, ra) alt = if not $ null ru
          then Left ru
          else if ra then alt else pure n
        toTriple x n = let evaled = setSizes n $ showSizingExpr testG in (n, recursionUnsizable evaled, recursionAborted evaled)
    in case sized of
      Left _  -> (tm, x)
      Right n -> (mempty, setSizes n x)
  tidyUp = \case
    (UnsizedAggregate uam, _) | not (null uam) -> case Map.minViewWithKey uam of
                                  Just ((urt, _), _) -> Left urt
    (_, x) -> pure . StuckExpr . clean $ x
  findBad :: (Functor f, PrettyPrintable1 f, Show s) =>
    EnhancedExpr
                        (SplitFunctor
                           (SplitFunctor
                              (SplitFunctor (SplitFunctor f UnsizedRecursionF) AbortableF)
                              SuperPositionF)
                           (StuckF
                              (SetStuck (Either s StuckNeedsSizing))
                              (StuckExpr
                                 (SetStuck (Either s StuckNeedsSizing))
                                 (SplitFunctor
                                    (SplitFunctor (SplitFunctor f UnsizedRecursionF) AbortableF)
                                    SuperPositionF))))
    -> EnhancedExpr
                        (SplitFunctor
                           (SplitFunctor (SplitFunctor f AbortableF) SuperPositionF) (StuckF
                              (SetStuck s)
                              (StuckExpr
                                 (SetStuck s)
                                 (SplitFunctor
                                    (SplitFunctor f AbortableF)
                                    SuperPositionF))))
  findBad = cata $ \case
    ZeroFW x  -> ZeroEE x
    OneFW (StuckF (Right StuckNeedsEnv) (StuckExpr x)) -> EnvStuck $ findBad x
    TwoFW x   -> TwoEE x
    ThreeFW x -> ThreeEE x
    z         -> error ("found bad thing: " <> prettyPrint z)
  clean = hoist $ \case
    ZeroFW x  -> ZeroFW x
    OneFW (StuckF (Right StuckNeedsEnv) (StuckExpr x)) -> OneFW (StuckF (Right StuckNeedsEnv) (StuckExpr $ clean x))
    TwoFW x   -> TwoFW x
    ThreeFW x -> ThreeFW x
    z         -> error "sizeTerm clean should be impossible"
  setSizes n = cata $ \case
    OneFW (StuckF (Left (Right StuckNeedsSizing)) (StuckExpr e)) -> evalPossible' $ setSizes n e
    OneFW (StuckF r (StuckExpr e)) -> OneEE (StuckF r (StuckExpr $ setSizes n e))
    FourFW (UnsizedRecursionF _) -> iterate (ZeroEE . SetEnvSF) (ZeroEE EnvSF) !! n
    x -> embed x
  recursionAborted = cata $ \case
    OneFW (StuckF _ (StuckExpr e))    -> recursionAborted e
    ThreeFW (AbortedF AbortRecursion) -> True
    x                                 -> getAny $ foldMap Any x
  recursionUnsizable = cata $ \case
    OneFW (StuckF _ (StuckExpr e)) -> recursionUnsizable e
    FourFW (RecursionTestF ri _)   -> Just ri  -- undispatched recursion tests mean unsizable
    FourFW (UnsizableF t)          -> Just t
    x                              -> foldr (<|>) empty x
  evalPossible = evalBottomUp (evalBasicDoNothing (evalSuper evalPossible (evalAbort (evalAnyFunction (evalRecursionTest evalPossible unhandledError)))))
  evalPossible' = unStuckExpr . evalPossible . StuckExpr
  evalPossibleTop = evalBottomUp (evalBasicDoNothing (evalAbort unhandledError))
  -- evalPossibleTop = evalBottomUp ZeroEE
  unhandledError :: (PrettyPrintable1 f) => PartExprF (EnhancedAbortStuck f s) -> EnhancedAbortStuck f s
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)
-}
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

instance TelomareLike (EnhancedExpr o) where
  fromTelomare = \case
    Zero     -> ZeroEE ZeroSF
    Pair a b -> ZeroEE $ PairSF (fromTelomare a) (fromTelomare b)
    Env      -> ZeroEE EnvSF
    SetEnv x -> ZeroEE $ SetEnvSF (fromTelomare x)
    Defer x  -> ZeroEE $ DeferSF (fromTelomare x)
    Gate l r -> ZeroEE $ GateSF (fromTelomare l) (fromTelomare r)
    PLeft x  -> ZeroEE $ LeftSF (fromTelomare x)
    PRight x -> ZeroEE $ RightSF (fromTelomare x)
    Trace    -> error "EnhancedExpr trace"
  toTelomare = \case
    ZeroEE x -> case x of
      ZeroSF     -> pure Zero
      PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
      EnvSF      -> pure Env
      SetEnvSF p -> SetEnv <$> toTelomare p
      DeferSF d  -> Defer <$> toTelomare d
      GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
      LeftSF x   -> PLeft <$> toTelomare x
      RightSF x  -> PRight <$> toTelomare x
    _ -> Nothing

instance TelomareLike SizeExpr where
  fromTelomare = \case
    Zero -> ZeroS
    Pair a b -> PairS (fromTelomare a) (fromTelomare b)
    Env -> EnvS
    SetEnv x -> SetEnvS $ fromTelomare x
    Defer x -> DeferS $ fromTelomare x
    Gate l r -> GateS (fromTelomare l) (fromTelomare r)
    PLeft x -> LeftS $ fromTelomare x
    PRight x -> RightS $ fromTelomare x
  toTelomare = \case
    ZeroS -> pure Zero
    PairS a b -> Pair <$> toTelomare a <*> toTelomare b
    EnvS -> pure Env
    SetEnvS x -> SetEnv <$> toTelomare x
    DeferS x -> Defer <$> toTelomare x
    GateS l r -> Gate <$> toTelomare l <*> toTelomare r
    LeftS x -> PLeft <$> toTelomare x
    RightS x -> PRight <$> toTelomare x
    _ -> Nothing

evalBU :: IExpr -> Maybe IExpr
evalBU = toIExpr . ebu . StuckExpr . fromTelomare where
  toIExpr = toTelomare . unStuckExpr
  ebu :: StuckExpr (SetStuck Void) VoidF -> StuckExpr (SetStuck Void) VoidF
  ebu = evalBottomUp ZeroEE

evalBU' :: IExpr -> IO IExpr
evalBU' = f . evalBU where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x

evalS' :: IExpr -> IO IExpr
evalS' = unM . toTelomare . evalS . fromTelomare where
  unM = \case
    Nothing -> pure Env
    Just x -> pure x

term4toAbortExpr :: Term4 -> AbortExpr s f
term4toAbortExpr (Term4 termMap) =
  let convertFrag = \case
        ZeroFrag      -> ZeroEE ZeroSF
        PairFrag a b  -> ZeroEE $ PairSF (convertFrag a) (convertFrag b)
        EnvFrag       -> ZeroEE EnvSF
        SetEnvFrag x  -> ZeroEE . SetEnvSF $ convertFrag x
        DeferFrag ind -> ZeroEE . DeferSF . convertFrag $ termMap Map.! ind
        AbortFrag     -> ThreeEE AbortF
        GateFrag l r  -> ZeroEE $ GateSF (convertFrag l) (convertFrag r)
        LeftFrag x    -> ZeroEE . LeftSF $ convertFrag x
        RightFrag x   -> ZeroEE . RightSF $ convertFrag x
        TraceFrag     -> ZeroEE EnvSF
        z             -> error ("term4toAbortExpr'' unexpected " <> show z)
  in StuckExpr $ convertFrag (rootFrag termMap)

abortExprToTerm4 :: (Show s, Show1 f, Functor f, Foldable f) => AbortExpr s f -> Either IExpr Term4
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
      ZeroFW (DeferSF x)  -> deferF x
      ThreeFW AbortF      -> pure AbortFrag
      ZeroFW (GateSF l r) -> GateFrag <$> l <*> r
      ZeroFW (LeftSF x)   -> LeftFrag <$> x
      ZeroFW (RightSF x)  -> RightFrag <$> x
      OneFW (StuckF (Right StuckNeedsEnv) (StuckExpr x)) -> cata convert x
      z                   -> error ("abortExprToTerm4 unexpected thing ") -- <> show (fmap (const ()) z))
  in case findAborted $ unStuckExpr x of
    Just e -> Left e
    _      -> pure . Term4 . buildFragMap . cata convert . unStuckExpr $ x

evalA :: (Maybe IExpr -> Maybe IExpr -> Maybe IExpr) -> Maybe IExpr -> Term4 -> Maybe IExpr
evalA combine base t =
  let initialEnv = TwoEE AnyPF
      unhandledError x = error ("evalA unhandled case " <> show x)
      runResult = let eval' :: AbortExpr Void VoidF -> AbortExpr Void VoidF
                      eval' = evalBottomUp (evalBasicDoNothing (evalSuper eval' (evalAbort unhandledError)))
                  in eval' . liftStuck deheadMain $ term4toAbortExpr t
      -- hack to check main functions as well as unit tests
      deheadMain = \case
        ZeroEE (PairSF (ZeroEE (DeferSF f)) _) -> f
        x                                      -> x
      getAborted = \case
        ThreeFW (AbortedF e) -> Just e
        TwoFW (EitherPF a b) -> combine a b
        x                    -> foldr (<|>) Nothing x
  in flip combine base . cata getAborted $ unStuckExpr runResult

-- type checking stuff in here, maybe replace old type checking eventually
data TypedF f
  = TypedF PartialType f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 TypedF where
  liftEq test (TypedF ta a) (TypedF tb b) = ta == tb && test a b

instance Show1 TypedF where
  liftShowsPrec showsPrec showList prec (TypedF t x) = shows "TypedF " . shows t . shows " (" . showsPrec 0 x . shows ")"

mergeSuperS :: SizeExpr -> SizeExpr -> SizeExpr
mergeSuperS a b = case (a, b) of
  (ZeroS, ZeroS) -> ZeroS
  (EnvS, EnvS) -> EnvS
  (PairS a b, PairS c d) | a == c -> PairS a $ mergeSuperS b d
  (PairS a b, PairS c d) | b == d -> PairS (mergeSuperS a c) b
  (SetEnvS x, SetEnvS y) -> SetEnvS $ mergeSuperS x y
  (DeferS x, DeferS y) -> DeferS $ mergeSuperS x y
  (GateS a b, GateS c d) | a == c -> GateS a $ mergeSuperS b d
  (GateS a b, GateS c d) | b == d -> GateS (mergeSuperS a c) b
  (LeftS x, LeftS y) -> LeftS $ mergeSuperS x y
  (RightS x, RightS y) -> RightS $ mergeSuperS x y
  (EitherS a b, EitherS c d) -> EitherS (mergeSuperS a c) (mergeSuperS b d)
  (AnyS, AnyS) -> AnyS
  (AbortS, AbortS) -> AbortS
  (AbortedS x, AbortedS y) | x == y -> AbortedS x
  -- (UnsizedRecursionS x, UnsizedRecursionS y) | x == y -> UnsizedRecursionS x
  (NestedSetEnvsS ta x, NestedSetEnvsS tb y) | ta == tb -> NestedSetEnvsS ta $ mergeSuperS x y
  (RecursionTestS ta x, RecursionTestS tb y) | ta == tb -> RecursionTestS ta $ mergeSuperS x y
  (r@(SizingResultsS (x:_)), SizingResultsS (y:_)) | x == y -> r
  (UnsizeableS ta, UnsizeableS tb) | ta == tb -> UnsizeableS ta
  _ -> EitherS a b

evalS :: SizeExpr -> SizeExpr
evalS = transform ev where
  ev = \case
    LeftS ZeroS -> ZeroS
    LeftS (PairS x _) -> x
    RightS ZeroS -> ZeroS
    RightS (PairS _ x) -> x
    GateSwitchS l _ ZeroS -> l
    GateSwitchS _ r (PairS _ _) -> r
    {-
    EnvS -> StuckEnvS EnvS
    LeftS (StuckEnvS x) -> StuckEnvS $ LeftS x
    RightS (StuckEnvS x) -> StuckEnvS $ RightS x
    SetEnvS (StuckEnvS x) -> StuckEnvS $ SetEnvS x
  -}
    FillFunctionS (DeferS d) e -> transform (ev . replaceEnv) d where
      replaceEnv = \case
        EnvS -> e
        x -> x
    -- super section
    LeftS AnyS -> AnyS
    LeftS (EitherS a b) -> mergeSuperS (ev $ LeftS a) (ev $ LeftS b)
    RightS AnyS -> AnyS
    RightS (EitherS a b) -> mergeSuperS (ev $ RightS a) (ev $ RightS b)
    SetEnvS (EitherS a b) -> mergeSuperS (ev $ SetEnvS a) (ev $ SetEnvS b)
    GateSwitchS l r AnyS -> EitherS l r
    -- GateSwitchS l r (EitherS a b) -> mergeSuperS (ev $ GateSwitchS l r a) (ev $ GateSwitchS l r b)
    FillFunctionS (EitherS ca cb) e -> mergeSuperS (ev $ FillFunctionS ca e) (ev $ FillFunctionS cb e)
    FillFunctionS c (EitherS ea eb) -> mergeSuperS (ev $ FillFunctionS c ea) (ev $ FillFunctionS c eb)
    -- abortable section
    LeftS (a@(AbortedS _)) -> a
    RightS (a@(AbortedS _)) -> a
    SetEnvS (a@(AbortedS _)) -> a
    FillFunctionS a@(AbortedS _) _ -> a
    FillFunctionS AbortS ZeroS -> DeferS EnvS
    FillFunctionS AbortS e@(PairS _ _) -> AbortedS $ trunc e where
      trunc = \case
        ZeroS -> Zero
        PairS a b -> Pair (trunc a) (trunc b)
        EitherS a _ -> trunc a
        AnyS -> Zero
        z -> error ("evalS FillFunction AbortS trunc, unexpected " <> show z)
    FillFunctionS AbortS AnyS -> AbortedS AbortAny
    -- sizing section
    NestedSetEnvsS _ x -> SizingResultsS $ iterate (ev . SetEnvS) x
    LeftS (SizingResultsS rl) -> SizingResultsS $ map (ev . LeftS) rl
    RightS (SizingResultsS rl) -> SizingResultsS $ map (ev . RightS) rl
    SetEnvS (SizingResultsS rl) -> SizingResultsS $ map (ev . SetEnvS) rl
    FillFunctionS (SizingResultsS rlc) (SizingResultsS rle) -> SizingResultsS [ev (FillFunctionS c e) | (c,e) <- zip rlc rle]
    FillFunctionS (SizingResultsS rl) e -> SizingResultsS $ map (ev . (\x -> FillFunctionS x e)) rl
    FillFunctionS c (SizingResultsS rl) -> SizingResultsS $ map (ev . FillFunctionS c) rl
    RecursionTestS _ ZeroS -> ZeroS
    RecursionTestS _ p@(PairS _ _) -> p
    RecursionTestS t AnyS -> UnsizeableS t
    RecursionTestS t (EitherS a b) -> EitherS (ev $ RecursionTestS t a) (ev $ RecursionTestS t b)
    RecursionTestS _ a@(AbortedS _) -> a
    RecursionTestS _ u@(UnsizeableS _) -> u
    -- eval any function
    FillFunctionS AnyS _ -> AnyS
    -- stuck expr
    x -> x
