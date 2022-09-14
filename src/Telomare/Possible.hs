{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
module Telomare.Possible where

import           Control.Applicative
import           Control.Lens.Plated
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
    x                   -> getAny $ foldMap Any x

data StuckF r g f
  = StuckF r g
  deriving (Functor, Foldable, Traversable)

instance (Show r, Show g) => Show1 (StuckF r g) where
  liftShowsPrec showsPrec showList prec (StuckF r x) = shows "StuckF (" . shows r . shows " - " . shows x . shows " )"

instance (Eq r, Eq g) => Eq1 (StuckF r g) where
  liftEq test (StuckF ra ga) (StuckF rb gb) = ra == rb && ga == gb

data StuckNeedsEnv = StuckNeedsEnv deriving (Eq, Show)

type SetStuck x = Either x StuckNeedsEnv

type StuckBase r g f = BasicBase (SplitFunctor f (StuckF r g))
newtype StuckExpr s f = StuckExpr { unStuckExpr :: EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f)))}
  deriving (Eq, Show)
pattern StuckFW :: StuckF r g a -> StuckBase r g f a
pattern StuckFW x = SplitFunctor (Left (SplitFunctor (Right x)))
pattern EnhancedStuck :: r -> EnhancedExpr (SplitFunctor f (StuckF r (StuckExpr r f)))
  -> EnhancedExpr (SplitFunctor f (StuckF r (StuckExpr r f)))
pattern EnhancedStuck r x = EnhancedExpr (StuckFW (StuckF r (StuckExpr x)))
pattern EnvStuck :: EnhancedExpr (SplitFunctor f (StuckF (SetStuck es) (StuckExpr (SetStuck es) f)))
  -> EnhancedExpr (SplitFunctor f (StuckF (SetStuck es) (StuckExpr (SetStuck es) f)))
pattern EnvStuck x = EnhancedStuck (Right StuckNeedsEnv) x

liftStuck :: (EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f)))
             -> EnhancedExpr (SplitFunctor f (StuckF s (StuckExpr s f))))
             -> StuckExpr s f -> StuckExpr s f
liftStuck f = StuckExpr . f . unStuckExpr

-- simplest eval rules
basicEval :: (PartExprF (EnhancedExpr o) -> EnhancedExpr o) -> (PartExprF (EnhancedExpr o) -> EnhancedExpr o)
basicEval handleOther = \case
    LeftSF (ZeroEE ZeroSF) -> ZeroEE ZeroSF
    LeftSF (ZeroEE (PairSF l _)) -> l
    RightSF (ZeroEE ZeroSF) -> ZeroEE ZeroSF
    RightSF (ZeroEE (PairSF _ r)) -> r
    SetEnvSF (ZeroEE (PairSF (ZeroEE (GateSF l _)) (ZeroEE (ZeroSF)))) -> l
    SetEnvSF (ZeroEE (PairSF (ZeroEE (GateSF _ r)) (ZeroEE (PairSF _ _)))) -> r
    x -> handleOther x

type EnhancedSetStuck f s = EnhancedExpr (SplitFunctor f (StuckF (SetStuck s) (StuckExpr (SetStuck s) f)))

evalBottomUp :: (Show so, Show1 o, Functor o) =>
  {-
  (PartExprF (EnhancedExpr (SplitFunctor o (StuckF (SetStuck so) (StuckExpr (SetStuck so) o))))
  -> EnhancedExpr (SplitFunctor o (StuckF (SetStuck so) (StuckExpr (SetStuck so) o)))
  ) ->
-}
  (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so) ->
  StuckExpr (SetStuck so) o -> StuckExpr (SetStuck so) o
evalBottomUp handleOther = StuckExpr . cata evalF . unStuckExpr where
  stepTrace x = trace ("step\n" <> show (PrettyStuckExpr . StuckExpr . embed $ x)) x
  recur = evalBottomUp handleOther
  evalS = \case
    EnvSF -> EnvStuck $ ZeroEE EnvSF
    LeftSF (EnhancedStuck r lx) -> EnhancedStuck r . ZeroEE . LeftSF $ lx
    RightSF (EnhancedStuck r rx) -> EnhancedStuck r . ZeroEE . RightSF $ rx
    SetEnvSF (ZeroEE (PairSF (ZeroEE (DeferSF d)) e)) -> cata runStuck d False where
      runStuck x underDefer = case x of
        StuckFW (StuckF (Right StuckNeedsEnv) (StuckExpr s)) -> if underDefer
          then embed . fmap ($ underDefer) $ x
          else unStuckExpr . recur . StuckExpr . (\rs -> cata runStuck rs False) $ s
        ZeroFW (DeferSF d) -> embed . ZeroFW . DeferSF $ d True
        ZeroFW EnvSF -> e
        x -> embed . fmap ($ underDefer) $ x
    SetEnvSF (ZeroEE (PairSF g@(ZeroEE (GateSF _ _)) (EnhancedStuck sr se))) ->
      EnhancedStuck sr . ZeroEE . SetEnvSF . ZeroEE $ PairSF g se
    SetEnvSF (ZeroEE (PairSF (EnhancedStuck sr sc) e)) ->
      EnhancedStuck sr . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc e
    SetEnvSF (EnhancedStuck sr sp) -> EnhancedStuck sr . ZeroEE . SetEnvSF $ sp
    SetEnvSF (ZeroEE (PairSF sc (EnvStuck e))) -> EnvStuck . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc e
    x -> handleOther x
  evalF = \case
    ZeroFW x -> basicEval evalS x
    x         -> embed x

evalBasicDoNothing :: (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so)
  -> (PartExprF (EnhancedSetStuck o so) -> EnhancedSetStuck o so)
evalBasicDoNothing handleOther x = let ex = ZeroEE x in case x of
  ZeroSF -> ex
  PairSF _ _ -> ex
  DeferSF _ -> ex
  GateSF _ _ -> ex
  _ -> handleOther x

type SuperExpr s f = StuckExpr (SetStuck s) (SplitFunctor f SuperPositionF)
type EnhancedSuperStuck f s = EnhancedSetStuck (SplitFunctor f SuperPositionF) s

evalSuper :: (Eq s, Show s, Eq1 f, Show1 f, Functor f) =>
  (StuckExpr (SetStuck s) (SplitFunctor f SuperPositionF) -> StuckExpr (SetStuck s) (SplitFunctor f SuperPositionF))
  -> (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
  -> (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
evalSuper recur handleOther =
  let rEval = unStuckExpr . recur . StuckExpr
  in \case
    LeftSF (TwoEE x) -> case x of
      AnyPF -> TwoEE AnyPF
      EitherPF a b -> mergeSuper' (rEval . ZeroEE . LeftSF $ a) (rEval . ZeroEE . LeftSF $ b)
    RightSF (TwoEE x) -> case x of
      AnyPF -> TwoEE AnyPF
      EitherPF a b -> mergeSuper' (rEval . ZeroEE . RightSF $ a) (rEval . ZeroEE . RightSF $ b)
    SetEnvSF (TwoEE (EitherPF a b)) -> mergeSuper' (rEval . ZeroEE . SetEnvSF $ a) (rEval . ZeroEE . SetEnvSF $ b)
    SetEnvSF (ZeroEE (PairSF (ZeroEE (GateSF l r)) se@(TwoEE _))) ->
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
            (Just ja, Just jb) -> pure $ mergeSuper' ja jb
            _                  -> a <|> b
      in case foldr combineOthers Nothing $ getPaths se of
        Nothing -> error "evalSuper gates getPaths should be impossible to have no alternatives"
        Just r -> r
    SetEnvSF (ZeroEE (PairSF (TwoEE (EitherPF sca scb)) se)) -> mergeSuper'
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF sca se)
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF scb se)
    SetEnvSF (ZeroEE (PairSF sc (TwoEE (EitherPF sea seb)))) -> mergeSuper'
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc sea)
      (rEval . ZeroEE . SetEnvSF . ZeroEE $ PairSF sc seb)
    x -> handleOther x

type AbortExpr s f = SuperExpr s (SplitFunctor f AbortableF)
type EnhancedAbortStuck f s = EnhancedSuperStuck (SplitFunctor f AbortableF) s

evalAbort :: (Show s, Show1 f, Functor f) => (PartExprF (EnhancedAbortStuck f s) -> EnhancedAbortStuck f s)
  -> (PartExprF (EnhancedAbortStuck f s) -> EnhancedAbortStuck f s)
evalAbort handleOther =
  \case
    LeftSF (a@(ThreeEE (AbortedF _))) -> a
    RightSF (a@(ThreeEE (AbortedF _))) -> a
    SetEnvSF (a@(ThreeEE (AbortedF _))) -> a
    SetEnvSF (ZeroEE (PairSF a@(ThreeEE (AbortedF _)) _)) -> a
    SetEnvSF (ZeroEE (PairSF _ a@(ThreeEE (AbortedF _)))) -> a
    SetEnvSF (ZeroEE (PairSF (ThreeEE AbortF) (ZeroEE ZeroSF))) -> ZeroEE . DeferSF . ZeroEE $ EnvSF
    SetEnvSF (ZeroEE (PairSF (ThreeEE AbortF) e@(ZeroEE (PairSF _ _)))) -> ThreeEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        ZeroFW ZeroSF -> Zero
        ZeroFW (PairSF a b) -> Pair a b
        TwoFW (EitherPF a _) -> a
        TwoFW AnyPF -> Zero
        z -> error ("evalAbort truncF unexpected thing")
    SetEnvSF (ZeroEE (PairSF (ThreeEE AbortF) (TwoEE AnyPF))) -> ThreeEE . AbortedF $ AbortAny
    x -> handleOther x

evalAnyFunction :: (Eq s, Show s, Eq1 f, Show1 f, Functor f)
  => (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
  -> (PartExprF (EnhancedSuperStuck f s) -> EnhancedSuperStuck f s)
evalAnyFunction handleOther =
  \case
    SetEnvSF (ZeroEE (PairSF (TwoEE AnyPF) _)) -> TwoEE AnyPF
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

mergeSuper' :: (Eq s, Eq1 f, Functor f) => EnhancedSuperStuck f s -> EnhancedSuperStuck f s -> EnhancedSuperStuck f s
mergeSuper' a b =
  let mergePart pa pb = case (pa,pb) of
        (ZeroSF, ZeroSF)                  -> pure ZeroSF
        (EnvSF, EnvSF)                    -> pure EnvSF
        (PairSF a b, PairSF c d) | a == c -> pure $ PairSF a (mergeSuper' b d)
        (PairSF a b, PairSF c d) | b == d -> pure $ PairSF (mergeSuper' a c) b
        (SetEnvSF x, SetEnvSF y)          -> pure $ SetEnvSF (mergeSuper' x y)
        (DeferSF x, DeferSF y)            -> pure $ DeferSF (mergeSuper' x y)
        (GateSF a b, GateSF c d) | a == c -> pure $ GateSF a (mergeSuper' b d)
        (GateSF a b, GateSF c d) | b == d -> pure $ GateSF (mergeSuper' a c) b
        (LeftSF x, LeftSF y)              -> pure $ LeftSF (mergeSuper' x y)
        (RightSF x, RightSF y)            -> pure $ RightSF (mergeSuper' x y)
        _                                 -> Left (pa, pb)
  in case (a,b) of
    (ZeroEE ba, ZeroEE bb) -> case mergePart ba bb of
      Right r       -> ZeroEE r
      Left (ea, eb) -> TwoEE $ EitherPF (ZeroEE ea) (ZeroEE eb)
    (TwoEE AnyPF, _) -> TwoEE AnyPF
    (_, TwoEE AnyPF) -> TwoEE AnyPF
    (TwoEE (EitherPF a b), TwoEE (EitherPF c d)) -> TwoEE $ EitherPF (mergeSuper' a c) (mergeSuper' b d)
    _ -> TwoEE $ EitherPF a b

data UnsizedRecursionF f
  = UnsizedRecursionF UnsizedRecursionToken
  | RecursionTestF UnsizedRecursionToken f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (UnsizedRecursionF a, UnsizedRecursionF b) -> a == b
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    _ -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec showList prec x = case x of
    UnsizedRecursionF be -> shows "UnsizedRecursionF (" . shows be . shows ")"
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec 0 x . shows ")"

type UnsizedExpr s f = AbortExpr s (SplitFunctor f UnsizedRecursionF)

newtype PrettyStuckExpr s o = PrettyStuckExpr (StuckExpr s o)

instance (Show s, Functor o) => Show (PrettyStuckExpr s o) where
  show (PrettyStuckExpr (StuckExpr x)) = State.evalState (cata alg $ x) 0 where
    alg = \case
      ZeroFW x -> case x of
        ZeroSF     -> pure "Z"
        PairSF a b -> indentWithTwoChildren' "P" a b
        EnvSF      -> pure "E"
        SetEnvSF x -> indentWithOneChild' "S" x
        DeferSF x  -> indentWithOneChild' "D" x
        GateSF l r -> indentWithTwoChildren' "G" l r
        LeftSF x   -> indentWithOneChild' "L" x
        RightSF x  -> indentWithOneChild' "R" x
      StuckFW (StuckF s (StuckExpr x)) -> indentWithOneChild' ("#" <> show s) $ cata alg x

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
        AuxFrag (NestedSetEnvs x) -> FourEE $ UnsizedRecursionF x
  in StuckExpr . convertFrag . unFragExprUR $ rootFrag termMap

{-
sizeTerm :: UnsizedExpr -> Maybe (AbortExpr VoidF)
sizeTerm term =
  let sizingTerm = eval term
      eval = evalEnhanced (handleSuper (handleAbort handleUnsized)) (SuperWrap AnyPF)
      collectUnsized :: UnsizedExpr -> [(UnsizedRecursionToken, UnsizedExpr)]
      collectUnsized x = case project x of
        UnsizedFW (UnsizedRecursionF b env) -> [(b,env)]
        x                                   -> foldMap collectUnsized x
      unsizedList = sortBy (\(_,aEnv) (_,bEnv) -> compare (Set.size $ getUnsized aEnv) (Set.size $ getUnsized bEnv)) $ collectUnsized sizingTerm
      setSizes test sizes = cata $ \case
        UnsizedFW (UnsizedRecursionF be env) -> trace ("unsized env is " <> show (PrettyUnsizedExpr env)) $ case Map.lookup be sizes of
          Just n -> iterate (ZeroEE . SetEnvSF) env !! n
          _ -> error ("sizeTerm setsizes ... somehow " <> show be <> " isn't present in size map")
        UnsizedFW (UnsizedBarrierF x) -> if test then eval x else x
        x -> embed x
      recursionAborted = \case
        AbortFW (AbortedF AbortRecursion)-> True
        x                                 -> getAny $ foldMap Any x
      sizeOptions (b,env) oldMap = do
        obe <- [0..8]
        c <- [0..8]
        let envSet = getUnsized env
        pure . Map.insert b (2 ^ c) $ Map.mapWithKey (\k v -> if Set.member k envSet then v ^ obe else v) oldMap
      sWrap (b,env) = UnsizedWrap (UnsizedBarrierF (UnsizedWrap (UnsizedRecursionF b env)))
      findSize oldMap (b,env) = lookup False . map (\m -> (cata recursionAborted . setSizes True m $ sWrap (b,env), m)) $ sizeOptions (b,env) oldMap
      clean = \case
        OneFW x -> OneFW x
        SuperFW x -> SuperFW x
        AbortFW x -> AbortFW x
        _ -> error "sizeTerm clean: should be impossible to see unsized recursion at this point"
      maybeMap = foldl' (\b a -> b >>= flip findSize a) (pure Map.empty) unsizedList
      maybeSized = trace ("sizeTerm final map: " <> show maybeMap) setSizes False <$> maybeMap <*> pure term
  in hoist clean <$> maybeSized
-}

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

{-
sizeTerm :: Integer -> UnsizedExpr' s f -> Either UnsizedRecursionToken (AbortExpr' Void VoidF)
sizeTerm recursionLimit = pure . liftStuck (hoist clean . snd . cata sizeF) where
  sizeF = \case
    ur@(FourFW (UnsizedRecursionF x)) -> (aggSetEnvs x, FourEE $ UnsizedRecursionF x)
    ur@(FourFW (RecursionTestF t (tm, x))) -> (aggTest t <> tm, FourEE $ RecursionTestF t x)
    ZeroFW (DeferSF (tm, x)) ->
      let sized = lookup False . map (\o -> (recursionAborted . setSizes o $ testG, o)) $ [1 .. fromInteger recursionLimit]
          testG = ZeroEE (PairSF (ZeroEE (DeferSF x)) (TwoEE AnyPF))
      in case sized of
        Nothing -> (tm, ZeroEE $ DeferSF x)
        Just n -> (mempty, )
  clean = \case
    ZeroFW x -> ZeroFW x
    OneFW x -> OneFW x
    TwoFW x -> TwoFW x
    ThreeFW x -> ThreeFW x
    _ -> error "sizeTerm clean should be impossible"
  setSizes n = cata $ \case
    FourFW (UnsizedRecursionF _) -> iterate (ZeroEE . SetEnvSF) (ZeroEE EnvSF) !! n
    x -> embed x
  recursionAborted = cata $ \case
    ThreeFW (AbortedF AbortRecursion) -> True
    x -> getAny $ foldMap Any x
  evalPossible = evalBottomUp (evalBasicDoNothing (evalSuper evalPossible (evalAbort (evalAnyFunction unhandledError))))
  unhandledError x = error ("sizeTerm unhandled case " <> show x)
-}


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

term4toAbortExpr :: Term4 -> AbortExpr s f
term4toAbortExpr (Term4 termMap) =
  let convertFrag = \case
        ZeroFrag -> ZeroEE ZeroSF
        PairFrag a b -> ZeroEE $ PairSF (convertFrag a) (convertFrag b)
        EnvFrag -> ZeroEE EnvSF
        SetEnvFrag x -> ZeroEE . SetEnvSF $ convertFrag x
        DeferFrag ind -> ZeroEE . DeferSF . convertFrag $ termMap Map.! ind
        AbortFrag -> ThreeEE AbortF
        GateFrag l r -> ZeroEE $ GateSF (convertFrag l) (convertFrag r)
        LeftFrag x -> ZeroEE . LeftSF $ convertFrag x
        RightFrag x -> ZeroEE . RightSF $ convertFrag x
        TraceFrag -> ZeroEE EnvSF
        z -> error ("term4toAbortExpr'' unexpected " <> show z)
  in StuckExpr $ convertFrag (rootFrag termMap)

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
        x                                            -> x
      getAborted = \case
        ThreeFW (AbortedF e) -> Just e
        TwoFW (EitherPF a b) -> combine a b
        x -> foldr (<|>) Nothing x
  in flip combine base . cata getAborted $ unStuckExpr runResult

-- type checking stuff in here, maybe replace old type checking eventually
data TypedF f
  = TypedF PartialType f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 TypedF where
  liftEq test (TypedF ta a) (TypedF tb b) = ta == tb && test a b

instance Show1 TypedF where
  liftShowsPrec showsPrec showList prec (TypedF t x) = shows "TypedF " . shows t . shows " (" . showsPrec 0 x . shows ")"
