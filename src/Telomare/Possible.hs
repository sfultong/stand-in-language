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
import           Telomare
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

type SimpleExpr = EnhancedExpr VoidF
type BasicBase f = SplitFunctor f PartExprF
type SuperBase f = BasicBase (SplitFunctor f SuperPositionF)
type AbortBase f = SuperBase (SplitFunctor f AbortableF)
type UnsizedBase = AbortBase UnsizedRecursionF

pattern BasicFW :: PartExprF a -> BasicBase f a
pattern BasicFW x = SplitFunctor (Right x)
pattern SuperFW :: SuperPositionF a -> SuperBase f a
pattern SuperFW x = SplitFunctor (Left (SplitFunctor (Right x)))
pattern AbortFW :: AbortableF a -> AbortBase f a
pattern AbortFW x = SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Right x)))))
pattern UnsizedFW :: UnsizedRecursionF a -> UnsizedBase a
pattern UnsizedFW x = SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left x)))))
pattern BasicExpr :: PartExprF (EnhancedExpr f) -> EnhancedExpr f
pattern BasicExpr x = EnhancedExpr (SplitFunctor (Right x))
pattern SuperWrap :: SuperPositionF (SuperExpr f) -> SuperExpr f
pattern SuperWrap x = EnhancedExpr (SplitFunctor (Left (SplitFunctor (Right x))))
pattern AbortWrap :: AbortableF (AbortExpr f) -> AbortExpr f
pattern AbortWrap x = EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Right x))))))
pattern UnsizedWrap :: UnsizedRecursionF UnsizedExpr -> UnsizedExpr
pattern UnsizedWrap x = EnhancedExpr (UnsizedFW x)

bareEnv :: (Functor f, Foldable f) => EnhancedExpr f -> Bool
bareEnv = cata bareF where
  bareF = \case
    BasicFW EnvSF       -> True
    BasicFW (DeferSF _) -> False
    x                   -> getAny $ foldMap Any x

evalEnhanced :: Functor o => (EnhancedExpr o -> PartExprF (EnhancedExpr o) -> EnhancedExpr o)
  -> EnhancedExpr o -> EnhancedExpr o -> EnhancedExpr o
evalEnhanced handleOther env (EnhancedExpr (SplitFunctor g)) =
  let recur = evalEnhanced handleOther env
  in case g of
    l@(Left _) -> EnhancedExpr $ SplitFunctor l
    Right r -> case fmap recur r of
      ZeroSF -> BasicExpr ZeroSF
      p@(PairSF _ _) -> BasicExpr p
      EnvSF -> env
      SetEnvSF x -> case x of
        BasicExpr (PairSF (BasicExpr cf) nenv) -> case cf of
          DeferSF c -> evalEnhanced handleOther nenv c
          GateSF l r -> case nenv of
            BasicExpr ZeroSF       -> recur l
            BasicExpr (PairSF _ _) -> recur r
            _                      -> handleOther env (SetEnvSF x)
          _ -> error "evalEnhanced shouldn't be here"
        _ -> handleOther env (SetEnvSF x)
      DeferSF _ -> BasicExpr r
      GateSF _ _ -> BasicExpr r
      LeftSF x -> case x of
        BasicExpr ZeroSF       -> BasicExpr ZeroSF
        BasicExpr (PairSF l _) -> l
        _                      -> handleOther env (LeftSF x)
      RightSF x -> case x of
        BasicExpr ZeroSF       -> BasicExpr ZeroSF
        BasicExpr (PairSF _ r) -> r
        _                      -> handleOther env (RightSF x)

{-
evalBottomUp :: Functor o => EnhancedExpr o -> EnhancedExpr o -> EnhancedExpr o
evalBottomUp env = cata evalF where
  evalF = \case
    BasicFW x -> case x of
      EnvSF -> env
      LeftSF lx -> case lx of
-}


data StuckF g f
  = StuckF g
  deriving (Functor, Foldable, Traversable)

instance Show g => Show1 (StuckF g) where
  liftShowsPrec showsPrec showList prec (StuckF x) = shows "StuckF (" . shows x . shows " )"

type StuckBase g f = BasicBase (SplitFunctor f (StuckF g))
newtype StuckExpr f = StuckExpr { unstuckExpr :: EnhancedExpr (SplitFunctor f (StuckF (StuckExpr f)))} deriving Show
pattern StuckFW :: StuckF g a -> StuckBase g f a
pattern StuckFW x = SplitFunctor (Left (SplitFunctor (Right x)))
pattern EnhancedStuck :: EnhancedExpr (SplitFunctor f (StuckF (StuckExpr f))) -> EnhancedExpr (SplitFunctor f (StuckF (StuckExpr f)))
pattern EnhancedStuck x = EnhancedExpr (StuckFW (StuckF (StuckExpr x)))

evalBottomUp :: (Show1 o, Functor o) => StuckExpr o -> StuckExpr o
evalBottomUp = StuckExpr . cata evalF . unstuckExpr where
  stepTrace x = trace ("step\n" <> show (PrettyStuckExpr . StuckExpr . embed $ x)) x
  evalF = \case
    BasicFW x -> case x of
      EnvSF -> EnhancedStuck $ BasicExpr EnvSF
      LeftSF x -> case x of
        BasicExpr ZeroSF       -> BasicExpr ZeroSF
        BasicExpr (PairSF l _) -> l
        EnhancedStuck lx       -> EnhancedStuck . BasicExpr . LeftSF $ lx
      RightSF x -> case x of
        BasicExpr ZeroSF       -> BasicExpr ZeroSF
        BasicExpr (PairSF _ r) -> r
        EnhancedStuck rx       -> EnhancedStuck . BasicExpr . RightSF $ rx
      SetEnvSF x -> case x of
        BasicExpr (PairSF c e) -> case c of
          BasicExpr bc -> case bc of
            DeferSF d -> cata runStuck d False where
              runStuck x underDefer = case x of
                StuckFW (StuckF (StuckExpr s)) -> if underDefer
                  then embed . fmap ($ underDefer) $ x
                  else unstuckExpr . evalBottomUp . StuckExpr . (\rs -> cata runStuck rs False) $ s
                BasicFW (DeferSF d) -> embed . BasicFW . DeferSF $ d True
                BasicFW EnvSF -> e
                x -> embed . fmap ($ underDefer) $ x
            GateSF l r -> case e of
              BasicExpr ZeroSF -> l
              BasicExpr (PairSF _ _) -> r
              EnhancedStuck se -> EnhancedStuck . BasicExpr . SetEnvSF . BasicExpr $ PairSF c se
            z -> error ("evalBottomUp setenv unexpected: " <> show z)
          EnhancedStuck sc -> EnhancedStuck . BasicExpr . SetEnvSF . BasicExpr $ PairSF sc e
        EnhancedStuck sp -> EnhancedStuck . BasicExpr . SetEnvSF $ sp
      x -> BasicExpr x
    x -> embed x

evalBottomUp' :: (Show1 o, Functor o, Traversable o) => StuckExpr o -> Maybe (StuckExpr o)
evalBottomUp' = liftM StuckExpr . cata evalF . unstuckExpr where
  evalF = \case
    BasicFW x -> case x of
      EnvSF -> pure . EnhancedStuck $ BasicExpr EnvSF
      LeftSF x -> x >>= \case
        BasicExpr ZeroSF       -> pure $ BasicExpr ZeroSF
        BasicExpr (PairSF l _) -> pure l
        EnhancedStuck lx       -> pure . EnhancedStuck . BasicExpr . LeftSF $ lx
      RightSF x -> x >>= \case
        BasicExpr ZeroSF       -> pure $ BasicExpr ZeroSF
        BasicExpr (PairSF _ r) -> pure r
        EnhancedStuck rx       -> pure . EnhancedStuck . BasicExpr . RightSF $ rx
      SetEnvSF x -> x >>= \case
        BasicExpr (PairSF c e) -> case c of
          BasicExpr bc -> case bc of
            DeferSF d -> pure $ cata runStuck d False where
              runStuck x underDefer = case x of
                StuckFW (StuckF (StuckExpr s)) -> if underDefer
                  then embed . fmap ($ underDefer) $ x
                  else unstuckExpr . evalBottomUp . StuckExpr . (\rs -> cata runStuck rs False) $ s
                BasicFW (DeferSF d) -> trace "under defer here" . embed . BasicFW . DeferSF $ d True
                BasicFW EnvSF -> e
                x -> embed . fmap ($ underDefer) $ x
            GateSF l r -> case e of
              BasicExpr ZeroSF -> pure l
              BasicExpr (PairSF _ _) -> pure r
              EnhancedStuck se -> pure . EnhancedStuck . BasicExpr . SetEnvSF . BasicExpr $ PairSF c se
            z -> Nothing
          EnhancedStuck sc -> pure . EnhancedStuck . BasicExpr . SetEnvSF . BasicExpr $ PairSF sc e
        EnhancedStuck sp -> pure . EnhancedStuck . BasicExpr . SetEnvSF $ sp
      x -> BasicExpr <$> sequence x
    x -> embed <$> sequence x

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

type SuperExpr f = EnhancedExpr (SplitFunctor f SuperPositionF)

superExtractOther :: SuperExpr f -> Either (f (SuperExpr f)) (SplitFunctor SuperPositionF PartExprF (SuperExpr f))
superExtractOther (EnhancedExpr (SplitFunctor x)) = case x of
  Left (SplitFunctor sx) -> case sx of
    Left ox   -> Left ox
    Right spx -> pure . SplitFunctor . Left $ spx
  Right rx -> pure . SplitFunctor . pure $ rx

mergeSuper :: Eq1 f => SuperExpr f -> SuperExpr f -> SuperExpr f
mergeSuper (EnhancedExpr (SplitFunctor a)) (EnhancedExpr (SplitFunctor b)) =
  let mergePart :: Eq1 f => PartExprF (SuperExpr f) -> PartExprF (SuperExpr f)
        -> Either (PartExprF (SuperExpr f), PartExprF (SuperExpr f)) (PartExprF (SuperExpr f))
      mergePart pa pb = case (pa, pb) of
        (ZeroSF, ZeroSF)                  -> pure ZeroSF
        (EnvSF, EnvSF)                    -> pure EnvSF
        (PairSF a b, PairSF c d) | a == c -> pure $ PairSF a (mergeSuper b d)
        (PairSF a b, PairSF c d) | b == d -> pure $ PairSF (mergeSuper a c) b
        (SetEnvSF x, SetEnvSF y)          -> pure $ SetEnvSF (mergeSuper x y)
        (DeferSF x, DeferSF y)            -> pure $ DeferSF (mergeSuper x y)
        (GateSF a b, GateSF c d) | a == c -> pure $ GateSF a (mergeSuper b d)
        (GateSF a b, GateSF c d) | b == d -> pure $ GateSF (mergeSuper a c) b
        (LeftSF x, LeftSF y)              -> pure $ LeftSF (mergeSuper x y)
        (RightSF x, RightSF y)            -> pure $ RightSF (mergeSuper x y)
        _                                 -> Left (pa, pb)
      superWrap = EnhancedExpr . SplitFunctor . Left . SplitFunctor . Right
      eitherWrap ea eb = superWrap $ EitherPF ea eb
  in case (a,b) of
    (Right pa, Right pb) -> case mergePart pa pb of
      Right r       -> BasicExpr r
      Left (ea, eb) -> eitherWrap (BasicExpr ea) (BasicExpr eb)
    (Left (SplitFunctor (Right AnyPF)), _) -> superWrap AnyPF
    (_, Left (SplitFunctor (Right AnyPF))) -> superWrap AnyPF
    (Left (SplitFunctor (Right sa)), Left (SplitFunctor (Right sb))) -> case (sa,sb) of
       (EitherPF a b, EitherPF c d) -> eitherWrap (mergeSuper a c) (mergeSuper b d)
       _ -> eitherWrap (EnhancedExpr $ SplitFunctor a) (EnhancedExpr $ SplitFunctor b)
    _ -> eitherWrap (EnhancedExpr $ SplitFunctor a) (EnhancedExpr $ SplitFunctor b)

handleSuper :: (Functor f, Eq1 f, Show1 f) => (SuperExpr f -> PartExprF (SuperExpr f) -> SuperExpr f)
  -> SuperExpr f -> PartExprF (SuperExpr f) -> SuperExpr f
handleSuper handleOther env term =
  let wrapS = EnhancedExpr . SplitFunctor . Left . SplitFunctor . Right
      recur = handleSuper handleOther env
      evalE = evalEnhanced (handleSuper handleOther)
      basicEval = evalE env . BasicExpr
  in case traverse superExtractOther term of
    Left _ -> handleOther env term
    Right extracted -> case extracted of
      LeftSF (SplitFunctor (Left x)) -> case x of
        AnyPF -> wrapS AnyPF
        EitherPF a b -> mergeSuper (basicEval . LeftSF $ a) (basicEval . LeftSF $ b)
      RightSF (SplitFunctor (Left x)) -> case x of
        AnyPF -> wrapS AnyPF
        EitherPF a b -> mergeSuper (basicEval . RightSF $ a) (basicEval . RightSF $ b)
      SetEnvSF (SplitFunctor sf) -> case sf of
        Left (EitherPF pa pb) -> mergeSuper (recur $ SetEnvSF pa) (recur $ SetEnvSF pb)
        Right (PairSF (EnhancedExpr (SplitFunctor sc)) se) -> case sc of
          Right (GateSF l r) ->
            let getPaths = \case
                  BasicExpr ZeroSF -> [Just leftPath, Nothing, Nothing]
                  BasicExpr (PairSF _ _) -> [Nothing, Just rightPath, Nothing]
                  SuperWrap x -> case x of
                    AnyPF -> [Just leftPath, Just rightPath, Nothing]
                    EitherPF a b -> (\[la,ra,oa] [lb,rb,ob] -> [la <|> lb, ra <|> rb, combineOthers oa ob])
                      (getPaths a) (getPaths b)
                  o@(EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left _))))) ->
                    [Nothing, Nothing
                    , pure $ handleOther env (SetEnvSF (BasicExpr (PairSF (EnhancedExpr (SplitFunctor sc)) o)))
                    ]
                combineOthers a b = case (a,b) of
                  (Just ja, Just jb) -> pure $ mergeSuper ja jb
                  _                  -> a <|> b
                leftPath = evalE env l
                rightPath = evalE env r
            in case foldr combineOthers Nothing $ getPaths se of
              Nothing -> error "handleSuper gates should be impossible to have no alternatives"
              Just r -> r
          Left (SplitFunctor scx) -> case scx of
            Left _ -> handleOther env term
            Right (EitherPF sca scb) -> mergeSuper (evalE se sca) (evalE se scb)
            z -> error ("handleSuper setEnv pair unexpected other scx " <> show sf)
          z -> error ("handleSuper setEnv pair unexpected sc " <> show sf)
        z -> error ("handleSuper setEnv unexpected " <> show sf)

type AbortExpr f = SuperExpr (SplitFunctor f AbortableF)

abortExtractOther :: AbortExpr f -> Either (f (AbortExpr f)) (SplitFunctor (SplitFunctor AbortableF SuperPositionF) PartExprF (AbortExpr f))
abortExtractOther (EnhancedExpr (SplitFunctor x)) = case x of
  Left (SplitFunctor sp) -> case sp of
    Left (SplitFunctor sa) -> case sa of
      Left o  -> Left o
      Right a -> pure . SplitFunctor . Left . SplitFunctor . Left $ a
    Right spx -> pure . SplitFunctor . Left . SplitFunctor . pure $ spx
  Right rx -> pure . SplitFunctor . pure $ rx

handleAbort :: (Functor f, Eq1 f, Show1 f) => (AbortExpr f -> PartExprF (AbortExpr f) -> AbortExpr f)
  -> AbortExpr f -> PartExprF (AbortExpr f) -> AbortExpr f
handleAbort handleOther env term =
  let wrapA = EnhancedExpr . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Right
      recur = handleAbort handleOther env
      truncateExp = cata truncA where
        truncA (SplitFunctor bs) = case bs of
          Right b -> case b of
            ZeroSF     -> Zero
            PairSF a b -> Pair a b
          Left (SplitFunctor ss) -> case ss of
            Right s -> case s of
              AnyPF        -> Zero
              EitherPF a _ -> a
            _ -> Zero
  in case traverse abortExtractOther term of
    Left _ -> handleOther env term
    Right extracted -> case extracted of
      LeftSF (SplitFunctor (Left (SplitFunctor (Left a@(AbortedF _))))) -> wrapA a
      RightSF (SplitFunctor (Left (SplitFunctor (Left a@(AbortedF _))))) -> wrapA a
      SetEnvSF (SplitFunctor p) -> case p of
        Left (SplitFunctor as) -> case as of
          Left a@(AbortedF _) -> wrapA a
          -- Right (EitherPF a b) -> mergeSuper (recur $ SetEnvSF a) (recur $ SetEnvSF b)
          Right (EitherPF a b) -> error "handleAbort setenv either ... I thought this should be handled by handleSuper"
        Right (PairSF sc se) -> case sc of
          BasicExpr (GateSF _ _) -> case se of
            (EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left _))))))) -> handleOther env term
            AbortWrap a@(AbortedF _) -> AbortWrap a
          (EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left _))))))) -> handleOther env term
          AbortWrap ax -> case ax of
            AbortF ->
              let testAbort (EnhancedExpr (SplitFunctor sse)) = case sse of
                    Right bse -> case bse of
                      ZeroSF -> BasicExpr . DeferSF . BasicExpr $ EnvSF
                      e      -> wrapA . AbortedF . truncateExp . BasicExpr $ e
                    Left (SplitFunctor sse) -> case sse of
                      Right ssse -> case ssse of
                        AnyPF -> wrapA . AbortedF $ AbortAny
                        EitherPF a b -> SuperWrap $ EitherPF (testAbort a) (testAbort b)
                      Left (SplitFunctor ase) -> case ase of
                        Right a@(AbortedF _) -> wrapA a
                        Left z -> handleOther env $ SetEnvSF (BasicExpr (PairSF (AbortWrap AbortF) se))
              in testAbort se
            alreadyAborted -> wrapA alreadyAborted
        z -> error ("unimplemented handleAbort for " <> show z)

data UnsizedRecursionF f
  = UnsizedRecursionF BreakExtras f
  -- | UnsizedBarrierF (Set BreakExtras) f -- probably doesn't need set here
  | UnsizedBarrierF f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (UnsizedRecursionF a _, UnsizedRecursionF b _) -> a == b
    (UnsizedBarrierF fa, UnsizedBarrierF fb)       -> test fa fb
    _                                              -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec showList prec x = case x of
    UnsizedRecursionF be env -> shows "UnsizedRecursionF (" . shows be . shows " " . showsPrec 0 env . shows ")"
    UnsizedBarrierF f -> shows "UnsizedBarrierF (" . showsPrec 0 f . shows ")"

type UnsizedExpr = AbortExpr UnsizedRecursionF

newtype PrettyUnsizedExpr = PrettyUnsizedExpr UnsizedExpr

instance Show PrettyUnsizedExpr where
  show (PrettyUnsizedExpr x) = State.evalState (cata alg $ x) 0 where
    alg = \case
      BasicFW x -> case x of
        ZeroSF     -> sindent "Z"
        PairSF a b -> indentWithTwoChildren "P" a b
        EnvSF      -> sindent "E"
        SetEnvSF x -> indentWithOneChild "S" x
        DeferSF x  -> indentWithOneChild "D" x
        GateSF l r -> indentWithTwoChildren "G" l r
        LeftSF x   -> indentWithOneChild "L" x
        RightSF x  -> indentWithOneChild "R" x
      SuperFW x -> case x of
        EitherPF a b -> indentWithTwoChildren "%" a b
        AnyPF        -> sindent "A"
      AbortFW x -> case x of
        AbortF     -> sindent "@"
        AbortedF m -> sindent ("!(" <> show m <> ")")
      UnsizedFW x -> case x of
        UnsizedRecursionF be ux -> indentWithOneChild ("U(" <> show be <> ")") ux
        UnsizedBarrierF ux -> indentWithOneChild "B" ux

newtype PrettyStuckExpr o = PrettyStuckExpr (StuckExpr o)

instance Functor o => Show (PrettyStuckExpr o) where
  show (PrettyStuckExpr (StuckExpr x)) = State.evalState (cata alg $ x) 0 where
    alg = \case
      BasicFW x -> case x of
        ZeroSF     -> pure "Z"
        PairSF a b -> indentWithTwoChildren' "P" a b
        EnvSF      -> pure "E"
        SetEnvSF x -> indentWithOneChild' "S" x
        DeferSF x  -> indentWithOneChild' "D" x
        GateSF l r -> indentWithTwoChildren' "G" l r
        LeftSF x   -> indentWithOneChild' "L" x
        RightSF x  -> indentWithOneChild' "R" x
      StuckFW (StuckF (StuckExpr x)) -> indentWithOneChild' "#" $ cata alg x

getUnsized :: UnsizedExpr -> Set BreakExtras
{-
getUnsized (EnhancedExpr x) = case x of
  UnsizedFW (UnsizedBarrierF s _) -> s
  _ -> foldMap getUnsized x
-}
getUnsized = cata sizeF where
  sizeF = \case
    UnsizedFW (UnsizedRecursionF be s) -> Set.insert be s
    x                                  -> Data.Foldable.fold x

handleUnsized :: UnsizedExpr -> PartExprF UnsizedExpr -> UnsizedExpr
handleUnsized env term =
  let makeBarrier = UnsizedWrap . UnsizedBarrierF . BasicExpr
  in case term of
    LeftSF (UnsizedWrap x) -> case x of
      UnsizedRecursionF be _ -> makeBarrier . LeftSF . UnsizedWrap $ UnsizedRecursionF be env
      UnsizedBarrierF x -> UnsizedWrap . UnsizedBarrierF . BasicExpr . LeftSF $ x
    RightSF (UnsizedWrap x) -> case x of
      UnsizedRecursionF be _ -> makeBarrier . RightSF . UnsizedWrap $ UnsizedRecursionF be env
      UnsizedBarrierF x -> UnsizedWrap . UnsizedBarrierF . BasicExpr . RightSF $ x
    SetEnvSF x -> case x of
      UnsizedWrap ux -> case ux of
        UnsizedRecursionF be _ -> makeBarrier . SetEnvSF . UnsizedWrap $ UnsizedRecursionF be env
        UnsizedBarrierF x -> UnsizedWrap . UnsizedBarrierF . BasicExpr . SetEnvSF $ x
      BasicExpr (PairSF uc ue) -> case uc of
        g@(BasicExpr (GateSF _ _)) -> case ue of
          UnsizedWrap (UnsizedRecursionF be _) -> makeBarrier . SetEnvSF . BasicExpr . PairSF g $ UnsizedWrap (UnsizedRecursionF be env)
          UnsizedWrap (UnsizedBarrierF uex) -> UnsizedWrap . UnsizedBarrierF . BasicExpr . SetEnvSF . BasicExpr $ PairSF g uex
        a@(AbortWrap AbortF) -> case ue of
          UnsizedWrap (UnsizedRecursionF be _) -> makeBarrier . SetEnvSF . BasicExpr . PairSF a $ UnsizedWrap (UnsizedRecursionF be env)
          UnsizedWrap (UnsizedBarrierF uex) -> UnsizedWrap . UnsizedBarrierF . BasicExpr . SetEnvSF . BasicExpr $ PairSF a uex
        UnsizedWrap ucx -> case ucx of
          --UnsizedRecursionF be _ -> makeBarrier . SetEnvSF . BasicExpr $ PairSF (UnsizedRecursionF) -- should be impossible
          UnsizedBarrierF x -> UnsizedWrap . UnsizedBarrierF . BasicExpr . SetEnvSF . BasicExpr $ PairSF x ue

term3ToUnsizedExpr :: Term3 -> UnsizedExpr
term3ToUnsizedExpr (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      convertFrag = \case
        ZeroFrag -> BasicExpr ZeroSF
        PairFrag a b -> BasicExpr $ PairSF (convertFrag a) (convertFrag b)
        EnvFrag -> BasicExpr EnvSF
        SetEnvFrag x -> BasicExpr . SetEnvSF $ convertFrag x
        DeferFrag ind -> BasicExpr . DeferSF . convertFrag $ fragLookup ind
        AbortFrag -> EnhancedExpr . AbortFW $ AbortF
        GateFrag l r -> BasicExpr $ GateSF (convertFrag l) (convertFrag r)
        LeftFrag x -> BasicExpr . LeftSF $ convertFrag x
        RightFrag x -> BasicExpr . RightSF $ convertFrag x
        TraceFrag -> BasicExpr EnvSF
        AuxFrag x -> EnhancedExpr . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Left $ UnsizedRecursionF x (BasicExpr EnvSF)
  in convertFrag $ rootFrag termMap

abortExprToFragMap :: AbortExpr a -> Map FragIndex (FragExpr b)
abortExprToFragMap expr =
  let build = \case
        BasicExpr x -> case x of
          ZeroSF     -> pure ZeroFrag
          PairSF a b -> PairFrag <$> build a <*> build b
          EnvSF      -> pure EnvFrag
          SetEnvSF x -> SetEnvFrag <$> build x
          DeferSF x  -> deferF $ build x
          GateSF l r -> GateFrag <$> build l <*> build r
          LeftSF x   -> LeftFrag <$> build x
          RightSF x  -> RightFrag <$> build x
        AbortWrap x -> case x of
          AbortF -> pure AbortFrag
        _ -> error "abortExprToFragMap unexpected stuff in AbortExpr"
  in buildFragMap (build expr)

unsizedExprToFragMap :: UnsizedExpr -> Map FragIndex (FragExpr BreakExtras)
unsizedExprToFragMap expr =
  let build = \case
        BasicExpr x -> case x of
          ZeroSF     -> pure ZeroFrag
          PairSF a b -> PairFrag <$> build a <*> build b
          EnvSF      -> pure EnvFrag
          SetEnvSF x -> SetEnvFrag <$> build x
          DeferSF x  -> deferF $ build x
          GateSF l r -> GateFrag <$> build l <*> build r
          LeftSF x   -> LeftFrag <$> build x
          RightSF x  -> RightFrag <$> build x
        AbortWrap x -> case x of
          AbortF -> pure AbortFrag
        EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (UnsizedRecursionF i _))))))) -> pure $ AuxFrag i
        _ -> error "unsizedExprToFragMap unexpected stuff in expr"
  in buildFragMap (build expr)

abortExprToTerm4 :: AbortExpr VoidF -> Term4
abortExprToTerm4 = Term4 . abortExprToFragMap

{-
sizeTerm :: UnsizedExpr -> Maybe (AbortExpr VoidF)
sizeTerm term = hoist clean <$> findSize 10 (cata sizeA $ annotateP term) where
  clean = \case
    BasicFW x -> BasicFW x
    SuperFW x -> SuperFW x
    AbortFW x -> AbortFW x
    _ -> error "sizeTerm clean: should be impossible to see unsized recursion at this point"
  sizeA :: AbortBase (SplitFunctor TypedF UnsizedRecursionF) TypeAnnotatedExpr -> TypeAnnotatedExpr
  sizeA = \case
    s@(SplitFunctor (Right (SetEnvSF sx))) -> if cleanApplication sx
                      then case findSize 8 (trace ("sizeTerm finding size of " <> show s) embed s) of
                             Nothing -> trace "failed to assess clean function" embed s -- can't resolve yet
                             Just x -> trace "succeeded in finding limit in sizeA" x
                      else embed s -- if calculation relies on or returns a function, ignore for now
    x -> embed x
  cleanApplication = \case
    EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (TypedF t x))))))))) ->
      case t of
        PairTypeP (ArrTypeP _ o) _ -> not (containsFunction o || bareEnv x)
  findSize limit term = let iterAmounts = take limit $ iterate (*2) 1
                            options = map (\i -> cata (setSize i) term) iterAmounts
                        in lookup False $ map (\x -> trace ("eval result is " <> show (eval x)) (cata recursionAborted $ eval x, x)) options
  eval = evalEnhanced (handleSuper (handleAbort undefined)) (SuperWrap AnyPF)
  setSize :: Int -> AbortBase (SplitFunctor TypedF UnsizedRecursionF) TypeAnnotatedExpr -> TypeAnnotatedExpr
  setSize n = \case
    SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Right (UnsizedRecursionF _ _)))))))) ->
      iterate (BasicExpr . SetEnvSF) (BasicExpr EnvSF) !! n
    SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (TypedF _ x)))))))) -> x
    x -> embed x
  recursionAborted = \case
    AbortFW (AbortedF AbortRecursion)-> True
    x -> getAny $ foldMap Any x
-}

sizeTerm :: UnsizedExpr -> Maybe (AbortExpr VoidF)
sizeTerm term =
  let sizingTerm = eval term
      eval = evalEnhanced (handleSuper (handleAbort handleUnsized)) (SuperWrap AnyPF)
      collectUnsized :: UnsizedExpr -> [(BreakExtras, UnsizedExpr)]
      collectUnsized x = case project x of
        UnsizedFW (UnsizedRecursionF b env) -> [(b,env)]
        x                                   -> foldMap collectUnsized x
      unsizedList = sortBy (\(_,aEnv) (_,bEnv) -> compare (Set.size $ getUnsized aEnv) (Set.size $ getUnsized bEnv)) $ collectUnsized sizingTerm
      setSizes test sizes = cata $ \case
        UnsizedFW (UnsizedRecursionF be env) -> trace ("unsized env is " <> show (PrettyUnsizedExpr env)) $ case Map.lookup be sizes of
          Just n -> iterate (BasicExpr . SetEnvSF) env !! n
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
        BasicFW x -> BasicFW x
        SuperFW x -> SuperFW x
        AbortFW x -> AbortFW x
        _ -> error "sizeTerm clean: should be impossible to see unsized recursion at this point"
      maybeMap = foldl' (\b a -> b >>= flip findSize a) (pure Map.empty) unsizedList
      maybeSized = trace ("sizeTerm final map: " <> show maybeMap) setSizes False <$> maybeMap <*> pure term
  in hoist clean <$> maybeSized

{-
data BottomUpResult a
  = BasicResult a
  | FunctionResult (a -> a)
  deriving (Eq, Ord, Show, Functor)
-}


instance TelomareLike (EnhancedExpr o) where
  fromTelomare = \case
    Zero     -> BasicExpr ZeroSF
    Pair a b -> BasicExpr $ PairSF (fromTelomare a) (fromTelomare b)
    Env      -> BasicExpr EnvSF
    SetEnv x -> BasicExpr $ SetEnvSF (fromTelomare x)
    Defer x  -> BasicExpr $ DeferSF (fromTelomare x)
    Gate l r -> BasicExpr $ GateSF (fromTelomare l) (fromTelomare r)
    PLeft x  -> BasicExpr $ LeftSF (fromTelomare x)
    PRight x -> BasicExpr $ RightSF (fromTelomare x)
    Trace    -> error "EnhancedExpr trace"
  toTelomare = \case
    BasicExpr x -> case x of
      ZeroSF     -> pure Zero
      PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
      EnvSF      -> pure Env
      SetEnvSF p -> SetEnv <$> toTelomare p
      DeferSF d  -> Defer <$> toTelomare d
      GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
      LeftSF x   -> PLeft <$> toTelomare x
      RightSF x  -> PRight <$> toTelomare x
    _ -> Nothing

evalS :: IExpr -> Maybe IExpr
evalS = toTelomare . evalEnhanced handleOther (BasicExpr ZeroSF). fromTelomare where
  handleOther :: EnhancedExpr Maybe -> PartExprF (EnhancedExpr Maybe) -> EnhancedExpr Maybe
  handleOther = error "TODO evalS handleOther"

evalS' :: IExpr -> IO IExpr
evalS' = f . evalS where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x

evalBU :: IExpr -> Maybe IExpr
evalBU = toIExpr . ebu . StuckExpr . fromTelomare where
  toIExpr = (>>= (toTelomare . unstuckExpr))
  ebu :: StuckExpr VoidF -> Maybe (StuckExpr VoidF)
  -- ebu = evalBottomUp
  ebu = evalBottomUp'

evalBU' :: IExpr -> IO IExpr
evalBU' = f . evalBU where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x

term4ToAbortExpr :: Term4 -> AbortExpr VoidF
term4ToAbortExpr (Term4 termMap) =
  let fragLookup = (termMap Map.!)
  in term4ToAbortExpr' fragLookup (rootFrag termMap)

term4ToAbortExpr' :: (FragIndex -> FragExpr a) -> FragExpr a -> AbortExpr VoidF
term4ToAbortExpr' fragLookup frag =
  let convertFrag = \case
        ZeroFrag -> BasicExpr ZeroSF
        PairFrag a b -> BasicExpr $ PairSF (convertFrag a) (convertFrag b)
        EnvFrag -> BasicExpr EnvSF
        SetEnvFrag x -> BasicExpr . SetEnvSF $ convertFrag x
        DeferFrag ind -> BasicExpr . DeferSF . convertFrag $ fragLookup ind
        AbortFrag -> EnhancedExpr . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Right $ AbortF
        GateFrag l r -> BasicExpr $ GateSF (convertFrag l) (convertFrag r)
        LeftFrag x -> BasicExpr . LeftSF $ convertFrag x
        RightFrag x -> BasicExpr . RightSF $ convertFrag x
        TraceFrag -> BasicExpr EnvSF
        _ -> error "term4ToAbortExpr' should be impossible"
  in convertFrag frag

evalA :: (Maybe IExpr -> Maybe IExpr -> Maybe IExpr) -> Maybe IExpr -> Term4 -> Maybe IExpr
evalA combine base t =
  let initialEnv = SuperWrap AnyPF
      runResult = evalEnhanced (handleSuper (handleAbort undefined)) initialEnv . deheadMain $ term4ToAbortExpr t
      -- hack to check main functions as well as unit tests
      deheadMain = \case
        BasicExpr (PairSF (BasicExpr (DeferSF f)) _) -> f
        x                                            -> x
      getAborted = \case
        SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Right (AbortedF e)))))) -> Just e
        SplitFunctor (Left (SplitFunctor (Right (EitherPF a b)))) -> combine a b
        x -> foldr (<|>) Nothing x
  in flip combine base $ cata getAborted runResult

-- type checking stuff in here, maybe replace old type checking eventually
data TypedF f
  = TypedF PartialType f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq1 TypedF where
  liftEq test (TypedF ta a) (TypedF tb b) = ta == tb && test a b

instance Show1 TypedF where
  liftShowsPrec showsPrec showList prec (TypedF t x) = shows "TypedF " . shows t . shows " (" . showsPrec 0 x . shows ")"

type TypeAnnotatedExpr = AbortExpr (SplitFunctor TypedF UnsizedRecursionF)

annotateP :: UnsizedExpr -> TypeAnnotatedExpr
annotateP expr =
  let annoF = \case -- TODO delete or figure out why (cata annoF) does not match annoF'
        BasicFW x -> case x of
          ZeroSF -> pure (ZeroTypeP, BasicExpr ZeroSF)
          PairSF a b -> do
            (ta, ga) <- a
            (tb, gb) <- b
            pure (PairTypeP ta tb, BasicExpr $ PairSF ga gb)
          EnvSF -> State.gets (\(t, _, _) -> (t, BasicExpr EnvSF))
          SetEnvSF x -> do
            (tx, gx) <- x
            (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
            associateVar (PairTypeP (ArrTypeP it ot) it) tx
            pure (ot, BasicExpr . SetEnvSF . typeWrap tx $ gx)
          DeferSF x -> do
            (tx, gx) <- x
            (it, _, _) <- State.get
            _ <- newEnv -- increment env variable
            pure (ArrTypeP it tx, BasicExpr . DeferSF $ gx)
          GateSF l r -> do
            (tl, gl) <- l
            (tr, gr) <- r
            associateVar tl tr
            pure (ArrTypeP ZeroTypeP tl, BasicExpr $ GateSF gl gr)
          LeftSF x -> do
            (tx, gx) <- x
            (lt, _) <- withNewEnv $ pure ()
            associateVar (PairTypeP lt AnyType) tx
            pure (lt, BasicExpr . LeftSF $ gx)
          RightSF x -> do
            (tx, gx) <- x
            (rt, _) <- withNewEnv $ pure ()
            associateVar (PairTypeP AnyType rt) tx
            pure (rt, BasicExpr . RightSF $ gx)
        AbortFW AbortF -> do
          (it, _) <- withNewEnv $ pure ()
          pure (ArrTypeP ZeroTypeP (ArrTypeP it it), AbortWrap AbortF)
        SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (UnsizedRecursionF nr ox)))))) -> do
          (_, x) <- ox
          State.gets (\(t, _, _) -> (t, EnhancedExpr . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Right
                                      $ UnsizedRecursionF nr x))
      typeWrap t = EnhancedExpr . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Left . TypedF t
      annoF' = \case
        BasicExpr x -> case x of
          ZeroSF -> pure (ZeroTypeP, BasicExpr $ ZeroSF)
          PairSF a b -> do
            (ta, ga) <- annoF' a
            (tb, gb) <- annoF' b
            pure (PairTypeP  ta tb, BasicExpr $ PairSF ga gb)
          EnvSF -> State.gets (\(t, _, _) -> (t, BasicExpr EnvSF))
          SetEnvSF x -> do
            (tx, gx) <- annoF' x
            (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
            associateVar (PairTypeP (ArrTypeP it ot) it) tx
            pure (ot, BasicExpr . SetEnvSF . typeWrap tx $ gx)
          DeferSF x -> do
            (it, (tx, gx)) <- withNewEnv $ annoF' x
            pure (ArrTypeP it tx, BasicExpr . DeferSF $ gx)
          GateSF l r -> do
            (tl, gl) <- annoF' l
            (tr, gr) <- annoF' r
            associateVar tl tr
            pure (ArrTypeP ZeroTypeP tl, BasicExpr $ GateSF gl gr)
          LeftSF x -> do
            (tx, gx) <- annoF' x
            (tl, _) <- withNewEnv $ pure ()
            associateVar (PairTypeP tl AnyType) tx
            pure (tl, BasicExpr $ LeftSF gx)
          RightSF x -> do
            (tx, gx) <- annoF' x
            (tr, _) <- withNewEnv $ pure ()
            associateVar (PairTypeP AnyType tr) tx
            pure (tr, BasicExpr $ RightSF gx)
        AbortWrap AbortF -> do
            (t, _) <- withNewEnv $ pure ()
            pure (ArrTypeP ZeroTypeP (ArrTypeP t t), AbortWrap AbortF)
        EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (UnsizedRecursionF nr ox))))))) -> do
          (_, x) <- annoF' ox
          State.gets (\(t, _, _) ->
            ( t
            , EnhancedExpr . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Left . SplitFunctor . Right $ UnsizedRecursionF nr x
            ))

  in case State.runState (runExceptT $ annoF' expr) (TypeVariable 0, Set.empty, 1) of
    (Right (_, tg), (_, ts, _)) ->
      let resolver = fullyResolve (`Map.lookup` sm)
          resolveF = \case
            SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (TypedF t x)))))))) ->
              EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Left (TypedF (resolver t) x)))))))))
            x -> EnhancedExpr x
          sm = case buildTypeMap ts of
            Right m -> m
            z -> error ("annotateP some sort of typecheck error " <> show z)
      in cata resolveF tg

