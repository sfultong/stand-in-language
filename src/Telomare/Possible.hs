{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
module Telomare.Possible where

import           Control.Applicative
import           Control.Lens.Plated
import Control.Monad
import Control.Monad.Reader (Reader, ReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State (State, StateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class
import           Data.DList          (DList)
import qualified Data.DList          as DList
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import Data.Map (Map)
import qualified Data.Map as Map
import           Data.Monoid
import Data.Set (Set)
import qualified Data.Set            as Set
import           Debug.Trace
import           Telomare

data PossibleExprF a f
  = ZeroXF
  | AnyXF
  | PairXF f f
  | EitherXF f f
  | FunctionXF (FragExpr a)
  | ClosureXF (FragExpr a) f -- hack for lazy evaluation
  deriving (Eq, Ord, Show, Functor)

newtype PossibleExpr a = PossibleExpr {getPEF :: PossibleExprF a (PossibleExpr a)}
  deriving (Eq, Ord)

type instance Base (PossibleExpr a) = PossibleExprF a

instance Recursive (PossibleExpr a) where
  project = getPEF

instance Corecursive (PossibleExpr a) where
  embed = PossibleExpr

instance (Eq a) => Semigroup (PossibleExpr a) where
  (<>) (PossibleExpr a) (PossibleExpr b) = case (a,b) of
    (ZeroXF, ZeroXF)                      -> PossibleExpr ZeroXF
    (AnyXF, _)                            -> PossibleExpr AnyXF
    (_, AnyXF)                            -> PossibleExpr AnyXF
    (FunctionXF a, FunctionXF b) | a == b -> PossibleExpr $ FunctionXF a
    (PairXF a b, PairXF c d) | a == c     -> PossibleExpr $ PairXF a (b <> d)
    (PairXF a b, PairXF c d) | b == d     -> PossibleExpr $ PairXF (a <> c) b
    (EitherXF a b, EitherXF c d)          -> PossibleExpr $ EitherXF (a <> c) (b <> d)
    _ | a == b                            -> PossibleExpr a
    _                                     -> PossibleExpr $ EitherXF (PossibleExpr a) (PossibleExpr b)

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
    (ZeroSF, ZeroSF) -> True
    (EnvSF, EnvSF) -> True
    (PairSF a b, PairSF c d) -> test a c && test b d
    (SetEnvSF x, SetEnvSF y) -> test x y
    (DeferSF x, DeferSF y) -> test x y
    (GateSF a b, GateSF c d) -> test a c && test b d
    (LeftSF x, LeftSF y) -> test x y
    (RightSF x, RightSF y) -> test x y
    _ -> False

-- newtype EnhancedExpr o = EnhancedExpr {unEnhanceExpr :: Either o (PartExprF (EnhancedExpr o))} deriving (Eq, Show)
newtype EnhancedExpr f = EnhancedExpr {unEnhanceExpr :: Either (f (EnhancedExpr f)) (PartExprF (EnhancedExpr f))} -- deriving (Eq, Show)

{-
instance (Show1 f) => Show (EnhancedExpr f) where
  show (EnhancedExpr x) = "EnhancedExpr " <> case x of
    Left fa -> "Left (" <> showsPrec1 0 fa ")"
    Right x -> "Right (" <> show x <> ")"
-}

{-
instance (Eq1 f) => Eq (EnhancedExpr f) where
  (EnhancedExpr a) == (EnhancedExpr b) = case (a,b) of
    (Right ea, Right eb) -> ea == eb
    (Left fa, Left fb) -> eq1 fa fb
    _ -> False
-}

instance Eq1 f => Eq (EnhancedExpr f) where
  (EnhancedExpr a) == (EnhancedExpr b) = case (a,b) of
    (Left la, Left lb) -> eq1 la lb
    (Right ra, Right rb) -> eq1 ra rb
    _ -> False

{-
instance Corecursive (EnhancedExpr o) where
  embed = EnhancedExpr . pure
-}

evalEnhanced :: (EnhancedExpr o -> PartExprF (EnhancedExpr o) -> EnhancedExpr o)
  -> EnhancedExpr o -> EnhancedExpr o -> EnhancedExpr o
evalEnhanced handleOther env (EnhancedExpr g) =
  let wrap = EnhancedExpr . pure
      recur = evalEnhanced handleOther env
  in case g of
    l@(Left _) -> EnhancedExpr l
    Right r -> case fmap recur r of
      ZeroSF -> wrap ZeroSF
      p@(PairSF _ _) -> wrap p
      EnvSF -> env
      SetEnvSF x -> case x of
        EnhancedExpr (Right (PairSF (EnhancedExpr (Right cf)) nenv)) -> case cf of
          DeferSF c -> evalEnhanced handleOther nenv c
          GateSF l r -> case nenv of
            EnhancedExpr (Right ZeroSF) -> recur l
            EnhancedExpr (Right (PairSF _ _)) -> recur r
            _ -> handleOther env (SetEnvSF x)
          _ -> handleOther env (SetEnvSF x)
        _ -> handleOther env (SetEnvSF x)
      DeferSF _ -> wrap r
      GateSF _ _ -> wrap r
      LeftSF x -> case x of
        EnhancedExpr (Right ZeroSF) -> wrap ZeroSF
        EnhancedExpr (Right (PairSF l _)) -> l
        _ -> handleOther env (LeftSF x)
      RightSF x -> case x of
        EnhancedExpr (Right ZeroSF) -> wrap ZeroSF
        EnhancedExpr (Right (PairSF _ r)) -> r
        _ -> handleOther env (RightSF x)

data SuperPositionF f
  = EitherPF f f
  | AnyPF
  deriving (Eq, Ord, Show, Functor)

instance Eq1 SuperPositionF where
  liftEq test a b = case (a,b) of
    (AnyPF, AnyPF) -> True
    (EitherPF a b, EitherPF c d) -> test a c && test b d
    _ -> False

data AbortableF f
  = AbortF
  | AbortedF
  deriving (Eq, Ord, Show, Functor)

instance Eq1 AbortableF  where
  liftEq test a b = case (a,b) of
    (AbortF, AbortF) -> True
    (AbortedF, AbortedF) -> True
    _ -> False

{-
newtype OptionalFunctor f x = OptionalFunctor { unOptionalF :: Either (f x) x } deriving (Eq, Show)

instance Eq1 f => Eq1 (OptionalFunctor f) where
  liftEq test (OptionalFunctor a) (OptionalFunctor b) = case (a,b) of
    (Right ua, Right ub) -> test ua ub
    (Left oa, Left ob) -> liftEq test oa ob
    _ -> False
-}

newtype SplitFunctor g f x = SplitFunctor { unSplitF :: Either (g x) (f x) } deriving (Eq, Show)

instance (Eq1 f, Eq1 g) => Eq1 (SplitFunctor g f) where
  liftEq test (SplitFunctor a) (SplitFunctor b) = case (a,b) of
    (Right fa, Right fb) -> liftEq test fa fb
    (Left ga, Left gb) -> liftEq test ga gb
    _ -> False

class PartialSemigroup m where
  partialMerge :: m -> m -> Either (m,m) m

partfMerge :: (Eq f, Semigroup f) => PartExprF f -> PartExprF f -> Either (PartExprF f, PartExprF f) (PartExprF f)
partfMerge a b = case (a,b) of
  (ZeroSF, ZeroSF) -> pure ZeroSF
  (EnvSF, EnvSF) -> pure EnvSF
  (PairSF a b, PairSF c d) | a == c -> pure $ PairSF a (b <> d)
  (PairSF a b, PairSF c d) | b == d -> pure $ PairSF (a <> c) b
  (SetEnvSF x, SetEnvSF y) -> pure $ SetEnvSF (x <> y)
  (DeferSF x, DeferSF y) -> pure $ DeferSF (x <> y)
  (GateSF a b, GateSF c d) | a == c -> pure $ GateSF a (b <> d)
  (GateSF a b, GateSF c d) | b == d -> pure $ GateSF (a <> c) b
  (LeftSF x, LeftSF y) -> pure $ LeftSF (x <> y)
  (RightSF x, RightSF y) -> pure $ RightSF (x <> y)
  _ -> Left (a,b)

-- newtype SuperWrap f x = SuperWrap (OptionalFunctor f (OptionalFunctor SuperPositionF x))
-- newtype SuperWrap f x = SuperWrap (SplitFunctor f SuperPositionF x)

{-
instance Eq1 f => Eq1 (SuperWrap f) where
  liftEq test (SuperWrap a) (SuperWrap b) = liftEq (liftEq test) a b
-}

-- type SuperExpr f = EnhancedExpr (SuperWrap f)
type SuperExpr f = EnhancedExpr (SplitFunctor f SuperPositionF)

{-
instance (Semigroup x) => Semigroup (SuperWrap f x) where
  (<>) (SuperWrap (OptionalFunctor a)) (SuperWrap (OptionalFunctor b)) = case (a,b) of
    (Right (OptionalFunctor sa), Right (OptionalFunctor sb)) -> case (sa,sb) of
-}

-- instance Semigroup (EnhancedExpr (SuperWrap f)) where

superExtractOther :: SuperExpr f -> Either (f (SuperExpr f)) (SplitFunctor SuperPositionF PartExprF (SuperExpr f))
superExtractOther (EnhancedExpr x) = case x of
  Left (SplitFunctor sx) -> case sx of
    Left ox -> Left ox
    Right spx -> pure . SplitFunctor . Left $ spx
  Right rx -> pure . SplitFunctor . pure $ rx

mergeSuper :: Eq1 f => SuperExpr f -> SuperExpr f -> SuperExpr f
mergeSuper (EnhancedExpr a) (EnhancedExpr b) =
  let mergePart :: Eq1 f => PartExprF (SuperExpr f) -> PartExprF (SuperExpr f)
        -> Either (PartExprF (SuperExpr f), PartExprF (SuperExpr f)) (PartExprF (SuperExpr f))
      mergePart pa pb = case (pa, pb) of
        (ZeroSF, ZeroSF) -> pure ZeroSF
        (EnvSF, EnvSF) -> pure EnvSF
        (PairSF a b, PairSF c d) | a == c -> pure $ PairSF a (mergeSuper b d)
        (PairSF a b, PairSF c d) | b == d -> pure $ PairSF (mergeSuper a c) b
        (SetEnvSF x, SetEnvSF y) -> pure $ SetEnvSF (mergeSuper x y)
        (DeferSF x, DeferSF y) -> pure $ DeferSF (mergeSuper x y)
        (GateSF a b, GateSF c d) | a == c -> pure $ GateSF a (mergeSuper b d)
        (GateSF a b, GateSF c d) | b == d -> pure $ GateSF (mergeSuper a c) b
        (LeftSF x, LeftSF y) -> pure $ LeftSF (mergeSuper x y)
        (RightSF x, RightSF y) -> pure $ RightSF (mergeSuper x y)
        _ -> Left (pa, pb)
      superWrap = EnhancedExpr . Left . SplitFunctor . Right
      eitherWrap ea eb = superWrap $ EitherPF ea eb
  in case (a,b) of
    (Right pa, Right pb) -> case mergePart pa pb of
      Right r -> EnhancedExpr $ pure r
      Left (ea, eb) -> eitherWrap (EnhancedExpr $ pure ea) (EnhancedExpr $ pure eb)
    (Left (SplitFunctor (Right AnyPF)), _) -> superWrap AnyPF
    (_, Left (SplitFunctor (Right AnyPF))) -> superWrap AnyPF
    (Left (SplitFunctor (Right sa)), Left (SplitFunctor (Right sb))) -> case (sa,sb) of
       (EitherPF a b, EitherPF c d) -> eitherWrap (mergeSuper a c) (mergeSuper b d)
       _ -> eitherWrap (EnhancedExpr a) (EnhancedExpr b)
    _ -> eitherWrap (EnhancedExpr a) (EnhancedExpr b)

handleSuper :: Eq1 f => (SuperExpr f -> PartExprF (SuperExpr f) -> SuperExpr f)
  -> SuperExpr f -> PartExprF (SuperExpr f) -> SuperExpr f
handleSuper handleOther env term =
  let wrapS = EnhancedExpr . Left . SplitFunctor . Right
      recur = handleSuper handleOther env
      evalE = evalEnhanced (handleSuper handleOther)
      basicEval = evalE env . EnhancedExpr . pure
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
        Right (PairSF (EnhancedExpr sc) se) -> case sc of
          Left (SplitFunctor scx) -> case scx of
            Left _ -> handleOther env term
            Right (EitherPF sca scb) -> mergeSuper (evalE se sca) (evalE se scb)

type AbortExpr f = SuperExpr (SplitFunctor f AbortableF)

abortExtractOther :: AbortExpr f -> Either (f (AbortExpr f)) (SplitFunctor (SplitFunctor AbortableF SuperPositionF) PartExprF (AbortExpr f))
abortExtractOther (EnhancedExpr x) = case x of
  Left (SplitFunctor sp) -> case sp of
    Left (SplitFunctor sa) -> case sa of
      Left o -> Left o
      Right a -> pure . SplitFunctor . Left . SplitFunctor . Left $ a
    Right spx -> pure . SplitFunctor . Left . SplitFunctor . pure $ spx
  Right rx -> pure . SplitFunctor . pure $ rx

handleAbort :: Eq1 f => (AbortExpr f -> PartExprF (AbortExpr f) -> AbortExpr f)
  -> AbortExpr f -> PartExprF (AbortExpr f) -> AbortExpr f
handleAbort handleOther env term =
  let wrapA = EnhancedExpr . Left . SplitFunctor . Left . SplitFunctor . Right
  in case traverse abortExtractOther term of
    Left _ -> handleOther env term
    Right extracted -> case extracted of
      LeftSF (SplitFunctor (Left (SplitFunctor (Left AbortedF)))) -> wrapA AbortedF
      RightSF (SplitFunctor (Left (SplitFunctor (Left AbortedF)))) -> wrapA AbortedF
      SetEnvSF _ -> wrapA AbortedF -- if we're got AbortableF in here in any configuration, should abort
  {-
      SetEnvSF (SplitFunctor sf) -> case sf of
        Left (SplitFunctor (Left AbortedF)) -> wrapA AbortedF
-}
{-

instance (Eq o) => Semigroup (SuperExpr o) where
  (<>) (SuperExpr a) (SuperExpr b) =
    let mergePart (EnhancedExpr a) (EnhancedExpr b) = case (a,b) of
          (Right _, Left _) -> Nothing
        wrap = SuperExpr . pure
    in case (a,b) of
      (Right sa, Right sb) -> case (sa,sb) of
        (AnyPF,_) -> wrap AnyPF
-}

-- handleSuper :: forall o. (Show o, Eq o) => (SuperExpr o -> SuperPositionF (SuperExpr o) -> SuperExpr o)
  {-
handleSuper :: forall o. (Show o, Eq o) => (EnhancedExpr (SuperExpr o) -> PartExprF (SuperExpr o) -> EnhancedExpr (SuperExpr o))
  -> (EnhancedExpr (SuperExpr o) -> PartExprF (EnhancedExpr (SuperExpr o)) -> EnhancedExpr (SuperExpr o))
handleSuper handleOther env =
  -- let wrap = EnhancedExpr . pure
  let wrap = SuperExpr . pure
      handleThis = handleSuper handleOther
      recur = handleThis env
  in \case
    LeftSF x -> case unEnhanceExpr x of
      Left s@(SuperExpr lx) -> case lx of
        Right lxs -> case lxs of
          AnyPF -> EnhancedExpr . Left . SuperExpr . Right $ AnyPF
          -- EitherPF a b -> EnhancedExpr . Left . SuperExpr . Right $ EitherPX () ()
          EitherPF a b -> EnhancedExpr . Left . SuperExpr . Right $ EitherPX () ()

        -- Right AnyPF -> EnhancedExpr . Left . SuperExpr . Right $ AnyPF

-}
      
  {-
      Left (SuperExpr (Right (EnhancedExpr sp))) -> case sp of
        AnyPF -> x
-}


{-
evalE :: forall o. (Show o, Eq o) => (SuperExpr o -> SuperPositionF (Either o (SuperPositionF (SuperExpr o))) -> SuperExpr o)
  -> SuperExpr o -> SuperExpr o -> SuperExpr o
evalE handleOther env (SuperExpr g) =
  let wrap = SuperExpr . pure
      recur = evalE handleOther env
  in case g of
    l@(Left _) -> SuperExpr l
    Right r -> case r of
      EnhancedExpr ()
-}

instance TelomareLike (EnhancedExpr o) where
  fromTelomare = let wrap = EnhancedExpr . pure in \case
    Zero -> wrap ZeroSF
    Pair a b -> wrap $ PairSF (fromTelomare a) (fromTelomare b)
    Env -> wrap EnvSF
    SetEnv x -> wrap $ SetEnvSF (fromTelomare x)
    Defer x -> wrap $ DeferSF (fromTelomare x)
    Gate l r -> wrap $ GateSF (fromTelomare l) (fromTelomare r)
    PLeft x -> wrap $ LeftSF (fromTelomare x)
    PRight x -> wrap $ RightSF (fromTelomare x)
    Trace -> error "EnhancedExpr trace"
  toTelomare = \case
    EnhancedExpr (Right x) -> case x of
      ZeroSF -> pure Zero
      PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
      EnvSF -> pure Env
      SetEnvSF p -> SetEnv <$> toTelomare p
      DeferSF d -> Defer <$> toTelomare d
      GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
      LeftSF x -> PLeft <$> toTelomare x
      RightSF x -> PRight <$> toTelomare x
    _ -> Nothing

evalS :: IExpr -> IO IExpr
evalS = f . toTelomare . evalEnhanced handleOther (EnhancedExpr $ Right ZeroSF). fromTelomare where
  f = \case
    Nothing -> pure Env
    Just x -> pure x
  handleOther :: EnhancedExpr Maybe -> PartExprF (EnhancedExpr Maybe)-> EnhancedExpr Maybe
  handleOther = error "TODO evalS handleOther"

{-
instance (Eq a, Eq f, Semigroup f) => Semigroup (PossibleExprF a f) where
  (<>) a b = case (a,b) of
    (AnyXF, _) -> AnyXF
    (_, AnyXF) -> AnyXF
    (ZeroXF, ZeroXF) -> ZeroXF
    (FunctionXF a, FunctionXF b) | a == b -> FunctionXF a
    (PairXF a b, PairXF c d) | a == c -> PairXF a (b <> d)
    (PairXF a b, PairXF c d) | b == d -> PairXF (a <> c) b
    (EitherXF a b, EitherXF c d) -> EitherXF (a <> c) (b <> d)
    _ | a == b -> a
    _ -> EitherXF a b -- here's the problem. Can't construct infinite type
-}

{-
instance Semigroup (PossibleExpr a) where
  (<>) (PossibleExpr a) (PossibleExpr b) = PossibleExpr (a <> b)
-}

{-
instance (Show a) => Show (PossibleExpr a) where
  show exp = State.evalState (cata alg exp) 0 where
    alg :: (Show a, Show b) => (Base (PossibleExpr a)) (State Int String) -> State Int String
    alg = \case
      ZeroXF -> sindent "ZeroX"
      AnyXF  -> sindent "AnyX"
      PairXF a b -> indentWithTwoChildren "PairX" a b
      EitherXF a b -> indentWithTwoChildren "EitherX" a b
      FunctionXF f -> cata showFragAlg f
      ClosureXF f x -> indentWithTwoChildren "ClosureX" (cata showFragAlg f) x
-}
instance (Show a) => Show (PossibleExpr a) where
  show exp = State.evalState (cata alg exp) 0 where
    alg :: (Show a) => (Base (PossibleExpr a)) (State Int String) -> State Int String
    alg = \case
      ZeroXF -> sindent "ZeroX"
      AnyXF  -> sindent "AnyX"
      PairXF a b -> indentWithTwoChildren "PairX" a b
      EitherXF a b -> indentWithTwoChildren "EitherX" a b
      FunctionXF f -> cata showFragAlg f
      ClosureXF f x -> indentWithTwoChildren "ClosureX" (cata showFragAlg f) x

data PossibleOtherExpr a o
  = NormalExpr (PossibleExprF a (PossibleOtherExpr a o))
  | OtherExpr o
  deriving (Eq, Ord)

data OpExprF o f
  = OpLeft f
  | OpRight f
  | OpSetEnv f
  | OpSetEnvPair (Either o f) (Either o f) -- hacky
  -- | OpSetEnvPair (Either f o) (Either f o) -- hacky
  {-
  | OpWithEnv o f -- hacky, for when SetEnv has a definite env, but an indefinite function body
  | OpNeedsEnv o f -- hacky, for when SetEnv has a definite function body, but an indefinite env
-}
  | OpAbort o
  deriving (Eq, Ord, Show, Functor)
{-
instance Plated (PossibleExpr a b) where
  plate f = \case
    ZeroX -> pure ZeroX
    AnyX  -> pure AnyX
    PairX a b -> PairX <$> f a <*> f b
    EitherX a b -> EitherX <$> f a <*> f b
    FunctionX frag -> pure $ FunctionX frag
    ClosureX frag i -> ClosureX frag <$> f i
-}

-- notice that AnyX will translate to an empty list, which may not be expected
toIExprList :: PossibleExpr a -> DList.DList IExpr
toIExprList = cata alg where
  alg = \case
    ZeroXF -> pure Zero
    PairXF a b -> Pair <$> a <*> b
    EitherXF a b -> a <> b
    _ -> mempty

toIExprList' :: (PossibleExpr a -> FragExpr a -> PossibleExpr a) -> PossibleExpr a -> DList.DList IExpr
toIExprList' setEval = let recur = toIExprList' setEval in \case
  PossibleExpr ZeroXF -> pure Zero
  PossibleExpr (PairXF a b) -> Pair <$> recur a <*> recur b
  PossibleExpr (EitherXF a b) -> recur a <> recur b
  PossibleExpr (ClosureXF f i) -> recur $ setEval i f

{-
annotations :: Ord a => PossibleExpr a b -> Set a
annotations = \case
  PairX a b -> annotations a <> annotations b
  EitherX a b -> annotations a <> annotations b
  AnnotateX a x -> Set.insert a $ annotations x
  ClosureX _ x -> annotations x
  _ -> mempty

noAnnotatedFunctions :: PossibleExpr a b -> Bool
noAnnotatedFunctions =
  let testF = \case
        AnnotateX _ x -> testF x
        FunctionX _ -> False
        EitherX a b -> testF a && testF b
        ClosureX _ e -> noAnnotatedFunctions e
        x -> noAnnotatedFunctions x
  in \case
    PairX a b -> noAnnotatedFunctions a && noAnnotatedFunctions b
    EitherX a b -> noAnnotatedFunctions a && noAnnotatedFunctions b
    AnnotateX _ x -> testF x
    ClosureX _ e -> noAnnotatedFunctions e
    _ -> True
-}

truncatePossible :: PossibleExpr a -> FragExpr a
truncatePossible = cata alg where
  alg = \case
    ZeroXF -> ZeroFrag
    AnyXF -> ZeroFrag
    PairXF a b -> PairFrag a b
    EitherXF a _ -> a
    FunctionXF f -> f
    ClosureXF f x -> SetEnvFrag (PairFrag f x)

containsAux :: (FragIndex -> FragExpr a) -> FragExpr a -> Bool
containsAux fragLookup = let recur = containsAux fragLookup in \case
  PairFrag a b -> recur a || recur b
  SetEnvFrag x -> recur x
  DeferFrag ind -> recur $ fragLookup ind
  GateFrag l r -> recur l || recur r
  LeftFrag x -> recur x
  RightFrag x -> recur x
  AuxFrag _ -> True
  _ -> False

containsAux' :: (FragIndex -> FragExpr a) -> PossibleExpr a -> Bool
{-
containsAux' fragLookup = let recur = containsAux' fragLookup in \case
  PairXF a b -> recur a || recur b
  EitherXF a b -> recur a || recur b
  FunctionXF f -> containsAux fragLookup f
  ClosureXF f i -> containsAux fragLookup f || recur i
  _ -> False
-}
containsAux' fragLookup = cata alg where
  alg = \case
    PairXF a b -> a || b
    EitherXF a b -> a || b
    FunctionXF f -> containsAux fragLookup f
    ClosureXF f i -> containsAux fragLookup f || i
    _ -> False

type BasicPossible = PossibleExpr BreakExtras
-- type TestMapBuilder = StateT [(Set BreakExtras, BasicPossible)] (Reader (BreakExtras -> Int))
type TestMapBuilder = StateT [(Set BreakExtras, BasicPossible)] (Reader (BreakExtras -> Int))

-- type PResult o a = Either o (PossibleExprF a (PResult o a))
newtype PResult o a = PResult {unPResult :: Either o (PossibleExprF a (PResult o a))} deriving (Eq,Show)

type instance Base (PResult o a) = PossibleExprF a

instance Corecursive (PResult o a) where
  embed = PResult . pure
{-
instance (Eq o, Eq a) => Semigroup (PResult o a) where
  (<>) (PResult a) (PResult b) = case (a,b) of
    (Right a', Right b') -> PResult . Right $ a' <> b'
    (_) -> PResult . Right $ EitherXF (PResult a) (PResult b)
-}

{-
resultHas :: (PossibleExprF a (PResult o a) -> Bool) -> PResult o a -> Bool
resultHas f = let recur = resultHas f in \case
  PResult (Right x) -> case x of
    EitherXF a b -> recur a || recur b
    x' -> f x'
  _ -> False
-}
resultsFromList :: DList (PResult o a) -> PResult o a
resultsFromList l = case l of
  DList.Nil -> error "resultsFromList empty list"
  DList.Cons x xs -> foldr (\a b -> PResult (Right (EitherXF a b))) x xs

toPossible' :: forall a o. (Show a, Eq a, Show o, Eq o) => (FragIndex -> FragExpr a)
--  -> ((PossibleExpr a -> FragExpr a -> PResult o a) -> PossibleExpr a -> PossibleExpr a -> PossibleExpr a -> PResult o a)
  -> (OpExprF (PResult o a) o -> PResult o a)
  -> (a -> o) -- maybe replaceable by processOther?
  -> PResult o a -> FragExpr a -> PResult o a
toPossible' fragLookup processOther doAnnotation env =
  let tp = toPossible' fragLookup processOther doAnnotation
      recur = tp env
      wrap = PResult . pure
      prMap f (PResult r) = PResult (f r)
      unWrap (PResult r) = r
  {-
      processOther :: OpExprF (PResult o a) o -> PResult o a
      processOther = error "processOther TODO"
-}
      force = \case
        ClosureXF x env -> tp env x
        x -> embed x
      deepForce = \case
        PResult (Right x) -> case x of
          PairXF a b -> embed $ PairXF (deepForce a) (deepForce b)
          EitherXF a b -> embed $ EitherXF (deepForce a) (deepForce b)
          ClosureXF f i -> tp i f
          x -> embed x
      envWrap :: FragExpr a -> PResult o a
      envWrap = \case
        DeferFrag ind -> wrap . FunctionXF $ fragLookup ind
        x -> wrap $ ClosureXF x env
      resultLists :: PResult o a -> (DList o, DList (PossibleExprF a (PResult o a)))
      resultLists = \case
        PResult (Right x) -> case x of
          EitherXF a b -> resultLists a <> resultLists b
          _ -> (mempty, DList.singleton x)
        PResult (Left o) -> (DList.singleton o, mempty)
      isPair = \case
        PairXF _ _ -> True
        _ -> False
  in \case
    ZeroFrag -> embed ZeroXF
    PairFrag a b -> wrap $ PairXF (envWrap a) (envWrap b)
    EnvFrag -> env
    LeftFrag x -> f $ recur x where
      f = \case
        PResult (Right v) -> case v of
          z@ZeroXF -> wrap z
          a@AnyXF -> wrap a
          PairXF ln _ -> case ln of
            PResult (Right v') -> force v'
            PResult (Left o) -> PResult $ Left o
          EitherXF a b -> case (a, b) of
            (a'@(PResult (Right _)), b'@(PResult (Right _))) -> wrap $ EitherXF (f a') (f b')
            (a'@(PResult (Right _)), PResult (Left ob)) -> wrap $ EitherXF (f a') (processOther (OpLeft ob))
            (PResult (Left oa), b'@(PResult (Right _))) -> wrap $ EitherXF (processOther (OpLeft oa)) (f b')
            (PResult (Left oa), PResult (Left ob)) -> wrap $ EitherXF (processOther (OpLeft oa)) (processOther (OpLeft ob))
          z -> error $ "toPossible' LeftFrag unexpected " <> show z
        PResult (Left o) -> processOther $ OpLeft o
    RightFrag x -> f $ recur x where
      f = \case
        PResult (Right v) -> case v of
          z@ZeroXF -> wrap z
          a@AnyXF -> wrap a
          PairXF _ rn -> case rn of
            PResult (Right v') -> force v'
            PResult (Left o) -> PResult $ Left o
          EitherXF a b -> case (a, b) of
            (a'@(PResult (Right _)), b'@(PResult (Right _))) -> wrap $ EitherXF (f a') (f b')
            (a'@(PResult (Right _)), PResult (Left ob)) -> wrap $ EitherXF (f a') (processOther (OpRight ob))
            (PResult (Left oa), b'@(PResult (Right _))) -> wrap $ EitherXF (processOther (OpRight oa)) (f b')
            (PResult (Left oa), PResult (Left ob)) -> wrap $ EitherXF (processOther (OpRight oa)) (processOther (OpRight ob))
          z -> error $ "toPossible' RightFrag unexpected " <> show z
        PResult (Left o) -> processOther $ OpRight o
    SetEnvFrag x -> f $ recur x where
      f = \case
        PResult (Right v) -> case v of
            PairXF (PResult a) (PResult b) -> case (a >>= unPResult . force, b >>= unPResult . force) of
              (Right fp, Right ip) -> case fp of
                FunctionXF af -> case af of
                  GateFrag l r -> let ipList = resultLists $ wrap ip
                                      leftElem = if elem ZeroXF $ snd ipList then DList.singleton (recur l) else mempty
                                      rightElem = if any isPair $ snd ipList then DList.singleton (recur r) else mempty
                                      otherStuff = if length (leftElem <> rightElem) < 2
                                                   then processOther . OpSetEnvPair (Left $ wrap fp) . pure <$> fst ipList
                                                   else mempty
                                  in if elem AnyXF $ snd ipList
                                     then resultsFromList $ DList.fromList [recur l, recur r]
                                     else resultsFromList $ leftElem <> rightElem <> otherStuff
                  AbortFrag -> processOther . OpAbort . deepForce $ embed ip
                  x -> tp (embed ip) x
                z -> error ("unexpected function in toPossible' setenv: " <> show z)
              (Right fp, Left ip) -> processOther $ OpSetEnvPair (Left $ embed fp) (Right ip)
              (Left fp, Right ip) -> processOther $ OpSetEnvPair (Right fp) (Left $ embed ip)
              (Left fp, Left ip) -> processOther $ OpSetEnvPair (Right fp) (Right ip)
            EitherXF a b -> wrap $ EitherXF (f a) (f b)
            z -> error $ "toPossible' setenv not pair" <> show z
        PResult (Left o) -> processOther $ OpSetEnv o
    DeferFrag ind -> wrap . FunctionXF $ fragLookup ind
    g@(GateFrag _ _) -> wrap . FunctionXF $ g
    AbortFrag -> wrap . FunctionXF $ AbortFrag
    AuxFrag ur -> PResult . Left $ doAnnotation ur
    TraceFrag -> env

toPossible :: forall a m. (Show a, Eq a, Monad m) => (FragIndex -> FragExpr a)
  -> ((PossibleExpr a -> FragExpr a -> m (PossibleExpr a)) -> PossibleExpr a-> PossibleExpr a -> PossibleExpr a -> m (PossibleExpr a))
  -> (a -> m (PossibleExpr a))
  -> PossibleExpr a -> FragExpr a -> m (PossibleExpr a)
toPossible fragLookup setEval doAnnotation env =
  let toPossible' :: PossibleExpr a -> FragExpr a -> m (PossibleExpr a)
      toPossible' = toPossible fragLookup setEval doAnnotation
      ppe :: PossibleExprF a (PossibleExpr a) -> m (PossibleExpr a)
      ppe = pure . PossibleExpr
      traceThrough x = x -- trace ("toPossible dump: " <> show x) x
      recur :: FragExpr a -> m (PossibleExpr a)
      recur = toPossible' env -- . traceThrough
      envWrap :: FragExpr a -> PossibleExpr a
      envWrap x = case x of
        DeferFrag ind -> PossibleExpr . FunctionXF $ fragLookup ind
        x -> PossibleExpr $ ClosureXF x env
      force :: PossibleExprF a (PossibleExpr a) -> m (PossibleExpr a)
      force x = case x of
        ClosureXF x env -> toPossible' env x
        _ -> ppe x
      go :: FragExpr a -> m (PossibleExpr a)
      go f = case f of
        ZeroFrag -> ppe ZeroXF
        PairFrag a b -> ppe $ PairXF (envWrap a) (envWrap b)
        EnvFrag -> pure env
        LeftFrag x -> let process' :: PossibleExprF a (PossibleExpr a) -> m (PossibleExpr a)
                          process' x' = case x' of
                            PairXF ln _ -> force . getPEF $ ln
                            z@ZeroXF -> ppe z
                            a@AnyXF -> ppe a
                            EitherXF a b -> fmap PossibleExpr $ EitherXF <$> process a <*> process b
                            z -> error $ "toPossible leftFrag unexpected: " <> show z
                          process = process' . getPEF
                      in recur x >>= process
        RightFrag x -> let -- process' :: Possi
                           process' = \case
                              PairXF _ rn -> force . getPEF $ rn
                              z@ZeroXF -> ppe z
                              a@AnyXF -> ppe a
                              EitherXF a b -> fmap PossibleExpr $ EitherXF <$> process a <*> process b
                              z -> error $ "toPossible rightFrag unexpected: " <> show z
                           process = process' . getPEF
                      in recur x >>= process
        SetEnvFrag x -> recur x >>=
          let processSet' :: PossibleExprF a (PossibleExpr a) -> m (PossibleExpr a)
              processSet' x' = case x' of
                PairXF ft it -> do
                  ft' <- force . getPEF $ ft
                  it' <- force . getPEF $ it
                  setEval toPossible' env ft' it'
                EitherXF a b -> (<>) <$> processSet a <*> processSet b
                z -> error $ "toPossible setenv not pair: " <> show z
              processSet = processSet' . getPEF
          in processSet
        DeferFrag ind -> ppe . FunctionXF $ fragLookup ind -- process Defer here rather than SetEnvFrag to reduce arguments to setEval
        g@(GateFrag _ _) -> ppe $ FunctionXF g
        AbortFrag -> ppe $ FunctionXF AbortFrag
        a@(AuxFrag ur) -> doAnnotation ur
        TraceFrag -> pure env
  in go

-- TODO switch FragExpr a to FragExpr Void ?
abortSetEval :: (Show a, Eq a) => (IExpr -> Maybe IExpr -> Maybe IExpr)
  -> Maybe IExpr
  -> (PossibleExpr a -> FragExpr a -> Either IExpr (PossibleExpr a))
  -> PossibleExpr a -> PossibleExpr a -> PossibleExpr a -> Either IExpr (PossibleExpr a)
abortSetEval abortCombine abortDefault sRecur env ft' it' =
  let sRecur' = sRecur env
      ppe = pure . PossibleExpr
      -- toExprList' :: PossibleExpr a b -> Either IExpr (DList.DList IExpr)
      toExprList' x = let pure' = pure . pure -- should I use Compose here?
                      in case x of
        ZeroXF -> pure' Zero
        PairXF a b -> do
          na <- toExprList a
          nb <- toExprList b
          pure $ Pair <$> na <*> nb
        -- EitherX a b -> (<>) <$> toExprList' a <*> toExprList' b
        EitherXF a b -> let comb :: DList.DList a -> DList.DList a -> DList.DList a
                            comb = (<>)
                        in comb <$> toExprList a <*> toExprList b
        ClosureXF f i -> sRecur i f >>= toExprList
      toExprList = toExprList' . getPEF
      setEval ft it = case ft of
        FunctionXF af -> case af of
          GateFrag l r -> case (getPEF it, toExprList it) of
            (_, Left e) -> Left e -- if evaluating input aborts, bubble up abort result
            (AnyXF, _) -> (<>) <$> sRecur' l <*> sRecur' r
            (_, Right iList) -> case (elem Zero iList, length iList > 1) of
              (True, True) -> (<>) <$> sRecur' l <*> sRecur' r
              (True, False) -> sRecur' l
              _ -> sRecur' r
          AbortFrag -> case toList <$> toExprList it of
            Left e -> Left e -- if evaluating input aborts, bubble up abort result
            Right l -> case foldr abortCombine abortDefault $ l of
              Nothing -> ppe $ FunctionXF EnvFrag
              -- Just e -> trace ("aborting from input of " <> show it) Left e
              Just e -> Left e
          -- From Defer
          AuxFrag _ -> error "abortSetEval: should be no AuxFrag here"
          x -> sRecur it x
  in setEval (getPEF ft') it'

staticAbortProcessOther :: OpExprF (PResult IExpr a) IExpr -> PResult IExpr a
staticAbortProcessOther = \case
  OpLeft o -> PResult $ Left o
  OpRight o -> PResult $ Left o
  OpSetEnv o -> PResult $ Left o
  -- OpSetEnvPair -- TODO

staticAbortSetEval :: (Show a, Eq a) =>
  (PossibleExpr a -> FragExpr a -> Either IExpr (PossibleExpr a))
  -> PossibleExpr a -> PossibleExpr a -> PossibleExpr a -> Either IExpr (PossibleExpr a)
staticAbortSetEval = let combine a b = case (a,b) of
                           (Zero, _) -> Nothing
                           (_, Nothing) -> Nothing
                           (x, _) -> Just x
                     in abortSetEval combine (Just Zero) -- Just Zero is a dummy value. It shouldn't be returned

sizingAbortSetEval :: (Show a, Eq a) => (PossibleExpr a -> FragExpr a -> Either IExpr (PossibleExpr a))
  -> PossibleExpr a -> PossibleExpr a -> PossibleExpr a -> Either IExpr (PossibleExpr a)
sizingAbortSetEval = let combine a b = case (a,b) of
                                         (_,Just x) -> Just x
                                         (Pair Zero Zero, _) -> Just $ Pair Zero Zero
                                         _ -> Nothing
                     in abortSetEval combine Nothing

{-
testBuildingSetEval :: (BasicPossible -> FragExpr BreakExtras -> TestMapBuilder BasicPossible)
  -> BasicPossible -> BasicPossible -> BasicPossible -> TestMapBuilder BasicPossible
testBuildingSetEval sRecur env ft' it' =
  let sRecur' = sRecur env
      force x = case x of
        ClosureX x env -> sRecur env x
        _ -> pure x
      deepForce = \case
        PairX a b -> PairX <$> deepForce a <*> deepForce b
        EitherX a b -> EitherX <$> deepForce a <*> deepForce b
        AnnotateX a x -> AnnotateX a <$> deepForce x -- we could probably prune annotations for where this will be used
        ClosureX f i -> sRecur i f
        x -> pure x
      initialPoisoned = annotations it'
      setEval poisonedSet ft it = case ft of
        AnnotateX p pf -> AnnotateX p <$> setEval (Set.insert p poisonedSet) pf it
        FunctionX af -> case af of
          AbortFrag -> pure $ FunctionX EnvFrag
          GateFrag l r -> let doGate = \case
                                AnnotateX p pf -> AnnotateX p <$> doGate pf
                                ZeroX -> sRecur' l
                                PairX _ _ -> sRecur' r
                                zo | foldl (\b a -> a == Zero || b) False (toIExprList zo) -> (<>) <$> sRecur' l <*> sRecur' r -- this takes care of EitherX with an embedded ZeroX
                                EitherX _ _ -> sRecur' r
                                AnyX -> (<>) <$> sRecur' l <*> sRecur' r
                                z -> error $ "buildingSetEval Gate unexpected input: " <> show z
                       in doGate it
          AuxFrag ind -> do
            error "should not be directly in auxfrag"
  {-
            cLimit <- ($ ind) <$> lift Reader.ask
-}
            cLimit <- ((\c -> if c < 0 then error ("climit is " <> show (ind, c)) else c) . ($ ind)) <$> lift Reader.ask
            let appP ii = sRecur ii $ SetEnvFrag EnvFrag -- simple hack to simulate function application
            iterate (>>= appP) (pure it) !! cLimit
          LeftFrag (RightFrag (RightFrag (RightFrag (AuxFrag ind)))) -> do
            {-
            cLimit <- ($ ind) <$> lift Reader.ask
-}
            cLimit <- ((\c -> if c < 0 then error ("climit is " <> show (ind, c)) else c) . ($ ind)) <$> lift Reader.ask
            let appP ii = sRecur ii $ SetEnvFrag EnvFrag -- simple hack to simulate function application
	    	pruneAnnotations (annoSet, AnnotateX i x) = pruneAnnotations (Set.insert i annoSet, x)
		pruneAnnotations (annoSet, x) = (annoSet, x)
                extractR (aSet, pairA) = do
                  pairB <- case pairA of
                    PairX _ wrappedB -> force wrappedB
                    _ -> error ("extractR bad " <> show pairA)
                  pairC <- case pairB of
                    PairX _ wrappedC -> force wrappedC
                    _ -> error ("extractR bad " <> show pairA)
                  pairD <- case pairC of
                    PairX _ wrappedD -> force wrappedD
                    _ -> error ("extractR bad " <> show pairA)
                  case pairD of
                    PairX wrappedR _ -> (\r -> foldr AnnotateX r aSet) <$> force wrappedR
                    _ -> error ("extractR bad " <> show pairA)
            itResult <- iterate (>>= appP) (pure $ AnnotateX ind it) !! cLimit
            extractR $ pruneAnnotations (mempty, itResult)
          _ -> let alterSizeTest v = \case
                     Nothing -> pure v
                     Just e -> pure $ (<>) <$> e <*> v
                   addSizeTest :: (Set BreakExtras, BasicPossible) -> TestMapBuilder ()
                   addSizeTest x = State.modify (x :)
		   hasContamination = not . null $ poisonedSet
                   conditionallyAddTests :: TestMapBuilder BasicPossible -> TestMapBuilder BasicPossible
                   conditionallyAddTests opt =
                     let truncatedResult = flip Reader.runReader (const 1) $ State.evalStateT opt mempty -- force church numerals to 1 to evaluate poison typing
                     in do
                       {-
                       let showAuxed x = if containsAux' x
                             then trace ("adding size test, but it has aux: " <> show x) x
                             else x
-}
                       let showAuxed = id
                       when (hasContamination && noAnnotatedFunctions truncatedResult) . showAuxed $ do
                         fit <- deepForce it
                         addSizeTest (poisonedSet, PairX ft fit)
                       opt
               in conditionallyAddTests $ sRecur it af
        z -> error ("tbse setEval unexpected " <> show z)
  in setEval initialPoisoned ft' it'
-}
