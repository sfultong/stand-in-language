{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Possible where

import Control.Applicative
import Control.Lens.Plated
import Control.Monad
import Control.Monad.Reader (Reader, ReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State (State, StateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import Telomare (FragExpr (..), FragIndex, IExpr (..),
                 TelomareLike (fromTelomare, toTelomare), Term4 (..),
                 pattern AbortAny, rootFrag)


-- foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b

testFoldr :: (a -> t -> t) -> [a] -> t -> t
testFoldr f =
  let c f n = f (f (f n))
      test = not . null
      layer recur l accum = f (head l) (recur (tail l) accum)
      base l accum = accum
      conditionalLayer r l = if test l then layer r l else base l
  in c conditionalLayer base

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
    RightSF x -> shows "RightSF (" . showsPrec 0 x . shows ")"

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

pattern BasicExpr :: PartExprF (EnhancedExpr f) -> EnhancedExpr f
pattern BasicExpr x = EnhancedExpr (SplitFunctor (Right x))
pattern SuperWrap :: SuperPositionF (SuperExpr f) -> SuperExpr f
pattern SuperWrap x = EnhancedExpr (SplitFunctor (Left (SplitFunctor (Right x))))
pattern AbortWrap :: AbortableF (AbortExpr f) -> AbortExpr f
pattern AbortWrap x = EnhancedExpr (SplitFunctor (Left (SplitFunctor (Left (SplitFunctor (Right x))))))

evalEnhanced :: Functor o => (EnhancedExpr o -> PartExprF (EnhancedExpr o) -> EnhancedExpr o)
  -> EnhancedExpr o -> EnhancedExpr o -> EnhancedExpr o
evalEnhanced handleOther env (EnhancedExpr (SplitFunctor g)) =
  let wrap = embed . SplitFunctor . pure -- could just use BasicExpr
      recur = evalEnhanced handleOther env
  in case g of
    l@(Left _) -> EnhancedExpr $ SplitFunctor l
    Right r -> case fmap recur r of
      ZeroSF -> wrap ZeroSF
      p@(PairSF _ _) -> wrap p
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
      DeferSF _ -> wrap r
      GateSF _ _ -> wrap r
      LeftSF x -> case x of
        BasicExpr ZeroSF       -> wrap ZeroSF
        BasicExpr (PairSF l _) -> l
        _                      -> handleOther env (LeftSF x)
      RightSF x -> case x of
        BasicExpr ZeroSF       -> wrap ZeroSF
        BasicExpr (PairSF _ r) -> r
        _                      -> handleOther env (RightSF x)

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
            Left _                   -> handleOther env term
            Right (EitherPF sca scb) -> mergeSuper (evalE se sca) (evalE se scb)
          z -> error ("handleSuper setEnv pair unexpected sc " <> show sf)
        z -> error ("handleSuper setEnv unexpected sc " <> show sf)
      z -> error ("handleSuper unexpected " <> show term)

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
          Right (EitherPF a b) -> mergeSuper (recur $ SetEnvSF a) (recur $ SetEnvSF b)
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

evalS :: IExpr -> IO IExpr
evalS = f . toTelomare . evalEnhanced handleOther (BasicExpr ZeroSF). fromTelomare where
  f = \case
    Nothing -> pure Env
    Just x  -> pure x
  handleOther :: EnhancedExpr Maybe -> PartExprF (EnhancedExpr Maybe) -> EnhancedExpr Maybe
  handleOther = error "TODO evalS handleOther"

term4ToAbortExpr :: Term4 -> AbortExpr VoidF
term4ToAbortExpr (Term4 termMap) =
  let fragLookup = (termMap Map.!)
  in term4ToAbortExpr' fragLookup (rootFrag termMap)

term4ToAbortExpr' :: (FragIndex -> FragExpr Void) -> FragExpr Void -> AbortExpr VoidF
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
  let initialEnv = EnhancedExpr . SplitFunctor . Left . SplitFunctor . Right $ AnyPF
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
