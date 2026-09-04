{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}

-- |The shared functor vocabulary of the compiler. Telomare's IRs are not
-- independent grammars: each one is a composition of the base functors
-- defined here ('BasicExprF', 'StuckF', 'AbortableF', 'LamTermF',
-- 'HighTermF'), glued together by the @*Base@ embed/extract classes. The
-- pattern synonyms are polymorphic over those classes, so one synonym
-- (e.g. 'PairB') works at every stage of the pipeline.
module Telomare.IR.Base where

import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.DeepSeq (NFData (..))
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Char (chr, ord)
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (..))
import Data.Functor.Foldable (Base, Corecursive (embed),
                              Recursive (cata, project))
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Validity (Validity)
import GHC.Generics (Generic, Generic1, Generically1 (..))
import Telomare.IR.Loc (LocTag (..))

class BasicBase g where
  embedB :: BasicExprF x -> g x
  extractB :: g x -> Maybe (BasicExprF x)

class StuckBase g where
  embedS :: StuckF x -> g x
  extractS :: g x -> Maybe (StuckF x)

class AbortBase g where
  embedA :: AbortableF x -> g x
  extractA :: g x -> Maybe (AbortableF x)

-- TODO make these bidirectional
pattern BasicFW :: BasicBase g => BasicExprF x -> g x
pattern BasicFW x <- (extractB -> Just x) where
  BasicFW x = embedB x
pattern BasicEE :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => BasicExprF g -> g
pattern BasicEE x = GFix (BasicFW x)
pattern StuckFW :: (StuckBase g) => StuckF x -> g x
pattern StuckFW x <- (extractS -> Just x) where
  StuckFW x = embedS x
pattern StuckEE :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => StuckF g -> g
pattern StuckEE x = GFix (StuckFW x)
pattern AbortFW :: AbortBase g => AbortableF x -> g x
pattern AbortFW x <- (extractA -> Just x) where
  AbortFW x = embedA x
pattern AbortEE :: (Base g ~ f, AbortBase f, Recursive g, Corecursive g) => AbortableF g -> g
pattern AbortEE x = GFix (AbortFW x)

pattern FillFunction :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> f g
pattern FillFunction c e = StuckFW (SetEnvSF (BasicEE (PairSF c e)))
pattern FillFunctionEE :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
pattern FillFunctionEE c i = GFix (FillFunction c i)
pattern GateSwitch :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g -> f g
pattern GateSwitch l r s <- (embed -> (GateSwitchEE l r s)) where
  GateSwitch l r s = project (GateSwitchEE l r s)
pattern GateSwitchEE :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g -> g
pattern GateSwitchEE l r s = GFix (FillFunction (GFix (FillFunction GateB s)) (PairB l r))
pattern AppEE :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
pattern AppEE c i <- StuckEE (SetEnvSF (StuckEE (SetEnvSF (BasicEE (PairSF (StuckEE (DeferSF _ (BasicEE (PairSF (StuckEE (LeftSF (StuckEE (RightSF (StuckEE EnvSF))))) (BasicEE (PairSF (StuckEE (LeftSF (StuckEE EnvSF))) (StuckEE (RightSF (StuckEE (RightSF (StuckEE EnvSF))))))))))) (BasicEE (PairSF i c)))))))

pattern EnvB :: (Recursive g, Corecursive g, Base g ~ f, StuckBase f) => g
pattern EnvB = StuckEE EnvSF
pattern SetEnvB :: (Recursive g, Corecursive g, Base g ~ f, StuckBase f) => g -> g
pattern SetEnvB x = StuckEE (SetEnvSF x)
pattern GateB :: (Recursive g, Corecursive g, Base g ~ f, StuckBase f) => g
pattern GateB  = StuckEE GateSF
pattern LeftB :: (Recursive g, Corecursive g, Base g ~ f, StuckBase f) => g -> g
pattern LeftB x = StuckEE (LeftSF x)
pattern RightB :: (Recursive g, Corecursive g, Base g ~ f, StuckBase f) => g -> g
pattern RightB x = StuckEE (RightSF x)
pattern ZeroB :: (Recursive g, Corecursive g, Base g ~ f, BasicBase f) => g
pattern ZeroB = BasicEE ZeroSF
pattern AbortB :: (Recursive g, Corecursive g, Base g ~ f, AbortBase f) => g
pattern AbortB = AbortEE AbortF
-- note: only use this where annotations don't matter
pattern PairB :: (Recursive g, Corecursive g, Base g ~ f, BasicBase f) => g -> g -> g
pattern PairB a b = BasicEE (PairSF a b)

varB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Int -> g
varB n = if n < 0
  then error $ "varB invalid debruijin index " <> show n
  else LeftB (iterate RightB EnvB !! n)

i2B :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w) => Int -> g
i2B = \case
  0 -> ZeroB
  n -> PairP (i2B $ n - 1) ZeroB

b2i :: (Base g ~ f, BasicBase f, Recursive g) => g -> Maybe Int
b2i = cata f where
  f = \case
    BasicFW ZeroSF -> Just 0
    BasicFW (PairSF n (Just 0)) -> succ <$> n
    _ -> Nothing

b2s :: forall g f. (Base g ~ f, CarryWrap g ~ f, BasicBase f, Recursive g, Corecursive g, CarryAnno g) => g -> Maybe String
b2s = fmap (fmap chr) . f where
  f = \case
    PairP x xs -> (:) <$> b2i x <*> f xs
    ZeroB -> pure []
    _ -> Nothing

s2b :: forall g f w. (Base g ~ f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w) => String -> g
s2b = foldr (PairP . i2B . ord) ZeroB

-- | Strict if-then-else: raw branches sit in the gate-switch pair, so both
-- are evaluated (speculatively and in parallel, under the IC runtime) and
-- the loser is discarded. The lazy forms ('Telomare.Machine.iteB' and
-- 'Telomare.IR.Builder.iteS') are the intended default; user-facing @if@
-- (ITEF in 'Telomare.Resolve') still compiles to this because the sizing
-- pass's input-boundedness analysis only sees through the strict shape.
-- Once sizing learns the lazy shape, ITEF switches, and this remains for
-- the planned post-sizing optimizer to swap back in where branch
-- speculation pays.
--
-- KEEP: do not delete as unused. (An ANN pragma would mark this
-- mechanically, but ANN's Template Haskell staging breaks Generic
-- deriving in modules like this one.)
iteB_ :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w) => g -> g -> g -> g
iteB_ i t e = SetEnvB $ PairP (SetEnvB $ PairP GateB i) (PairP e t)

data BasicExprF f
  = ZeroSF
  | PairSF f f
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

-- Hand-written so the traversal inlines and specialises at call sites;
-- the derived method carries no unfolding, leaving hot monadic traversals
-- (e.g. the sizing pass) stuck on dictionary passing.
instance Traversable BasicExprF where
  {-# INLINE traverse #-}
  traverse f = \case
    ZeroSF     -> pure ZeroSF
    PairSF a b -> liftA2 PairSF (f a) (f b)

instance Eq1 BasicExprF where
  liftEq test a b = case (a,b) of
    (ZeroSF, ZeroSF)           -> True
    (PairSF a' b', PairSF c d) -> test a' c && test b' d
    _                          -> False

instance Show1 BasicExprF where
  liftShowsPrec showsPrec' _showList _prec = \case
    ZeroSF -> shows "ZeroSF"
    PairSF a b -> shows "PairSF (" . showsPrec' 0 a . shows ", " . showsPrec' 0 b . shows ")"

instance BasicBase BasicExprF where
  embedB = id
  extractB = pure

type BasicExpr = Fix BasicExprF

data StuckF f
  = DeferSF FunctionIndex f
  | EnvSF
  | SetEnvSF f
  | GateSF
  | LeftSF f
  | RightSF f
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

instance Traversable StuckF where
  {-# INLINE traverse #-}
  traverse f = \case
    DeferSF fi x -> DeferSF fi <$> f x
    EnvSF        -> pure EnvSF
    SetEnvSF x   -> SetEnvSF <$> f x
    GateSF       -> pure GateSF
    LeftSF x     -> LeftSF <$> f x
    RightSF x    -> RightSF <$> f x

instance Show1 StuckF where
  liftShowsPrec showsPrec' _showList _prec = \case
    DeferSF fi x -> shows "DeferSF " . shows fi . shows " (" . showsPrec' 0 x . shows ")"
    EnvSF -> shows "EnvSF"
    SetEnvSF x -> shows "SetEnvSF (" . showsPrec' 0 x . shows ")"
    GateSF -> shows "GateSF"
    LeftSF x -> shows "LeftSF (" . showsPrec' 0 x . shows ")"
    RightSF x -> shows "RightSF (" . showsPrec' 0 x . shows ")"
instance Eq1 StuckF where
  liftEq test a b = case (a,b) of
    (DeferSF ix _, DeferSF iy _) | ix == iy -> True -- test a b
    (EnvSF, EnvSF)                          -> True
    (GateSF, GateSF)                        -> True
    (SetEnvSF x, SetEnvSF y)                -> test x y
    (LeftSF x, LeftSF y)                    -> test x y
    (RightSF x, RightSF y)                  -> test x y
    _                                       -> False

newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show, Generic)

instance Validity FunctionIndex

-- TODO we can simplify abort semantics to (defer env), and then could do gate x (abort [message] x) for conditional abort
data AbortableF f
  = AbortF
  | AbortedF BasicExpr
  deriving (Eq, Show, Functor, Foldable, Generic)

instance Traversable AbortableF where
  {-# INLINE traverse #-}
  traverse _ = \case
    AbortF     -> pure AbortF
    AbortedF x -> pure $ AbortedF x

instance Eq1 AbortableF  where
  liftEq _test a b = case (a,b) of
    (AbortF, AbortF)                  -> True
    (AbortedF x, AbortedF y) | x == y -> True
    _                                 -> False

instance Show1 AbortableF where
  liftShowsPrec _showsPrec _showList _prec = \case
    AbortF     -> shows "AbortF"
    AbortedF x -> shows "(AbortedF " . shows x . shows ")"

newtype UnsizedRecursionToken = UnsizedRecursionToken { unUnsizedRecursionToken :: Int }
  deriving (Eq, Ord, Show, Enum, Generic)
  deriving anyclass (NFData)

instance Validity UnsizedRecursionToken

-- | Lambdas can be closed if it's expresion does not depend on any
--   outer binding.
data LamType l
  = Open l
  | Closed l
  | LetBinding Int l
  deriving (Eq, Show, Ord)

class LamBase g where
  type LamVar g
  type LamT g

  embedL :: LamTermF (LamT g) (LamVar g) x -> g x
  extractL :: g x -> Maybe (LamTermF (LamT g) (LamVar g) x)


class HighBase g where
  embedH :: HighTermF x -> g x
  extractH :: g x -> Maybe (HighTermF x)

data LamTermF l v f
  = VarF v
  | AppF f f
  | LamF l f
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (LamTermF l v))
instance (Show l, Show v) => Show1 (LamTermF l v) where
  liftShowsPrec showsPrecFunc _showList _d = \case
    VarF s -> showString "VarUPF " . shows s
    AppF f x -> showString "AppUPF " . showsPrecFunc 11 f . showChar ' '
                  . showsPrecFunc 11 x
    LamF var body -> showString "LamUPF " . shows var . showChar ' '
                       . showsPrecFunc 11 body

-- | High level grammar elements
data HighTermF f
  = CheckF f f
  | ITEF f f f
  | HLeftF f
  | HRightF f
  | HTraceF f
  | HashF f -- ^ On ad hoc user defined types, this term will be substitued to a unique Int.
  | ChurchF Int
  | RecursionF f f f
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 HighTermF)
instance Show1 HighTermF where
  liftShowsPrec showsPrecFunc _showList _d = \case
    ITEF c t e -> showString "ITEUPF " . showsPrecFunc 11 c . showChar ' '
                    . showsPrecFunc 11 t . showChar ' ' . showsPrecFunc 11 e
    ChurchF n -> showString "ChurchUPF " . shows n
    RecursionF a b c -> showString "UnsizedRecursionUPF "
                                 . showsPrecFunc 11 a . showChar ' '
                                 . showsPrecFunc 11 b . showChar ' '
                                 . showsPrecFunc 11 c
    HLeftF x -> showString "LeftUPF " . showsPrecFunc 11 x
    HRightF x -> showString "RightUPF " . showsPrecFunc 11 x
    HTraceF x -> showString "TraceUPF " . showsPrecFunc 11 x
    CheckF a b -> showString "CheckUPF " . showsPrecFunc 11 a . showChar ' '
                    . showsPrecFunc 11 b
    HashF x -> showString "HashUPF " . showsPrecFunc 11 x

-- NOTE placeholder design: these instances let the unannotated *B builder
-- patterns construct annotated terms, but every node they build gets the
-- same generic GeneratedLoc — so any term flowing through them (compiler
-- machinery, iteB/iteS branches, anything appS-built) loses its source
-- location, and downstream blame (EAL diagnostics in particular) points at
-- "the Cofree instance" instead of user code. A cleaner design would
-- thread the enclosing annotation (the way PairP/appS's CarryAnno path
-- does) instead of inventing one here.
instance BasicBase f => BasicBase (CofreeT.CofreeF f LocTag) where
  embedB = (GeneratedLoc "BasicBase Cofree instance" Nothing CofreeT.:<) . embedB
  extractB = extractB . (\(_ CofreeT.:< x) -> x)
instance StuckBase f => StuckBase (CofreeT.CofreeF f LocTag) where
  embedS = (GeneratedLoc "StuckBase Cofree instance" Nothing CofreeT.:<) . embedS
  extractS = extractS . (\(_ CofreeT.:< x) -> x)
instance AbortBase f => AbortBase (CofreeT.CofreeF f LocTag) where
  embedA = (GeneratedLoc "AbortBase Cofree instance" Nothing CofreeT.:<) . embedA
  extractA = extractA . (\(_ CofreeT.:< x) -> x)
instance HighBase f => HighBase (CofreeT.CofreeF f LocTag) where
  embedH = (GeneratedLoc "HighBase Cofree instance" Nothing CofreeT.:<) . embedH
  extractH = extractH . (\(_ CofreeT.:< x) -> x)

instance LamBase f => LamBase (CofreeT.CofreeF f LocTag) where
  type LamVar (CofreeT.CofreeF f LocTag) = LamVar f
  type LamT (CofreeT.CofreeF f LocTag) = LamT f

  embedL = (GeneratedLoc "LamBase Cofree instance" Nothing CofreeT.:<) . embedL
  extractL = extractL . (\(_ CofreeT.:< x) -> x)

forget :: Corecursive a => Cofree (Base a) anno -> a
forget = cata (\(_ CofreeT.:< z) -> embed z)

tag :: Recursive a => anno -> a -> Cofree (Base a) anno
tag anno x = anno :< (tag anno <$> project x)


convertBasic :: (BasicBase g, BasicBase h, Base x ~ h, Recursive x, Corecursive x, Monad m) => (g (m x) -> m x) -> g (m x) -> m x
convertBasic convertOther = \case
  BasicFW x -> BasicEE <$> sequence x
  x -> convertOther x
convertStuck :: (StuckBase g, StuckBase h, Base x ~ h, Recursive x, Corecursive x, Monad m) => (g (m x) -> m x) -> g (m x) -> m x
convertStuck convertOther = \case
  StuckFW x -> StuckEE <$> sequence x
  x -> convertOther x
convertAbort :: (AbortBase g, AbortBase h, Base x ~ h, Recursive x, Corecursive x, Monad m) => (g (m x) -> m x) -> g (m x) -> m x
convertAbort convertOther = \case
  AbortFW x -> AbortEE <$> sequence x
  x -> convertOther x

-- general utility functions

insertAndGetKey :: (Ord e, Enum e) => a -> State (Map e a) e
insertAndGetKey v = do
  m <- State.get
  let nextKey = case Set.lookupMax $ Map.keysSet m of
        Nothing -> toEnum 0
        Just n  -> succ n
  State.put $ Map.insert nextKey v m
  pure nextKey

pattern AbortRecursion :: (Base g ~ f, CarryWrap g ~ f, BasicBase f, CarryAnno g, Recursive g, Corecursive g) => g -> g
pattern AbortRecursion t = PairP ZeroB t
pattern AbortUser :: (Base g ~ f, CarryWrap g ~ f, BasicBase f, CarryAnno g, Recursive g, Corecursive g) => g -> g
pattern AbortUser m  = PairP (PairP ZeroB ZeroB) m
pattern AbortAny :: (Base g ~ f, CarryWrap g ~ f, BasicBase f, CarryAnno g, Recursive g, Corecursive g) => g
pattern AbortAny = PairP (PairP (PairP ZeroB ZeroB) ZeroB) ZeroB
pattern AbortUnsizeable :: (Base g ~ f, CarryWrap g ~ f, BasicBase f, CarryAnno g, Recursive g, Corecursive g) => g -> g
pattern AbortUnsizeable t = PairP (PairP (PairP (PairP ZeroB ZeroB) ZeroB) ZeroB) t

convertAbortMessage :: (Base g ~ f, CarryWrap g ~ f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, Show g) => g -> String
convertAbortMessage = \case
  AbortRecursion t -> "recursion overflow (should be caught by other means) for rt: " <> show (b2i t)
  AbortUser s -> case b2s s of
    Nothing -> "user abort invalid data: " <> show s
    Just m  -> "user abort: " <> m
  AbortAny -> "user abort of all possible abort reasons (non-deterministic input)"
  x -> "unexpected abort: " <> show x

class CarryAnno g where
  type CarryWrap g :: Type -> Type

  getEmbed :: g -> (CarryWrap g) g -> g

instance CarryAnno BasicExpr where
  type CarryWrap BasicExpr = BasicExprF

  getEmbed _ = Fix

pattern GFix :: (Recursive g, Corecursive g, Base g ~ f) => f g -> g
pattern GFix x <- (project -> x) where
  GFix x = embed x
pattern VarFP :: (LamBase f, LamVar f ~ n) => n -> f x
pattern VarFP n <- (extractL -> Just (VarF n)) where
  VarFP n = embedL $ VarF n
pattern VarAFP :: (LamBase f, LamVar f ~ n) => a -> n -> CofreeT.CofreeF f a x
pattern VarAFP a n <- (a CofreeT.:< (extractL -> Just (VarF n))) where
  VarAFP a n = a CofreeT.:< embedL (VarF n)
pattern VarP :: (Recursive g, Corecursive g, Base g ~ f, LamBase f, LamVar f ~ n) => n -> g
pattern VarP n = GFix (VarFP n)
pattern AppAFP :: (LamBase f) => a -> b -> b -> CofreeT.CofreeF f a b
pattern AppAFP a f i <- (a CofreeT.:< (extractL -> Just (AppF f i))) where
  AppAFP a f i = a CofreeT.:< embedL (AppF f i)
pattern AppP :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, LamBase w, LamBase f) => g -> g -> g
pattern AppP f i <- (project -> (extractL -> Just (AppF f i))) where
  AppP f i = getEmbed f (embedL (AppF f i))
pattern LamAFP :: (LamBase f, LamT f ~ n) => a -> n -> b -> CofreeT.CofreeF f a b
pattern LamAFP a n x <- (a CofreeT.:< (extractL -> Just (LamF n x))) where
  LamAFP a n x = (a CofreeT.:<) . embedL $ LamF n x
pattern LamP :: (Recursive g, CarryAnno g, Base g ~ f, LamBase f, CarryWrap g ~ w, LamBase w, LamT w ~ n, LamT f ~ n) => n -> g -> g
pattern LamP n x <- (project -> (extractL -> Just (LamF n x))) where
  LamP n x = getEmbed x (embedL (LamF n x))
pattern ITEAFP :: (HighBase f) => LocTag -> b -> b -> b -> CofreeT.CofreeF f LocTag b
pattern ITEAFP a i t e <- (a CofreeT.:< (extractH -> Just (ITEF i t e))) where
  ITEAFP a i t e = a CofreeT.:< embedH (ITEF i t e)
pattern ITEP :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, HighBase f, HighBase w) => g -> g -> g -> g
pattern ITEP i t e <- (project -> (extractH -> Just (ITEF i t e))) where
  ITEP i t e = getEmbed i (embedH (ITEF i t e))
pattern HLeft :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, HighBase f, HighBase w) => g -> g
pattern HLeft x <- (project -> (extractH -> Just (HLeftF x))) where
  HLeft x = getEmbed x (embedH $ HLeftF x)
pattern HRight :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, HighBase f, HighBase w) => g -> g
pattern HRight x <- (project -> (extractH -> Just (HRightF x))) where
  HRight x = getEmbed x (embedH $ HRightF x)
pattern HTrace :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, HighBase f, HighBase w) => g -> g
pattern HTrace x <- (project -> (extractH -> Just (HTraceF x))) where
  HTrace x = getEmbed x (embedH $ HTraceF x)
pattern PairAFP :: (BasicBase f) => LocTag -> x -> x -> CofreeT.CofreeF f LocTag x
pattern PairAFP a x y <- (a CofreeT.:< (extractB -> Just (PairSF x y))) where
  PairAFP a x y = a CofreeT.:< embedB (PairSF x y)
pattern PairP :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, BasicBase f, BasicBase w) => g -> g -> g
pattern PairP a b <- (project -> (extractB -> Just (PairSF a b))) where
  PairP a b = getEmbed a (embedB (PairSF a b))
