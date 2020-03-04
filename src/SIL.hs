{-#LANGUAGE DeriveFunctor #-}
{-#LANGUAGE DeriveGeneric#-}
{-#LANGUAGE DeriveAnyClass#-}
{-#LANGUAGE GeneralizedNewtypeDeriving#-}
{-#LANGUAGE LambdaCase #-}
{-#LANGUAGE PatternSynonyms #-}
{-#LANGUAGE ViewPatterns #-}

module SIL where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.State (State)
import Data.Char
import Data.Void
import Data.Map (Map)
import Data.Functor.Foldable
import GHC.Generics
import qualified Data.Map as Map
import qualified Control.Monad.State as State

-- if classes were categories, this would be an EndoFunctor?
class EndoMapper a where
  endoMap :: (a -> a) -> a -> a

class EitherEndoMapper a where
  eitherEndoMap :: (a -> Either e a) -> a -> Either e a

class MonoidEndoFolder a where
  monoidFold :: Monoid m => (a -> m) -> a -> m

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- {,}
  | Env                      -- identifier
  | SetEnv !IExpr
  | Defer !IExpr
  -- the rest of these should be no argument constructors, to be treated as functions with setenv
  | Abort
  | Gate !IExpr !IExpr
  | PLeft !IExpr             -- left
  | PRight !IExpr            -- right
  | Trace
  deriving (Eq, Show, Ord)

-- probably should get rid of this in favor of ExprT
data ExprA a
  = ZeroA a
  | PairA (ExprA a) (ExprA a) a
  | EnvA a
  | SetEnvA (ExprA a) a
  | DeferA (ExprA a) a
  | AbortA a
  | GateA (ExprA a) (ExprA a) a
  | PLeftA (ExprA a) a
  | PRightA (ExprA a) a
  | TraceA a
  deriving (Eq, Ord, Show)

-- so we can add annotations at any location in the AST
data ExprT a
  = ZeroT
  | PairT (ExprT a) (ExprT a)
  | EnvT
  | SetEnvT (ExprT a)
  | DeferT (ExprT a)
  | AbortT
  | GateT (ExprT a) (ExprT a)
  | LeftT (ExprT a)
  | RightT (ExprT a)
  | TraceT
  | TagT (ExprT a) a
  deriving (Eq, Ord, Show)

-- there must be a typeclass I can derive that does this
getA :: ExprA a -> a
getA (ZeroA a) = a
getA (PairA _ _ a) = a
getA (EnvA a) = a
getA (SetEnvA _ a) = a
getA (DeferA _ a) = a
getA (AbortA a) = a
getA (GateA _ _ a) = a
getA (PLeftA _ a) = a
getA (PRightA _ a) = a
getA (TraceA a) = a

data LamType t
  = Open t
  | Closed t
  deriving (Eq, Show, Ord)

-- -- we can probably get rid of x
-- data ParserTerm l x v
--   = TZero
--   | TPair (ParserTerm l x v) (ParserTerm l x v)
--   | TVar v
--   | TApp (ParserTerm l x v) (ParserTerm l x v)
--   | TCheck (ParserTerm l x v) (ParserTerm l x v)
--   | TITE (ParserTerm l x v) (ParserTerm l x v) (ParserTerm l x v)
--   | TLeft (ParserTerm l x v)
--   | TRight (ParserTerm l x v)
--   | TTrace (ParserTerm l x v)
--   | TLam (LamType l) (ParserTerm l x v)
--   | TLimitedRecursion
--   | TTransformedGrammar x
--   deriving (Eq, Show, Ord, Functor)

-- we can probably get rid of x
-- | Functor to do an F-algebra for recursive schemes.
data ParserTermF l x v r
  = TZero
  | TPair r r
  | TVar v
  | TApp r r
  | TCheck r r
  | TITE r r r
  | TLeft r
  | TRight r
  | TTrace r
  | TLam (LamType l) r
  | TLimitedRecursion
  | TTransformedGrammar x
  deriving (Eq, Show, Ord, Functor)

type ParserTerm l x v = Fix (ParserTermF l x v)

-- instance Show (ParserTerm l x v) where
--   show Fix x = show x

tzero :: ParserTerm l x v
tzero = Fix TZero

tpair :: ParserTerm l x v -> ParserTerm l x v -> ParserTerm l x v
tpair x y = Fix $ TPair x y

tvar :: v -> ParserTerm l x v
tvar v = Fix $ TVar v

tapp :: ParserTerm l x v -> ParserTerm l x v -> ParserTerm l x v
tapp x y = Fix $ TApp x y

tcheck :: ParserTerm l x v -> ParserTerm l x v -> ParserTerm l x v
tcheck x y = Fix $ TCheck x y

tite :: ParserTerm l x v -> ParserTerm l x v -> ParserTerm l x v -> ParserTerm l x v
tite x y z = Fix $ TITE x y z

tleft :: ParserTerm l x v -> ParserTerm l x v
tleft x = Fix $ TLeft x

tright :: ParserTerm l x v -> ParserTerm l x v
tright x = Fix $ TRight x

ttrace :: ParserTerm l x v -> ParserTerm l x v
ttrace x = Fix $ TTrace x

tlam :: (LamType l) -> ParserTerm l x v -> ParserTerm l x v
tlam l x = Fix $ TLam l x

tlimitedrecursion :: ParserTerm l x v
tlimitedrecursion = Fix TLimitedRecursion

ttransformedgrammar :: x -> ParserTerm l x v
ttransformedgrammar x = Fix $ TTransformedGrammar x

newtype FragIndex = FragIndex { unFragIndex :: Int } deriving (Eq, Show, Ord, Enum, NFData, Generic)

data FragExpr a
  = ZeroF
  | PairF (FragExpr a) (FragExpr a)
  | EnvF
  | SetEnvF (FragExpr a)
  | DeferF FragIndex
  | AbortF
  | GateF (FragExpr a) (FragExpr a)
  | LeftF (FragExpr a)
  | RightF (FragExpr a)
  | TraceF
  | AuxF a
  deriving (Eq, Ord, Show)

newtype EIndex = EIndex { unIndex :: Int } deriving (Eq, Show, Ord)

data BreakExtras
  = UnsizedRecursion
  deriving Show

type Term1 = ParserTerm (Either () String) Void (Either Int String)
type Term2 = ParserTerm () Void Int
newtype Term3 = Term3 (Map FragIndex (FragExpr BreakExtras)) deriving Show
newtype Term4 = Term4 (Map FragIndex (FragExpr Void)) deriving Show

type BreakState a = State (FragIndex, Map FragIndex (FragExpr a))

type BreakState' a = BreakState a (FragExpr a)

type IndExpr = ExprA EIndex

instance EndoMapper IExpr where
  endoMap f Zero = f Zero
  endoMap f (Pair a b) = f $ Pair (endoMap f a) (endoMap f b)
  endoMap f Env = f Env
  endoMap f (SetEnv x) = f $ SetEnv (endoMap f x)
  endoMap f (Defer x) = f $ Defer (endoMap f x)
  endoMap f Abort = f Abort
  endoMap f (Gate l r) = f $ Gate (endoMap f l) (endoMap f r)
  endoMap f (PLeft x) = f $ PLeft (endoMap f x)
  endoMap f (PRight x) = f $ PRight (endoMap f x)
  endoMap f Trace = f Trace

instance EitherEndoMapper IExpr where
  eitherEndoMap f Zero = f Zero
  eitherEndoMap f (Pair a b) = (Pair <$> eitherEndoMap f a <*> eitherEndoMap f b) >>= f
  eitherEndoMap f Env = f Env
  eitherEndoMap f (SetEnv x) = (SetEnv <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (Defer x) = (Defer <$> eitherEndoMap f x) >>= f
  eitherEndoMap f Abort = f Abort
  eitherEndoMap f (Gate l r) = (Gate <$> eitherEndoMap f l <*> eitherEndoMap f r) >>= f
  eitherEndoMap f (PLeft x) = (PLeft <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (PRight x) = (PRight <$> eitherEndoMap f x) >>= f
  eitherEndoMap f Trace = f Trace

instance MonoidEndoFolder IExpr where
  monoidFold f Zero = f Zero
  monoidFold f (Pair a b) = mconcat [f (Pair a b), monoidFold f a, monoidFold f b]
  monoidFold f Env = f Env
  monoidFold f (SetEnv x) = mconcat [f (SetEnv x), monoidFold f x]
  monoidFold f (Defer x) = mconcat [f (Defer x), monoidFold f x]
  monoidFold f Abort = f Abort
  monoidFold f (Gate l r) = mconcat [f (Gate l r), monoidFold f l, monoidFold f r]
  monoidFold f (PLeft x) = mconcat [f (PLeft x), monoidFold f x]
  monoidFold f (PRight x) = mconcat [f (PRight x), monoidFold f x]
  monoidFold f Trace = f Trace

instance NFData IExpr where
  rnf Zero         = ()
  rnf (Pair e1 e2) = rnf e1 `seq` rnf e2
  rnf Env          = ()
  rnf (SetEnv  e)  = rnf e
  rnf (Defer   e)  = rnf e
  rnf Abort        = ()
  rnf (Gate l r)   = rnf l `seq` rnf r
  rnf (PLeft   e)  = rnf e
  rnf (PRight  e)  = rnf e
  rnf Trace        = ()

data RunTimeError
  = AbortRunTime IExpr
  | SetEnvError IExpr
  | GenericRunTimeError String IExpr
  | ResultConversionError String
  deriving (Eq, Ord)

instance Show RunTimeError where
  show (AbortRunTime a) = "Abort: " <> (show $ g2s a)
  show (SetEnvError e) = "Can't SetEnv: " <> show e
  show (GenericRunTimeError s i) = "Generic Runtime Error: " <> s <> " -- " <> show i
  show (ResultConversionError s) = "Couldn't convert runtime result to IExpr: " <> s

type RunResult = ExceptT RunTimeError IO

class SILLike a where
  fromSIL :: IExpr -> a
  toSIL :: a -> Maybe IExpr

class SILLike a => AbstractRunTime a where
  eval :: a -> RunResult a

rootFrag :: Map FragIndex a -> a
rootFrag = (Map.! FragIndex 0)

-- TODO get rid of these and use bidirectional pattern matching
zero :: IExpr
zero = Zero
pair :: IExpr -> IExpr -> IExpr
pair = Pair
var :: IExpr
var = Env
env :: IExpr
env = Env
twiddle :: IExpr -> IExpr
twiddle x = setenv (pair (defer (pair (pleft (pright env)) (pair (pleft env) (pright (pright env))))) x)
app :: IExpr -> IExpr -> IExpr
--app c i = setenv (twiddle (pair i c))
app c i = setenv (setenv (pair (defer (pair (pleft (pright env)) (pair (pleft env) (pright (pright env)))))
                          (pair i c)))
check :: IExpr -> IExpr -> IExpr
check c tc = setenv (pair (defer
                             (setenv (pair
                                        (setenv (pair Abort (app (pleft env) (pright env))))
                                        (pright env)
                                     )
                             )
                          )
                          (pair tc c)
                    )
pleft :: IExpr -> IExpr
pleft = PLeft
pright :: IExpr -> IExpr
pright = PRight
setenv :: IExpr -> IExpr
setenv = SetEnv
defer :: IExpr -> IExpr
defer = Defer
lam :: IExpr -> IExpr
lam x = pair (defer x) env
-- a form of lambda that does not pull in a surrounding environment
completeLam :: IExpr -> IExpr
completeLam x = pair (defer x) zero
ite :: IExpr -> IExpr -> IExpr -> IExpr
ite i t e = setenv (pair (Gate e t) i)
varN :: Int -> IExpr
varN n = pleft (iterate pright env !! n)
partialFix :: IExpr -> IExpr
partialFix = PartialFix (s2g "recursion depth limit exceeded")

varNF :: Int -> FragExpr a
varNF n = LeftF (iterate RightF EnvF !! n)

-- make sure these patterns are in exact correspondence with the shortcut functions above
pattern FirstArg :: IExpr
pattern FirstArg = PLeft Env
pattern SecondArg :: IExpr
pattern SecondArg = PLeft (PRight Env)
pattern ThirdArg :: IExpr
pattern ThirdArg <- PLeft (PRight (PRight Env))
pattern FourthArg :: IExpr
pattern FourthArg <- PLeft (PRight (PRight (PRight Env)))
pattern Lam :: IExpr -> IExpr
pattern Lam x = Pair (Defer x) Env
pattern App :: IExpr -> IExpr -> IExpr
pattern App c i = SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env)))))
                         (Pair i c)))
pattern TwoArgFun :: IExpr -> IExpr
pattern TwoArgFun c <- Pair (Defer (Pair (Defer c) Env)) Env
pattern ITE :: IExpr -> IExpr -> IExpr -> IExpr
pattern ITE i t e = SetEnv (Pair (Gate e t) i)
pattern EasyTrace :: IExpr -> IExpr
pattern EasyTrace x = SetEnv (Pair (Defer Trace) x)

countApps :: Int -> IExpr -> Maybe Int
countApps x FirstArg = pure x
countApps x (App SecondArg c) = countApps (x + 1) c
countApps _ _ = Nothing

pattern ChurchNum :: Int -> IExpr
pattern ChurchNum x <- TwoArgFun (countApps 0 -> Just x)
pattern PartialFix :: IExpr -> IExpr -> IExpr
pattern PartialFix m c = Lam (Lam (App
                                   (App c SecondArg)
                                   (Lam (App (SetEnv (Pair Abort m)) (App SecondArg FirstArg)))
                                  )
                             )

pattern ToChurch :: IExpr
pattern ToChurch <-
  Lam
    (App
      (App
        FirstArg
        (Lam (Lam (Lam (Lam
          (ITE
            ThirdArg
            (App
              SecondArg
              (App
                (App
                  (App
                    FourthArg
                    (PLeft ThirdArg)
                  )
                  SecondArg
                )
                FirstArg
              )
            )
            FirstArg
          )
        ))))
      )
      (Lam (Lam (Lam FirstArg)))
    )

deferF :: BreakState' a -> BreakState' a
deferF x = do
  bx <- x
  (fi@(FragIndex i), fragMap) <- State.get
  State.put (FragIndex (i + 1), Map.insert fi bx fragMap)
  pure $ DeferF fi

appF :: BreakState' a -> BreakState' a -> BreakState' a
appF c i =
  let twiddleF = deferF $ pure (PairF (LeftF (RightF EnvF)) (PairF (LeftF EnvF) (RightF (RightF EnvF))))
  in (\tf p -> SetEnvF (SetEnvF (PairF tf p))) <$> twiddleF <*> (PairF <$> i <*> c)

lamF :: BreakState' a -> BreakState' a
lamF x = (\f -> PairF f EnvF) <$> deferF x

clamF :: BreakState' a -> BreakState' a
clamF x = (\f -> PairF f ZeroF) <$> deferF x

toChurchF :: Int -> BreakState' a
toChurchF x' =
  let inner 0 = pure $ LeftF EnvF
      inner x = appF (pure $ LeftF (RightF EnvF)) (inner (x - 1))
  in lamF (lamF (inner x'))

partialFixF :: Int -> BreakState' a
partialFixF i =
  let firstArgF = pure $ LeftF EnvF
      secondArgF = pure $ LeftF (RightF EnvF)
      abortMessage = s2gF "recursion depth limit exceeded ~"
      abrt = SetEnvF . PairF AbortF <$> abortMessage
  in clamF (lamF (appF (appF (toChurchF i) secondArgF) (lamF (appF abrt (appF secondArgF firstArgF)))))

pattern FirstArgA :: ExprA a
pattern FirstArgA <- PLeftA (EnvA _) _
pattern SecondArgA :: ExprA a
pattern SecondArgA <- PLeftA (PRightA (EnvA _) _) _
pattern ThirdArgA :: ExprA a
pattern ThirdArgA <- PLeftA (PRightA (PRightA (EnvA _) _) _) _
pattern FourthArgA :: ExprA a
pattern FourthArgA <- PLeftA (PRightA (PRightA (PRightA (EnvA _) _) _) _) _
pattern AppA :: ExprA a -> ExprA a -> ExprA a
pattern AppA c i <- SetEnvA (SetEnvA (PairA
                                      (DeferA (PairA
                                               (PLeftA (PRightA (EnvA _) _) _)
                                               (PairA (PLeftA (EnvA _) _) (PRightA (PRightA (EnvA _) _) _) _)
                                               _)
                                       _)
                                      (PairA i c _)
                                      _)
                            _)
                    _
pattern LamA :: ExprA a -> ExprA a
pattern LamA x <- PairA (DeferA x _) (EnvA _) _
pattern TwoArgFunA :: ExprA a -> a -> a -> ExprA a
pattern TwoArgFunA c ana anb <- PairA (DeferA (PairA (DeferA c ana) (EnvA _) _) anb) (EnvA _) _
-- TODO check if these make sense at all. A church type should have two arguments (lamdas), but the inner lambdas
-- for addition/multiplication should be f, f+x rather than m+n
-- no, it does not, in \m n f x -> m f (n f x), m and n are FourthArg and ThirdArg respectively
pattern PlusA :: ExprA a -> ExprA a -> ExprA a
pattern PlusA m n <- LamA (LamA (AppA (AppA m SecondArgA) (AppA (AppA n SecondArgA) FirstArgA)))
pattern MultA :: ExprA a -> ExprA a -> ExprA a
pattern MultA m n <- LamA (AppA m (AppA n FirstArgA))

{-
pattern AppF :: FragExpr a -> FragExpr a -> FragExpr a
pattern AppF c i = SetEnvF (SetEnvF (PairF (DeferF (PairF (LeftF (RightF EnvF)) (PairF (LeftF EnvF) (RightF (RightF EnvF)))))
                                    (PairF i c)))
-}

data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord)

newtype PrettyDataType = PrettyDataType DataType

showInternal at@(ArrType _ _) = concat ["(", show $ PrettyDataType at, ")"]
showInternal t = show . PrettyDataType $ t

instance Show PrettyDataType where
  show (PrettyDataType dt) = case dt of
    ZeroType -> "D"
    (ArrType a b) -> concat [showInternal a, " -> ", showInternal b]
    (PairType a b) ->
      concat ["{", show $ PrettyDataType a, ",", show $ PrettyDataType b, "}"]

data PartialType
  = ZeroTypeP
  | AnyType
  | TypeVariable Int
  | ArrTypeP PartialType PartialType
  | PairTypeP PartialType PartialType
  deriving (Show, Eq, Ord)

newtype PrettyPartialType = PrettyPartialType PartialType

showInternalP at@(ArrTypeP _ _) = concat ["(", show $ PrettyPartialType at, ")"]
showInternalP t = show . PrettyPartialType $ t

instance Show PrettyPartialType where
  show (PrettyPartialType dt) = case dt of
    ZeroTypeP -> "Z"
    AnyType -> "A"
    (ArrTypeP a b) -> concat [showInternalP a, " -> ", showInternalP b]
    (PairTypeP a b) ->
      concat ["{", show $ PrettyPartialType a, ",", show $ PrettyPartialType b, "}"]
    (TypeVariable (-1)) -> "badType"
    (TypeVariable x) -> 'v' : show x

instance EndoMapper DataType where
  endoMap f ZeroType = f ZeroType
  endoMap f (ArrType a b) = f $ ArrType (endoMap f a) (endoMap f b)
  endoMap f (PairType a b) = f $ PairType (endoMap f a) (endoMap f b)

instance EndoMapper PartialType where
  endoMap f ZeroTypeP = f ZeroTypeP
  endoMap f AnyType = f AnyType
  endoMap f (TypeVariable i) = f $ TypeVariable i
  endoMap f (ArrTypeP a b) = f $ ArrTypeP (endoMap f a) (endoMap f b)
  endoMap f (PairTypeP a b) = f $ PairTypeP (endoMap f a) (endoMap f b)

mergePairType :: DataType -> DataType
mergePairType = endoMap f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = endoMap f where
  f (PairTypeP ZeroTypeP ZeroTypeP) = ZeroTypeP
  f x = x

newtype PrettyIExpr = PrettyIExpr IExpr

instance Show PrettyIExpr where
  show (PrettyIExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["{", show (PrettyIExpr a), ",", show (PrettyIExpr b), "}"]
    Zero -> "0"
    x -> show x

g2i :: IExpr -> Int
g2i Zero = 0
g2i (Pair a b) = 1 + g2i a + g2i b
g2i x = error $ "g2i " ++ show x

i2g :: Int -> IExpr
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero

ints2g :: [Int] -> IExpr
ints2g = foldr (\i g -> Pair (i2g i) g) Zero

g2Ints :: IExpr -> [Int]
g2Ints Zero = []
g2Ints (Pair n g) = g2i n : g2Ints g
g2Ints x = error $ "g2Ints " ++ show x

s2g :: String -> IExpr
s2g = ints2g . map ord

g2s :: IExpr -> String
g2s = map chr . g2Ints

toChurch :: Int -> IExpr
toChurch x =
  let inner 0 = PLeft Env
      inner x = app (PLeft $ PRight Env) (inner (x - 1))
  in lam (lam (inner x))

i2gF :: Int -> BreakState' a
i2gF 0 = pure ZeroF
i2gF n = PairF <$> i2gF (n - 1) <*> pure ZeroF

ints2gF :: [Int] -> BreakState' a
ints2gF = foldr (\i g -> PairF <$> i2gF i <*> g) (pure ZeroF)

s2gF :: String -> BreakState' a
s2gF = ints2gF . map ord

-- convention is numbers are left-nested pairs with zero on right
isNum :: IExpr -> Bool
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False

nextI :: State EIndex EIndex
nextI = State.state $ \(EIndex n) -> (EIndex n, EIndex (n + 1))

toIndExpr :: IExpr -> State EIndex IndExpr
toIndExpr Zero = ZeroA <$> nextI
toIndExpr (Pair a b) = PairA <$> toIndExpr a <*> toIndExpr b <*> nextI
toIndExpr Env = EnvA <$> nextI
toIndExpr (SetEnv x) = SetEnvA <$> toIndExpr x <*> nextI
toIndExpr (Defer x) = DeferA <$> toIndExpr x <*> nextI
toIndExpr Abort = AbortA <$> nextI
toIndExpr (Gate l r) = GateA <$> toIndExpr l <*> toIndExpr r <*> nextI
toIndExpr (PLeft x) = PLeftA <$> toIndExpr x <*> nextI
toIndExpr (PRight x) = PRightA <$> toIndExpr x <*> nextI
toIndExpr Trace = TraceA <$> nextI

toIndExpr' :: IExpr -> IndExpr
toIndExpr' x = State.evalState (toIndExpr x) (EIndex 0)

instance SILLike (ExprT a) where
  fromSIL = \case
    Zero -> ZeroT
    Pair a b -> PairT (fromSIL a) (fromSIL b)
    Env -> EnvT
    SetEnv x -> SetEnvT $ fromSIL x
    Defer x -> DeferT $ fromSIL x
    Abort -> AbortT
    Gate l r -> GateT (fromSIL l) (fromSIL r)
    PLeft x -> LeftT $ fromSIL x
    PRight x -> RightT $ fromSIL x
    Trace -> TraceT
  toSIL = \case
    ZeroT -> pure Zero
    PairT a b -> Pair <$> toSIL a <*> toSIL b
    EnvT -> pure Env
    SetEnvT x -> SetEnv <$> toSIL x
    DeferT x -> Defer <$> toSIL x
    AbortT -> pure Abort
    GateT l r -> Gate <$> toSIL l <*> toSIL r
    LeftT x -> PLeft <$> toSIL x
    RightT x -> PRight <$> toSIL x
    TraceT -> pure Trace
    TagT x _ -> toSIL x -- just elide tags

silToFragmap :: IExpr -> Map FragIndex (FragExpr a)
silToFragmap expr = Map.insert (FragIndex 0) bf m where
    (bf, (_,m)) = State.runState (convert expr) (FragIndex 1, Map.empty)
    convert = \case
      Zero -> pure ZeroF
      Pair a b -> PairF <$> convert a <*> convert b
      Env -> pure EnvF
      SetEnv x -> SetEnvF <$> convert x
      Defer x -> do
        bx <- convert x
        (fi@(FragIndex i), fragMap) <- State.get
        State.put (FragIndex (i + 1), Map.insert fi bx fragMap)
        pure $ DeferF fi
      Abort -> pure AbortF
      Gate l r -> GateF <$> convert l <*> convert r
      PLeft x -> LeftF <$> convert x
      PRight x -> RightF <$> convert x
      Trace -> pure TraceF

fragmapToSIL :: Map FragIndex (FragExpr a) -> Maybe IExpr
fragmapToSIL fragMap = convert (rootFrag fragMap) where
    convert = \case
      ZeroF -> pure Zero
      PairF a b -> Pair <$> convert a <*> convert b
      EnvF -> pure Env
      SetEnvF x -> SetEnv <$> convert x
      DeferF ind -> Defer <$> (Map.lookup ind fragMap >>= convert)
      AbortF -> pure Abort
      GateF l r -> Gate <$> convert l <*> convert r
      LeftF x -> PLeft <$> convert x
      RightF x -> PRight <$> convert x
      TraceF -> pure Trace
      AuxF _ -> Nothing

instance SILLike Term3 where
  fromSIL = Term3 . silToFragmap
  toSIL (Term3 fragMap) = fragmapToSIL fragMap

instance SILLike Term4 where
  fromSIL = Term4 . silToFragmap
  toSIL (Term4 fragMap) = fragmapToSIL fragMap
