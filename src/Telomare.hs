{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

module Telomare where

import           Control.DeepSeq
import           Control.Lens.Combinators
import           Control.Monad.Except
import           Control.Monad.State      (State)
import qualified Control.Monad.State      as State
import           Data.Char
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Void
import           GHC.Generics

-- if classes were categories, this would be an EndoFunctor?
class EndoMapper a where
  endoMap :: (a -> a) -> a -> a

class EitherEndoMapper a where
  eitherEndoMap :: (a -> Either e a) -> a -> Either e a

class MonoidEndoFolder a where
  monoidFold :: Monoid m => (a -> m) -> a -> m

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- (,)
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
makeBaseFunctor ''IExpr -- * Functorial version IExprF.

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
getA (ZeroA a)     = a
getA (PairA _ _ a) = a
getA (EnvA a)      = a
getA (SetEnvA _ a) = a
getA (DeferA _ a)  = a
getA (AbortA a)    = a
getA (GateA _ _ a) = a
getA (PLeftA _ a)  = a
getA (PRightA _ a) = a
getA (TraceA a)    = a

-- | Lambdas can be closed if it's expresion does not depend on any
--   outer binding.
data LamType l
  = Open l
  | Closed l
  deriving (Eq, Show, Ord)

-- | Parser AST
data ParserTerm l v
  = TZero
  | TPair (ParserTerm l v) (ParserTerm l v)
  | TVar v
  | TApp (ParserTerm l v) (ParserTerm l v)
  | TCheck (ParserTerm l v) (ParserTerm l v)
  | TITE (ParserTerm l v) (ParserTerm l v) (ParserTerm l v)
  | TLeft (ParserTerm l v)
  | TRight (ParserTerm l v)
  | TTrace (ParserTerm l v)
  | TLam (LamType l) (ParserTerm l v)
  | TLimitedRecursion
  deriving (Eq, Ord, Functor, Foldable, Traversable)
makeBaseFunctor ''ParserTerm -- * Functorial version ParserTermF

instance (Show l, Show v) => Show (ParserTerm l v) where
  show x = State.evalState (cata alg $ x) 0 where
    alg :: (Base (ParserTerm l v)) (State Int String) -> State Int String
    alg TZeroF = sindent "TZero"
    alg (TPairF sl sr) = indentWithTwoChildren "TPair" sl sr
    alg (TVarF v) = sindent $ "TVar " <> show v
    alg (TAppF sl sr) = indentWithTwoChildren "TApp" sl sr
    alg (TCheckF sl sr) = indentWithTwoChildren "TCheck" sl sr
    alg (TITEF sx sy sz) = do
      i <- State.get
      State.put $ i + 2
      x <- sx
      State.put $ i + 2
      y <- sy
      State.put $ i + 2
      z <- sz
      pure $ indent i "TITE\n" <> x <> "\n" <> y <> "\n" <> z
    alg (TLeftF l) = indentWithOneChild "TLeft" l
    alg (TRightF r) = indentWithOneChild "TRight" r
    alg (TTraceF x) = indentWithOneChild "TTrace" x
    alg (TLamF l x) = indentWithOneChild ("TLam " <> show l) x
    alg TLimitedRecursionF = sindent "TLimitedRecursion"

-- |Helper function to indent. Usefull for indented Show instances.
indent :: Int -> String -> String
indent i str = replicate i ' ' <> str

-- |Indentation with the State Monad.
sindent :: String -> State Int String
sindent str = State.get >>= (\i -> pure $ indent i str)

-- |One child indentation.
indentWithOneChild :: String -> State Int String -> State Int String
indentWithOneChild str sx = do
  i <- State.get
  State.put $ i + 2
  x <- sx
  pure $ indent i (str <> "\n") <> x

-- |Two children indentation.
indentWithTwoChildren :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren str sl sr = do
  i <- State.get
  State.put $ i + 2
  l <- sl
  State.put $ i + 2
  r <- sr
  pure $ indent i (str <> "\n") <> l <> "\n" <> r


-- |`dropUntil p xs` drops leading elements until `p $ head xs` is satisfied.
dropUntil :: (a -> Bool) -> [a] -> [a]
dropUntil _ [] = []
dropUntil p x@(x1:_) =
  case p x1 of
    False -> dropUntil p (drop 1 x)
    True  -> x

newtype FragIndex = FragIndex { unFragIndex :: Int } deriving (Eq, Show, Ord, Enum, NFData, Generic)

data FragExpr a
  = ZeroFrag
  | PairFrag (FragExpr a) (FragExpr a)
  | EnvFrag
  | SetEnvFrag (FragExpr a)
  | DeferFrag FragIndex
  | AbortFrag
  | GateFrag (FragExpr a) (FragExpr a)
  | LeftFrag (FragExpr a)
  | RightFrag (FragExpr a)
  | TraceFrag
  | AuxFrag a
  deriving (Eq, Ord)
makeBaseFunctor ''FragExpr -- * Functorial version FragExprF.

instance Show a => Show (FragExpr a) where
  show fexp = State.evalState (cata alg fexp) 0 where
    alg :: (Base (FragExpr a)) (State Int String) -> State Int String
    alg = \case
      ZeroFragF -> sindent "ZeroF"
      (PairFragF sl sr) -> indentWithTwoChildren "PairF" sl sr
      EnvFragF -> sindent "EnvF"
      (SetEnvFragF sx) -> indentWithOneChild "SetEnvF" sx
      (DeferFragF i) -> sindent $ "DeferF " <> show i
      AbortFragF -> sindent "AbortFragF"
      (GateFragF sx sy) -> indentWithTwoChildren "GateF" sx sy
      (LeftFragF sl) -> indentWithOneChild "LeftF" sl
      (RightFragF sr) -> indentWithOneChild "RightF" sr
      TraceFragF -> sindent "TraceF"
      (AuxFragF x) -> sindent $ "AuxF " <> show x


newtype EIndex = EIndex { unIndex :: Int } deriving (Eq, Show, Ord)

data BreakExtras
  = UnsizedRecursion
  deriving Show

type Term1 = ParserTerm String String
type Term2 = ParserTerm () Int

-- |Term3 :: Map FragIndex (FragExpr BreakExtras) -> Term3
newtype Term3 = Term3 (Map FragIndex (FragExpr BreakExtras)) deriving Show
newtype Term4 = Term4 (Map FragIndex (FragExpr Void)) deriving Show

type BreakState a = State (FragIndex, Map FragIndex (FragExpr a))

type BreakState' a = BreakState a (FragExpr a)

type IndExpr = ExprA EIndex

-- instance Show Term3 where
--   show = ppShow

instance EndoMapper IExpr where
  endoMap f Zero       = f Zero
  endoMap f (Pair a b) = f $ Pair (endoMap f a) (endoMap f b)
  endoMap f Env        = f Env
  endoMap f (SetEnv x) = f $ SetEnv (endoMap f x)
  endoMap f (Defer x)  = f $ Defer (endoMap f x)
  endoMap f Abort      = f Abort
  endoMap f (Gate l r) = f $ Gate (endoMap f l) (endoMap f r)
  endoMap f (PLeft x)  = f $ PLeft (endoMap f x)
  endoMap f (PRight x) = f $ PRight (endoMap f x)
  endoMap f Trace      = f Trace

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

class TelomareLike a where
  fromTelomare :: IExpr -> a
  toTelomare :: a -> Maybe IExpr

class TelomareLike a => AbstractRunTime a where
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
varNF n = LeftFrag (iterate RightFrag EnvFrag !! n)

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
countApps x FirstArg          = pure x
countApps x (App SecondArg c) = countApps (x + 1) c
countApps _ _                 = Nothing

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
  pure $ DeferFrag fi

appF :: BreakState' a -> BreakState' a -> BreakState' a
appF c i =
  let twiddleF = deferF $ pure (PairFrag (LeftFrag (RightFrag EnvFrag)) (PairFrag (LeftFrag EnvFrag) (RightFrag (RightFrag EnvFrag))))
  in (\tf p -> SetEnvFrag (SetEnvFrag (PairFrag tf p))) <$> twiddleF <*> (PairFrag <$> i <*> c)

lamF :: BreakState' a -> BreakState' a
lamF x = (\f -> PairFrag f EnvFrag) <$> deferF x

clamF :: BreakState' a -> BreakState' a
clamF x = (\f -> PairFrag f ZeroFrag) <$> deferF x

toChurchF :: Int -> BreakState' a
toChurchF x' =
  let inner 0 = pure $ LeftFrag EnvFrag
      inner x = appF (pure $ LeftFrag (RightFrag EnvFrag)) (inner (x - 1))
  in lamF (lamF (inner x'))

partialFixF :: Int -> BreakState' a
partialFixF i =
  let firstArgF = pure $ LeftFrag EnvFrag
      secondArgF = pure $ LeftFrag (RightFrag EnvFrag)
      abortMessage = s2gF "recursion depth limit exceeded ~"
      abrt = SetEnvFrag . PairFrag AbortFrag <$> abortMessage
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

data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord)

newtype PrettyDataType = PrettyDataType DataType

showInternal :: DataType -> String
showInternal at@(ArrType _ _) = concat ["(", show $ PrettyDataType at, ")"]
showInternal t                = show . PrettyDataType $ t

instance Show PrettyDataType where
  show (PrettyDataType dt) = case dt of
    ZeroType -> "D"
    (ArrType a b) -> concat [showInternal a, " -> ", showInternal b]
    (PairType a b) ->
      concat ["(", show $ PrettyDataType a, ",", show $ PrettyDataType b, ")"]

data PartialType
  = ZeroTypeP
  | AnyType
  | TypeVariable Int
  | ArrTypeP PartialType PartialType
  | PairTypeP PartialType PartialType
  deriving (Show, Eq, Ord)

newtype PrettyPartialType = PrettyPartialType PartialType

showInternalP :: PartialType -> String
showInternalP at@(ArrTypeP _ _) = concat ["(", show $ PrettyPartialType at, ")"]
showInternalP t = show . PrettyPartialType $ t

instance Show PrettyPartialType where
  show (PrettyPartialType dt) = case dt of
    ZeroTypeP -> "Z"
    AnyType -> "A"
    (ArrTypeP a b) -> concat [showInternalP a, " -> ", showInternalP b]
    (PairTypeP a b) ->
      concat ["(", show $ PrettyPartialType a, ",", show $ PrettyPartialType b, ")"]
    (TypeVariable (-1)) -> "badType"
    (TypeVariable x) -> 'v' : show x

instance EndoMapper DataType where
  endoMap f ZeroType       = f ZeroType
  endoMap f (ArrType a b)  = f $ ArrType (endoMap f a) (endoMap f b)
  endoMap f (PairType a b) = f $ PairType (endoMap f a) (endoMap f b)

instance EndoMapper PartialType where
  endoMap f ZeroTypeP        = f ZeroTypeP
  endoMap f AnyType          = f AnyType
  endoMap f (TypeVariable i) = f $ TypeVariable i
  endoMap f (ArrTypeP a b)   = f $ ArrTypeP (endoMap f a) (endoMap f b)
  endoMap f (PairTypeP a b)  = f $ PairTypeP (endoMap f a) (endoMap f b)

mergePairType :: DataType -> DataType
mergePairType = endoMap f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x                            = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = endoMap f where
  f (PairTypeP ZeroTypeP ZeroTypeP) = ZeroTypeP
  f x                               = x

newtype PrettyIExpr = PrettyIExpr IExpr

instance Show PrettyIExpr where
  show (PrettyIExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["(", show (PrettyIExpr a), ",", show (PrettyIExpr b), ")"]
    Zero -> "0"
    x -> show x

g2i :: IExpr -> Int
g2i Zero       = 0
g2i (Pair a b) = 1 + g2i a + g2i b
g2i x          = error $ "g2i " ++ show x

i2g :: Int -> IExpr
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero

ints2g :: [Int] -> IExpr
ints2g = foldr (\i g -> Pair (i2g i) g) Zero

g2Ints :: IExpr -> [Int]
g2Ints Zero       = []
g2Ints (Pair n g) = g2i n : g2Ints g
g2Ints x          = error $ "g2Ints " ++ show x

s2g :: String -> IExpr
s2g = ints2g . map ord

g2s :: IExpr -> String
g2s = map chr . g2Ints

toChurch :: Int -> IExpr
toChurch x =
  let inner 0 = PLeft Env
      inner a = app (PLeft $ PRight Env) (inner (a - 1))
  in lam (lam (inner x))

i2gF :: Int -> BreakState' a
i2gF 0 = pure ZeroFrag
i2gF n = PairFrag <$> i2gF (n - 1) <*> pure ZeroFrag

ints2gF :: [Int] -> BreakState' a
ints2gF = foldr (\i g -> PairFrag <$> i2gF i <*> g) (pure ZeroFrag)

s2gF :: String -> BreakState' a
s2gF = ints2gF . map ord

-- convention is numbers are left-nested pairs with zero on right
isNum :: IExpr -> Bool
isNum Zero          = True
isNum (Pair n Zero) = isNum n
isNum _             = False

nextI :: State EIndex EIndex
nextI = State.state $ \(EIndex n) -> (EIndex n, EIndex (n + 1))

toIndExpr :: IExpr -> State EIndex IndExpr
toIndExpr Zero       = ZeroA <$> nextI
toIndExpr (Pair a b) = PairA <$> toIndExpr a <*> toIndExpr b <*> nextI
toIndExpr Env        = EnvA <$> nextI
toIndExpr (SetEnv x) = SetEnvA <$> toIndExpr x <*> nextI
toIndExpr (Defer x)  = DeferA <$> toIndExpr x <*> nextI
toIndExpr Abort      = AbortA <$> nextI
toIndExpr (Gate l r) = GateA <$> toIndExpr l <*> toIndExpr r <*> nextI
toIndExpr (PLeft x)  = PLeftA <$> toIndExpr x <*> nextI
toIndExpr (PRight x) = PRightA <$> toIndExpr x <*> nextI
toIndExpr Trace      = TraceA <$> nextI

toIndExpr' :: IExpr -> IndExpr
toIndExpr' x = State.evalState (toIndExpr x) (EIndex 0)

instance TelomareLike (ExprT a) where
  fromTelomare = \case
    Zero -> ZeroT
    Pair a b -> PairT (fromTelomare a) (fromTelomare b)
    Env -> EnvT
    SetEnv x -> SetEnvT $ fromTelomare x
    Defer x -> DeferT $ fromTelomare x
    Abort -> AbortT
    Gate l r -> GateT (fromTelomare l) (fromTelomare r)
    PLeft x -> LeftT $ fromTelomare x
    PRight x -> RightT $ fromTelomare x
    Trace -> TraceT
  toTelomare = \case
    ZeroT -> pure Zero
    PairT a b -> Pair <$> toTelomare a <*> toTelomare b
    EnvT -> pure Env
    SetEnvT x -> SetEnv <$> toTelomare x
    DeferT x -> Defer <$> toTelomare x
    AbortT -> pure Abort
    GateT l r -> Gate <$> toTelomare l <*> toTelomare r
    LeftT x -> PLeft <$> toTelomare x
    RightT x -> PRight <$> toTelomare x
    TraceT -> pure Trace
    TagT x _ -> toTelomare x -- just elide tags

telomareToFragmap :: IExpr -> Map FragIndex (FragExpr a)
telomareToFragmap expr = Map.insert (FragIndex 0) bf m where
    (bf, (_,m)) = State.runState (convert expr) (FragIndex 1, Map.empty)
    convert = \case
      Zero -> pure ZeroFrag
      Pair a b -> PairFrag <$> convert a <*> convert b
      Env -> pure EnvFrag
      SetEnv x -> SetEnvFrag <$> convert x
      Defer x -> do
        bx <- convert x
        (fi@(FragIndex i), fragMap) <- State.get
        State.put (FragIndex (i + 1), Map.insert fi bx fragMap)
        pure $ DeferFrag fi
      Abort -> pure AbortFrag
      Gate l r -> GateFrag <$> convert l <*> convert r
      PLeft x -> LeftFrag <$> convert x
      PRight x -> RightFrag <$> convert x
      Trace -> pure TraceFrag

fragmapToTelomare :: Map FragIndex (FragExpr a) -> Maybe IExpr
fragmapToTelomare fragMap = convert (rootFrag fragMap) where
    convert = \case
      ZeroFrag -> pure Zero
      PairFrag a b -> Pair <$> convert a <*> convert b
      EnvFrag -> pure Env
      SetEnvFrag x -> SetEnv <$> convert x
      DeferFrag ind -> Defer <$> (Map.lookup ind fragMap >>= convert)
      AbortFrag -> pure Abort
      GateFrag l r -> Gate <$> convert l <*> convert r
      LeftFrag x -> PLeft <$> convert x
      RightFrag x -> PRight <$> convert x
      TraceFrag -> pure Trace
      AuxFrag _ -> Nothing

instance TelomareLike Term3 where
  fromTelomare = Term3 . telomareToFragmap
  toTelomare (Term3 fragMap) = fragmapToTelomare fragMap

instance TelomareLike Term4 where
  fromTelomare = Term4 . telomareToFragmap
  toTelomare (Term4 fragMap) = fragmapToTelomare fragMap
