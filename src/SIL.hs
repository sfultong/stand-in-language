{-#LANGUAGE PatternSynonyms #-}
{-#LANGUAGE ViewPatterns #-}
{-#LANGUAGE LambdaCase #-}
module SIL where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Char

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
  | Gate
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
  | GateA a
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
  | GateT
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
getA (GateA a) = a
getA (PLeftA _ a) = a
getA (PRightA _ a) = a
getA (TraceA a) = a

newtype EIndex = EIndex { unIndex :: Int } deriving (Eq, Show, Ord)

type IndExpr = ExprA EIndex

instance EndoMapper IExpr where
  endoMap f Zero = f Zero
  endoMap f (Pair a b) = f $ Pair (endoMap f a) (endoMap f b)
  endoMap f Env = f Env
  endoMap f (SetEnv x) = f $ SetEnv (endoMap f x)
  endoMap f (Defer x) = f $ Defer (endoMap f x)
  endoMap f Abort = f Abort
  endoMap f Gate = f Gate
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
  eitherEndoMap f Gate = f Gate
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
  monoidFold f Gate = f Gate
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
  rnf Gate         = ()
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
silTrace :: IExpr -> IExpr
silTrace x = SetEnv (Pair Trace x)
gate :: IExpr -> IExpr
gate x = SetEnv (Pair Gate x)
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
ite i t e = setenv (pair (gate i) (pair e t))
varN :: Int -> IExpr
varN n = pleft (iterate pright env !! n)

-- make sure these patterns are in exact correspondence with the shortcut functions above
pattern FirstArg :: IExpr
pattern FirstArg <- PLeft Env
pattern SecondArg :: IExpr
pattern SecondArg <- PLeft (PRight Env)
pattern ThirdArg :: IExpr
pattern ThirdArg <- PLeft (PRight (PRight Env))
pattern FourthArg :: IExpr
pattern FourthArg <- PLeft (PRight (PRight (PRight Env)))
pattern Lam :: IExpr -> IExpr
pattern Lam x <- Pair (Defer x) Env
pattern App :: IExpr -> IExpr -> IExpr
pattern App c i <- SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env)))))
                          (Pair i c)))
pattern TwoArgFun :: IExpr -> IExpr
pattern TwoArgFun c <- Pair (Defer (Pair (Defer c) Env)) Env
pattern ITE :: IExpr -> IExpr -> IExpr -> IExpr
pattern ITE i t e = SetEnv (Pair (SetEnv (Pair Gate i)) (Pair e t))

countApps :: Int -> IExpr -> Maybe Int
countApps x FirstArg = pure x
countApps x (App SecondArg c) = countApps (x + 1) c
countApps _ _ = Nothing

pattern ChurchNum :: Int -> IExpr
pattern ChurchNum x <- TwoArgFun (countApps 0 -> Just x)

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
pattern ITEA :: ExprA a -> ExprA a -> ExprA a -> ExprA a
pattern ITEA i t e <- SetEnvA (PairA (SetEnvA (PairA (GateA _) i _) _) (PairA e t _) _) _
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

-- convention is numbers are left-nested pairs with zero on right
isNum :: IExpr -> Bool
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False

nextI :: State EIndex EIndex
nextI = state $ \(EIndex n) -> (EIndex n, EIndex (n + 1))

toIndExpr :: IExpr -> State EIndex IndExpr
toIndExpr Zero = ZeroA <$> nextI
toIndExpr (Pair a b) = PairA <$> toIndExpr a <*> toIndExpr b <*> nextI
toIndExpr Env = EnvA <$> nextI
toIndExpr (SetEnv x) = SetEnvA <$> toIndExpr x <*> nextI
toIndExpr (Defer x) = DeferA <$> toIndExpr x <*> nextI
toIndExpr Abort = AbortA <$> nextI
toIndExpr Gate = GateA <$> nextI
toIndExpr (PLeft x) = PLeftA <$> toIndExpr x <*> nextI
toIndExpr (PRight x) = PRightA <$> toIndExpr x <*> nextI
toIndExpr Trace = TraceA <$> nextI

toIndExpr' :: IExpr -> IndExpr
toIndExpr' x = evalState (toIndExpr x) (EIndex 0)

instance SILLike (ExprT a) where
  fromSIL = \case
    Zero -> ZeroT
    Pair a b -> PairT (fromSIL a) (fromSIL b)
    Env -> EnvT
    SetEnv x -> SetEnvT $ fromSIL x
    Defer x -> DeferT $ fromSIL x
    Abort -> AbortT
    Gate -> GateT
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
    GateT -> pure Gate
    LeftT x -> PLeft <$> toSIL x
    RightT x -> PRight <$> toSIL x
    TraceT -> pure Trace
    TagT x _ -> toSIL x -- just elide tags

{-
instance 

toIndexedExpr :: (ExprT a -> Bool) -> IExpr -> State EIndex (ExprT EIndex)
toIndexedExpr f expr =
  let 
-}
