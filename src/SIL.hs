{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE StandaloneDeriving #-}
module SIL where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Char
import Data.Functor.Classes
import Data.Functor.Foldable
-- import Prelude hiding (Foldable)

-- if classes were categories, this would be an EndoFunctor?
{-

class EndoMapper a where
  endoMap :: (a -> a) -> a -> a

class EitherEndoMapper a where
  eitherEndoMap :: (a -> Either e a) -> a -> Either e a

class MonoidEndoFolder a where
  monoidFold :: Monoid m => (a -> m) -> a -> m
  -}

{-
data Expr
  = Zero                     -- no special syntax necessary
  | Pair !Expr !Expr       -- {,}
  | Env                      -- identifier
  | SetEnv !Expr
  | Defer !Expr
  | Abort !Expr
  | Gate !Expr
  | PLeft !Expr             -- left
  | PRight !Expr            -- right
  | Trace !Expr             -- trace
  deriving (Eq, Show, Ord)
-}

data ExprF a
  = ZeroF
  | EnvF
  | PairF a a
  | SetEnvF a
  | DeferF a
  | AbortF a
  | GateF a
  | PLeftF a
  | PRightF a
  | TraceF a
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)
  -- deriving Functor
{-
deriving instance Eq a => Eq (ExprF a)
deriving instance Ord a => Ord (ExprF a)
deriving instance Show a => Show (ExprF a)
-}
--instance Eq a => Eq1 (ExprF a) where
instance Eq1 ExprF where
  liftEq f a b = case (a, b) of
    (ZeroF, ZeroF) -> True
    (EnvF, EnvF) -> True
    (PairF a b, PairF c d) -> f a c && f b d
    (SetEnvF a, SetEnvF b) -> f a b
    (DeferF a, DeferF b) -> f a b
    (AbortF a, AbortF b) -> f a b
    (GateF a, GateF b) -> f a b
    (PLeftF a, PLeftF b) -> f a b
    (PRightF a, PRightF b) -> f a b
    (TraceF a, TraceF b) -> f a b
    _ -> False

semiFromEnum :: ExprF a -> Int
semiFromEnum = \case
  ZeroF -> 0
  EnvF -> 1
  PairF _ _ -> 2
  SetEnvF _ -> 3
  DeferF _ -> 4
  AbortF _ -> 5
  GateF _ -> 6
  PLeftF _ -> 7
  PRightF _ -> 8
  TraceF _ -> 9

foldOrder :: [Ordering] -> Ordering
foldOrder [] = EQ
foldOrder (EQ:xs) = foldOrder xs
foldOrder (x:_) = x

instance Ord1 ExprF where
  liftCompare f a b = case (a, b) of
    (PairF a b, PairF c d) -> foldOrder [f a c, f b d]
    (SetEnvF a, SetEnvF b) -> f a b
    (DeferF a, DeferF b) -> f a b
    (AbortF a, AbortF b) -> f a b
    (GateF a, GateF b) -> f a b
    (PLeftF a, PLeftF b) -> f a b
    (PRightF a, PRightF b) -> f a b
    (TraceF a, TraceF b) -> f a b
    (a, b) -> compare (semiFromEnum a) (semiFromEnum b)

instance Show1 ExprF where
  -- liftShowsPrec :: (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> f a -> ShowS
  liftShowsPrec showsPrec showList i = let recur = showsPrec i in \case
    ZeroF -> showString "ZeroF"
    EnvF -> showString "EnvF"
    PairF a b -> showParen True $ shows "PairF " . recur a . shows " " . recur b
    SetEnvF x -> showParen True $ shows "SetEnvF " . recur x
    DeferF x -> showParen True $ shows "DeferF " . recur x
    AbortF x -> showParen True $ shows "AbortF " . recur x
    GateF x -> showParen True $ shows "GateF " . recur x
    PLeftF x -> showParen True $ shows "PLeftF " . recur x
    PRightF x -> showParen True $ shows "PRightF " . recur x
    TraceF x -> showParen True $ shows "TraceF " . recur x

type Expr = Fix ExprF
newtype Expr' = Expr' {getExpr :: Expr } deriving (Eq, Ord, Show)

data ExprAF a f = ExprAF { eanno :: a, exprA :: ExprF f}
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

type ExprA a = Fix (ExprAF a)

--instance Show1 ExprA where
instance Show1 (ExprAF a) where
  liftShowsPrec showsPrec showList i = liftShowsPrec showsPrec showList i . exprA

{-
data ExprA a
  = ZeroA a
  | PairA (ExprA a) (ExprA a) a
  | EnvA a
  | SetEnvA (ExprA a) a
  | DeferA (ExprA a) a
  | AbortA (ExprA a) a
  | GateA (ExprA a) a
  | PLeftA (ExprA a) a
  | PRightA (ExprA a) a
  | TraceA (ExprA a) a
  deriving (Eq, Ord, Show)

-- there must be a typeclass I can derive that does this
getA :: ExprA a -> a
getA (ZeroA a) = a
getA (PairA _ _ a) = a
getA (EnvA a) = a
getA (SetEnvA _ a) = a
getA (DeferA _ a) = a
getA (AbortA _ a) = a
getA (GateA _ a) = a
getA (PLeftA _ a) = a
getA (PRightA _ a) = a
getA (TraceA _ a) = a
-}

newtype EIndex = EIndex { unIndex :: Int } deriving (Eq, Show, Ord)

type IndExpr = ExprA EIndex

  --endoMap :: (a -> a) -> a -> a
  --eitherEndoMap :: (a -> Either e a) -> a -> Either e a
  --monoidFold :: Monoid m => (a -> m) -> a -> m
{-
endoMap, eitherEndoMap, monoidFold :: Functor f => (a -> b) -> f a -> f b
endoMap = fmap
eitherEndoMap = fmap
monoidFold = fmap
-}

{-
instance EndoMapper Expr where
  endoMap f Zero = f Zero
  endoMap f (Pair a b) = f $ Pair (endoMap f a) (endoMap f b)
  endoMap f Env = f Env
  endoMap f (SetEnv x) = f $ SetEnv (endoMap f x)
  endoMap f (Defer x) = f $ Defer (endoMap f x)
  endoMap f (Abort x) = f $ Abort (endoMap f x)
  endoMap f (Gate g) = f $ Gate (endoMap f g)
  endoMap f (PLeft x) = f $ PLeft (endoMap f x)
  endoMap f (PRight x) = f $ PRight (endoMap f x)
  endoMap f (Trace x) = f $ Trace (endoMap f x)

instance EitherEndoMapper Expr where
  eitherEndoMap f Zero = f Zero
  eitherEndoMap f (Pair a b) = (Pair <$> eitherEndoMap f a <*> eitherEndoMap f b) >>= f
  eitherEndoMap f Env = f Env
  eitherEndoMap f (SetEnv x) = (SetEnv <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (Defer x) = (Defer <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (Abort x) = (Abort <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (Gate x) = (Gate <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (PLeft x) = (PLeft <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (PRight x) = (PRight <$> eitherEndoMap f x) >>= f
  eitherEndoMap f (Trace x) = (Trace <$> eitherEndoMap f x) >>= f

instance MonoidEndoFolder Expr where
  monoidFold f Zero = f Zero
  monoidFold f (Pair a b) = mconcat [f (Pair a b), monoidFold f a, monoidFold f b]
  monoidFold f Env = f Env
  monoidFold f (SetEnv x) = mconcat [f (SetEnv x), monoidFold f x]
  monoidFold f (Defer x) = mconcat [f (Defer x), monoidFold f x]
  monoidFold f (Abort x) = mconcat [f (Abort x), monoidFold f x]
  monoidFold f (Gate x) = mconcat [f (Gate x), monoidFold f x]
  monoidFold f (PLeft x) = mconcat [f (PLeft x), monoidFold f x]
  monoidFold f (PRight x) = mconcat [f (PRight x), monoidFold f x]
  monoidFold f (Trace x) = mconcat [f (Trace x), monoidFold f x]
-}

instance NFData Expr' where
  rnf = (. getExpr) $ cata (\case
     ZeroF         -> ()
     (PairF e1 e2) -> rnf e1 `seq` rnf e2
     EnvF          -> ()
     (SetEnvF  e)  -> rnf e
     (DeferF   e)  -> rnf e
     (AbortF   e)  -> rnf e
     (GateF    e)  -> rnf e
     (PLeftF   e)  -> rnf e
     (PRightF  e)  -> rnf e
     (TraceF   e)  -> rnf e
     )

data RunTimeError
  = AbortRunTime Expr
  | SetEnvError Expr
  | GenericRunTimeError String Expr
  | ResultConversionError String
  deriving (Eq, Ord)

instance Show RunTimeError where
  show (AbortRunTime a) = "Abort: " <> (show $ g2s a)
  show (SetEnvError e) = "Can't SetEnv: " <> show (PrettyExpr e)
  show (GenericRunTimeError s i) = "Generic Runtime Error: " <> s <> " -- " <> show (PrettyExpr i)
  show (ResultConversionError s) = "Couldn't convert runtime result to Expr: " <> s

type RunResult = ExceptT RunTimeError IO

class AbstractRunTime a where
  eval :: a -> RunResult a
  fromSIL :: Expr -> a
  toSIL :: a -> Maybe Expr

zero :: Expr
zero = Fix ZeroF
pair :: Expr -> Expr -> Expr
pair a b = Fix $ PairF a b
var :: Expr
var = Fix EnvF
env :: Expr
env = Fix EnvF
twiddle :: Expr -> Expr
twiddle x = setenv (pair (defer (pair (pleft (pright env)) (pair (pleft env) (pright (pright env))))) x)
app :: Expr -> Expr -> Expr
--app c i = setenv (twiddle (pair i c))
app c i = setenv (setenv (pair (defer (pair (pleft (pright env)) (pair (pleft env) (pright (pright env)))))
                          (pair i c)))
check :: Expr -> Expr -> Expr -- TODO we're going to change semantics of Abort, right?
check c tc = setenv (pair (defer (ite
                                  (app (pleft env) (pright env))
                                  (Fix . AbortF $ app (pleft env) (pright env))
                                  (pright env)
                           ))
                           (pair tc c)
                    )
gate :: Expr -> Expr
gate = Fix . GateF
pleft :: Expr -> Expr
pleft = Fix . PLeftF
pright :: Expr -> Expr
pright = Fix . PRightF
setenv :: Expr -> Expr
setenv = Fix . SetEnvF
defer :: Expr -> Expr
defer = Fix . DeferF
traceE :: Expr -> Expr
traceE = Fix . TraceF

lam :: Expr -> Expr
lam x = pair (defer x) env
-- a form of lambda that does not pull in a surrounding environment
completeLam :: Expr -> Expr
completeLam x = pair (defer x) zero
ite :: Expr -> Expr -> Expr -> Expr
ite i t e = setenv (pair (gate i) (pair e t))
varN :: Int -> Expr
varN n = pleft (iterate pright env !! n)

-- make sure these patterns are in exact correspondence with the shortcut functions above
pattern Env :: Expr
pattern Env = Fix EnvF
pattern Zero :: Expr
pattern Zero = Fix ZeroF
pattern PLeft :: Expr -> Expr
pattern PLeft x = Fix (PLeftF x)
pattern PRight :: Expr -> Expr
pattern PRight x = Fix (PRightF x)
pattern Defer :: Expr -> Expr
pattern Defer x = Fix (DeferF x)
pattern SetEnv :: Expr -> Expr
pattern SetEnv x = Fix (SetEnvF x)
pattern Gate :: Expr -> Expr
pattern Gate x = Fix (GateF x)
pattern Abort :: Expr -> Expr
pattern Abort x = Fix (AbortF x)
pattern Trace :: Expr -> Expr
pattern Trace x = Fix (TraceF x)
pattern Pair :: Expr -> Expr -> Expr
pattern Pair a b = Fix (PairF a b)
pattern FirstArg :: Expr
pattern FirstArg = PLeft Env
pattern SecondArg :: Expr
pattern SecondArg = PLeft (PRight Env)
pattern ThirdArg :: Expr
pattern ThirdArg = PLeft (PRight (PRight Env))
pattern FourthArg :: Expr
pattern FourthArg = PLeft (PRight (PRight (PRight Env)))
pattern Lam :: Expr -> Expr
pattern Lam x = Pair (Defer x) Env
pattern App :: Expr -> Expr -> Expr
pattern App c i = SetEnv (SetEnv (Pair (Defer (Pair (PLeft (PRight Env)) (Pair (PLeft Env) (PRight (PRight Env)))))
                          (Pair i c)))
pattern TwoArgFun :: Expr -> Expr
pattern TwoArgFun c = Pair (Defer (Pair (Defer c) Env)) Env
pattern ITE :: Expr -> Expr -> Expr -> Expr
pattern ITE i t e = SetEnv (Pair (Gate i) (Pair e t))

countApps :: Int -> Expr -> Maybe Int
countApps x FirstArg = pure x
countApps x (App SecondArg c) = countApps (x + 1) c
countApps _ _ = Nothing

pattern ChurchNum :: Int -> Expr
pattern ChurchNum x <- TwoArgFun (countApps 0 -> Just x)

pattern ToChurch :: Expr
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
{-
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
pattern ITEA i t e <- SetEnvA (PairA (GateA i _) (PairA e t _) _) _
-- TODO check if these make sense at all. A church type should have two arguments (lamdas), but the inner lambdas
-- for addition/multiplication should be f, f+x rather than m+n
-- no, it does not, in \m n f x -> m f (n f x), m and n are FourthArg and ThirdArg respectively
pattern PlusA :: ExprA a -> ExprA a -> ExprA a
pattern PlusA m n <- LamA (LamA (AppA (AppA m SecondArgA) (AppA (AppA n SecondArgA) FirstArgA)))
pattern MultA :: ExprA a -> ExprA a -> ExprA a
pattern MultA m n <- LamA (AppA m (AppA n FirstArgA))
-}

{-
data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord)
-}
data DataTypeF a
  = DataOnlyTypeF
  | ArrTypeF a a
  | PairTypeF a a
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

type DataType = Fix DataTypeF

pattern DataOnlyType = Fix DataOnlyTypeF
pattern ArrType a b = Fix (ArrTypeF a b)
pattern PairType a b = Fix (PairTypeF a b)

newtype PrettyDataType = PrettyDataType {getPrettyDataType :: DataType}

instance Eq1 DataTypeF where
  liftEq f a b = case (a, b) of
    (DataOnlyTypeF, DataOnlyTypeF) -> True
    (ArrTypeF a b, ArrTypeF c d) -> f a c && f b d
    (PairTypeF a b, PairTypeF c d) -> f a c && f b d
    _ -> False

dataTypePartialEnum :: DataTypeF a -> Int
dataTypePartialEnum = \case
  DataOnlyTypeF -> 0
  ArrTypeF _ _ -> 1
  PairTypeF _ _ -> 2

instance Ord1 DataTypeF where
  liftCompare f a b = case (a, b) of
    (ArrTypeF a b, ArrTypeF c d) -> foldOrder [f a c, f b d]
    (PairTypeF a b, PairTypeF c d) -> foldOrder [f a c, f b d]
    (a, b) -> compare (dataTypePartialEnum a) (dataTypePartialEnum b)

instance Show1 DataTypeF where
  liftShowsPrec showsPrec showList i = let recur = showsPrec i in \case
    DataOnlyTypeF -> showString "DataOnlyTypeF"
    ArrTypeF a b -> showParen True $ shows "ArrTypeF " . recur a . shows " " . recur b
    PairTypeF a b -> showParen True $ shows "PairTypeF " . recur a . shows " " . recur b

-- showInternal at@(ArrType _ _) = concat ["(", show $ PrettyDataType at, ")"]
-- showInternal t = show . PrettyDataType $ t


-- can we make this more generic so that it can be reused for PrettyPartialTypes?
-- showBasicType :: DataTypeF (DataTypeF a, String) -> String
showBasicType = \case
    DataOnlyTypeF -> "D"
    (ArrTypeF (Fix (ArrTypeF _ _), sa) (_, sb)) -> "(" <> sa <> ")" <> " -> " <> sb
    (ArrTypeF (_, sa) (_, sb)) -> sa <> " -> " <> sb
    (PairTypeF (_, sa) (_, sb)) -> "{" <> sa <> "," <> sb <> "}"

instance Show PrettyDataType where
  {-
  show (PrettyDataType dt) = case dt of
    ZeroType -> "D"
    (ArrType a b) -> concat [showInternal a, " -> ", showInternal b]
    (PairType a b) ->
      concat ["{", show $ PrettyDataType a, ",", show $ PrettyDataType b, "}"]
-}
  show = para showBasicType . getPrettyDataType

{-
data PartialType
  = ZeroTypeP
  | AnyType
  | TypeVariable Int
  | ArrTypeP PartialType PartialType
  | PairTypeP PartialType PartialType
  deriving (Show, Eq, Ord)
-}
data PartialTypeF a
  {-
  = ZeroTypePF
  | AnyTypeF
  | TypeVariableF Int
  | ArrTypePF a a
  | PairTypePF a a
-}
  = SimpleTypeF (DataTypeF a)
  | AnyTypeF
  | TypeVariableF Int
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

pattern AnyType = Fix AnyTypeF
pattern TypeVariable i = Fix (TypeVariableF i)
pattern DataOnlyTypeP = Fix (SimpleTypeF (DataOnlyTypeF))
pattern PairTypeP a b = Fix (SimpleTypeF (PairTypeF a b))
pattern ArrTypeP a b = Fix (SimpleTypeF (ArrTypeF a b))

type PartialType = Fix PartialTypeF

instance Eq1 PartialTypeF where
  liftEq f a b = case (a, b) of
    (AnyTypeF, AnyTypeF) -> True
    (TypeVariableF a, TypeVariableF b) -> a == b
    (SimpleTypeF a, SimpleTypeF b) -> liftEq f a b
    _ -> False

partialTypePartialEnum :: PartialTypeF a -> Int
partialTypePartialEnum = \case
  AnyTypeF -> 0
  TypeVariableF _ -> 1
  SimpleTypeF _ -> 2

instance Ord1 PartialTypeF where
  liftCompare f a b = case (a, b) of
    (TypeVariableF a, TypeVariableF b) -> compare a b
    (SimpleTypeF a, SimpleTypeF b) -> liftCompare f a b
    (a, b) -> compare (partialTypePartialEnum a) (partialTypePartialEnum b)

instance Show1 PartialTypeF where
  liftShowsPrec showsPrec showList i = let recur = showsPrec i in \case
    AnyTypeF -> showString "AnyTpeF"
    TypeVariableF i -> showParen True $ shows "TypeVariableF " . shows i
    SimpleTypeF x -> liftShowsPrec showsPrec showList i x

newtype PrettyPartialType = PrettyPartialType {getPrettyPartialType :: PartialType}

-- showInternalP at@(ArrTypeP _ _) = concat ["(", show $ PrettyPartialType at, ")"]
-- showInternalP t = show . PrettyPartialType $ t

instance Show PrettyPartialType where
  show = para showOne . getPrettyPartialType where
    showOne (SimpleTypeF (DataOnlyTypeF)) = "D"
    showOne (SimpleTypeF (ArrTypeF ((Fix (SimpleTypeF (ArrTypeF _ _))), sa) (_, sb))) = "(" <> sa <> ")" <> " -> " <> sb
    showOne (SimpleTypeF (ArrTypeF (_, sa) (_, sb))) = sa <> " -> " <> sb
    showOne (SimpleTypeF (PairTypeF (_, sa) (_, sb))) = "{" <> sa <> "," <> sb <> "}"
    -- showOne (SimpleTypeF x) = showBasicType x
    showOne AnyTypeF = "A"
    showOne (TypeVariableF (-1)) = "badType"
    showOne (TypeVariableF i) = 'v' : show i
  {-
  show (PrettyPartialType dt) = case dt of
    ZeroTypeP -> "Z"
    AnyType -> "A"
    (ArrTypeP a b) -> concat [showInternalP a, " -> ", showInternalP b]
    (PairTypeP a b) ->
      concat ["{", show $ PrettyPartialType a, ",", show $ PrettyPartialType b, "}"]
    (TypeVariable (-1)) -> "badType"
    (TypeVariable x) -> 'v' : show x
-}

{-
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
-}

{-
mergePairType :: DataType -> DataType
mergePairType = endoMap f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = endoMap f where
  f (PairTypeP ZeroTypeP ZeroTypeP) = ZeroTypeP
  f x = x
-}
mergePairType :: DataType -> DataType
mergePairType = cata $ \case
  (PairTypeF DataOnlyType DataOnlyType) -> DataOnlyType
  x -> Fix x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = cata $ \case
  (SimpleTypeF (PairTypeF DataOnlyTypeP DataOnlyTypeP)) -> DataOnlyTypeP
  x -> Fix x

newtype PrettyExpr = PrettyExpr {getExprP :: Expr}

instance Show PrettyExpr where
  {-
  show (PrettyExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["{", show (PrettyExpr a), ",", show (PrettyExpr b), "}"]
    Zero -> "0"
    x -> show x
-}
  show = (. getExprP) $ para (\case
    -- x | isnNum x -> show $ g2i x
    --(PairF a b) -> "{" <> a <> "," <> "}"
    ZeroF -> "0"
    (PairF (ia, a) (_, b)) -> case g2i ia of
      Just n -> show $ n + 1
      _ -> "{" <> a <> "," <> a <> "}"
    x -> show $ fmap snd x
    )

g2i :: Expr -> Maybe Int
{-
g2i Zero = 0
g2i (Pair a b) = 1 + (g2i a) + (g2i b)
g2i x = error $ "g2i " ++ (show x)
-}
g2i = cata $ \case
  ZeroF -> pure 0
  PairF a Nothing -> succ <$> a
  _ -> Nothing

i2g :: Int -> Expr
{-
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero
-}
i2g = ana $ \case
  0 -> ZeroF
  n -> PairF (n - 1) 0

ints2g :: [Int] -> Expr
ints2g = foldr (\i g -> Fix $ PairF (i2g i) g) $ Fix ZeroF

g2Ints :: Expr -> Maybe [Int]
g2Ints (Fix ZeroF) = pure []
g2Ints (Fix (PairF n g)) = (:) <$> g2i n <*> g2Ints g
-- g2Ints x = error $ "g2Ints " ++ show x
g2Ints _ = Nothing

s2g :: String -> Expr
s2g = ints2g . map ord

g2s :: Expr -> Maybe String
g2s = fmap (map chr) . g2Ints

-- convention is numbers are left-nested pairs with zero on right
isNum :: Expr -> Bool
{-
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False
-}
isNum = not . null . g2i

nextI :: State EIndex EIndex
nextI = state $ \(EIndex n) -> ((EIndex n), EIndex (n + 1))

toIndExpr :: Expr -> State EIndex IndExpr
toIndExpr = cata $ \x -> do
  ind <- nextI
  (Fix . ExprAF ind) <$> sequence x
  {-
  (ind :<) <$> case x of
    PairF a b -> Pair <$> a <*> b
    _ -> Fix <$> sequence x
-}
    
{-
toIndExpr Zero = ZeroA <$> nextI
toIndExpr (Pair a b) = PairA <$> toIndExpr a <*> toIndExpr b <*> nextI
toIndExpr Env = EnvA <$> nextI
toIndExpr (SetEnv x) = SetEnvA <$> toIndExpr x <*> nextI
toIndExpr (Defer x) = DeferA <$> toIndExpr x <*> nextI
toIndExpr (Abort x) = AbortA <$> toIndExpr x <*> nextI
toIndExpr (Gate x) = GateA <$> toIndExpr x <*> nextI
toIndExpr (PLeft x) = PLeftA <$> toIndExpr x <*> nextI
toIndExpr (PRight x) = PRightA <$> toIndExpr x <*> nextI
toIndExpr (Trace x) = TraceA <$> toIndExpr x <*> nextI
-}

toIndExpr' :: Expr -> IndExpr
toIndExpr' x = evalState (toIndExpr x) (EIndex 0)
