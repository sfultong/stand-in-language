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

module Telomare where --(IExpr(..), ParserTerm(..), LamType(..), Term1(..), Term2(..), Term3(..), Term4(..)
               --, FragExpr(..), FragIndex, TelomareLike, fromTelomare, toTelomare, rootFrag) where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Lens.Combinators
import           Control.Lens.Plated
import           Control.Monad.Except
import           Control.Monad.State      (State)
import qualified Control.Monad.State      as State
import           Data.Char
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set
import           Data.Void
import           GHC.Generics

{- top level TODO list
 - change AbortFrag form to something more convenient
 - extract abort logic from arbitrary expressions (like, make quick dynamic check the way we have static check)
 - make sure recur calls in unsized recursion combinator are structurally smaller ... although, we can fail sizing and report that to user
-}
-- TODO replace with a Plated fold
class MonoidEndoFolder a where
  monoidFold :: Monoid m => (a -> m) -> a -> m

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- (,)
  | Env                      -- identifier
  | SetEnv !IExpr -- SetEnv takes a Pair where the right part is Env and the left part is Defer. Inside the Defer is a closed lambda with all argument information on the right (i.e. Env)
  | Defer !IExpr
  -- the rest of these should be no argument constructors, to be treated as functions with setenv
  | Gate !IExpr !IExpr
  | PLeft !IExpr             -- left
  | PRight !IExpr            -- right
  | Trace
  deriving (Eq, Show, Ord, Read)
makeBaseFunctor ''IExpr -- Functorial version IExprF.

instance Plated IExpr where
  plate f = \case
    Pair a b -> Pair <$> f a <*> f b
    SetEnv x -> SetEnv <$> f x
    Defer x  -> Defer <$> f x
    Gate l r -> Gate <$> f l <*> f r
    PLeft x  -> PLeft <$> f x
    PRight x -> PRight <$> f x
    x        -> pure x

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
  | THash (ParserTerm l v)
  | TLam (LamType l) (ParserTerm l v)
  | TLimitedRecursion (ParserTerm l v) (ParserTerm l v) (ParserTerm l v)
  deriving (Eq, Ord, Functor, Foldable, Traversable)
makeBaseFunctor ''ParserTerm -- Functorial version ParserTermF

instance Plated (ParserTerm l v) where
  plate f = \case
    TITE i t e -> TITE <$> f i <*> f t <*> f e
    TPair a b  -> TPair <$> f a <*> f b
    TApp u x   -> TApp <$> f u <*> f x
    TLam s x   -> TLam s <$> f x
    TLeft x    -> TLeft <$> f x
    TRight x   -> TRight <$> f x
    TTrace x   -> TTrace <$> f x
    THash x    -> THash <$> f x
    TCheck c x -> TCheck <$> f c <*> f x
    x          -> pure x


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
    alg (THashF x) = indentWithOneChild "THash" x
    alg (TLamF l x) = indentWithOneChild ("TLam " <> show l) x
    alg (TLimitedRecursionF t r b) = indentWithThreeChildren "TLimitedRecursion" t  r  b

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

indentWithOneChild' :: String -> State Int String -> State Int String
indentWithOneChild' str sx = do
  i <- State.get
  State.put $ i + 2
  x <- sx
  pure $ str <> " " <> x

indentWithTwoChildren' :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren' str sl sr = do
  i <- State.get
  State.put $ i + 2
  l <- sl
  State.put $ i + 2
  r <- sr
  -- pure $ indent i (str <> "\n") <> l <> "\n" <> r
  pure $ str <> " " <> l <> "\n" <> indent (i + 2) r

indentWithChildren' :: String -> [State Int String] -> State Int String
indentWithChildren' str l = do
  i <- State.get
  let doLine = (liftA (<> "\n" <> indent (i + 2) "")) . (State.put (i + 2) >>)
  foldl (\s c -> (<>) <$> s <*> c) (pure $ str <> " ") $ map doLine l

-- |Two children indentation.
indentWithTwoChildren :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren str sl sr = do
  i <- State.get
  State.put $ i + 2
  l <- sl
  State.put $ i + 2
  r <- sr
  pure $ indent i (str <> "\n") <> l <> "\n" <> r

indentWithThreeChildren :: String -> State Int String -> State Int String -> State Int String -> State Int String
indentWithThreeChildren str sa sb sc = do
  i <- State.get
  State.put $ i + 2
  a <- sa
  State.put $ i + 2
  b <- sb
  State.put $ i + 2
  c <- sc
  pure $ indent i (str <> "\n") <> a <> "\n" <> b <> "\n" <> c

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
  deriving (Eq, Ord, Generic, NFData)
makeBaseFunctor ''FragExpr -- Functorial version FragExprF.

instance Plated (FragExpr a) where
  plate f = \case
    PairFrag a b -> PairFrag <$> f a <*> f b
    SetEnvFrag x -> SetEnvFrag <$> f x
    GateFrag l r -> GateFrag <$> f l <*> f r
    LeftFrag x   -> LeftFrag <$> f x
    RightFrag x  -> RightFrag <$> f x
    x            -> pure x

showFragAlg :: Show a => (Base (FragExpr a)) (State Int String) -> State Int String
showFragAlg = \case
      ZeroFragF         -> sindent "ZeroF"
      (PairFragF sl sr) -> indentWithTwoChildren "PairF" sl sr
      EnvFragF          -> sindent "EnvF"
      (SetEnvFragF sx)  -> indentWithOneChild "SetEnvF" sx
      (DeferFragF i)    -> sindent $ "DeferF " <> show i
      AbortFragF        -> sindent "AbortFragF"
      (GateFragF sx sy) -> indentWithTwoChildren "GateF" sx sy
      (LeftFragF sl)    -> indentWithOneChild "LeftF" sl
      (RightFragF sr)   -> indentWithOneChild "RightF" sr
      TraceFragF        -> sindent "TraceF"
      (AuxFragF x)      -> sindent $ "AuxF " <> show x

instance Show a => Show (FragExpr a) where
  show fexp = State.evalState (cata showFragAlg fexp) 0

newtype EIndex = EIndex { unIndex :: Int } deriving (Eq, Show, Ord)

newtype UnsizedRecursionToken = UnsizedRecursionToken { unUnsizedRecursionToken :: Int } deriving (Eq, Ord, Show, Enum, NFData, Generic)

data RecursionSimulationPieces a
  = NestedSetEnvs UnsizedRecursionToken
  | SizingWrapper UnsizedRecursionToken a
  deriving (Eq, Ord, Show, NFData, Generic)

newtype FragExprUR = FragExprUR { unFragExprUR :: FragExpr (RecursionSimulationPieces FragExprUR) }
  deriving (Eq, Show, NFData, Generic)

type RecursionPieceFrag = RecursionSimulationPieces FragExprUR

type Term1 = ParserTerm String String
type Term2 = ParserTerm () Int

-- |Term3 :: Map FragIndex (FragExpr BreakExtras) -> Term3
newtype Term3 = Term3 (Map FragIndex FragExprUR) deriving (Eq, Show, Generic, NFData)
newtype Term4 = Term4 (Map FragIndex (FragExpr Void)) deriving (Eq, Show)

type BreakState a b = State (b, FragIndex, Map FragIndex (FragExpr a))

type BreakState' a b = BreakState a b (FragExpr a)

type IndExpr = ExprA EIndex

-- instance Show Term3 where
--   show = ppShow

instance MonoidEndoFolder IExpr where
  monoidFold f Zero = f Zero
  monoidFold f (Pair a b) = mconcat [f (Pair a b), monoidFold f a, monoidFold f b]
  monoidFold f Env = f Env
  monoidFold f (SetEnv x) = mconcat [f (SetEnv x), monoidFold f x]
  monoidFold f (Defer x) = mconcat [f (Defer x), monoidFold f x]
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
varN n = if n < 0
  then error ("varN invalid debruijin index " <> show n)
  else pleft (iterate pright env !! n)

varNF :: Int -> FragExpr a
varNF n = if n < 0
  then error ("varN invalid debruijin index " <> show n)
  else LeftFrag (iterate RightFrag EnvFrag !! n)

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

deferF :: BreakState' a b -> BreakState' a b
deferF x = do
  bx <- x
  (uri, fi@(FragIndex i), fragMap) <- State.get
  State.put (uri, FragIndex (i + 1), Map.insert fi bx fragMap)
  pure $ DeferFrag fi

pairF :: BreakState' a b -> BreakState' a b -> BreakState' a b
pairF = liftA2 PairFrag

appF :: BreakState' a b -> BreakState' a b -> BreakState' a b
appF c i =
  let twiddleF = deferF $ pure (PairFrag (LeftFrag (RightFrag EnvFrag)) (PairFrag (LeftFrag EnvFrag) (RightFrag (RightFrag EnvFrag))))
  in (\tf p -> SetEnvFrag (SetEnvFrag (PairFrag tf p))) <$> twiddleF <*> (PairFrag <$> i <*> c)

lamF :: BreakState' a b -> BreakState' a b
lamF x = pairF (deferF x) $ pure EnvFrag

clamF :: BreakState' a b -> BreakState' a b
clamF x = pairF (deferF x) $ pure ZeroFrag

innerChurchF :: Int -> BreakState' a b
innerChurchF x = if x < 0
  then error ("innerChurchF called with " <> show x)
  else pure $ iterate SetEnvFrag EnvFrag !! x

iteF :: BreakState' a b -> BreakState' a b -> BreakState' a b -> BreakState' a b
-- iteF i t e = (\ii tt ee -> SetEnvFrag (PairFrag (GateFrag  ee tt) ii)) <$> i <*> t <*> e
iteF = liftA3 (\ii tt ee -> SetEnvFrag (PairFrag (GateFrag  ee tt) ii))

-- to construct a church numeral (\f x -> f ... (f x))
-- the new, optimized church numeral operation iterates on a function "frame" (rf, (rf, (f', (x, env'))))
-- rf is the function to pull arguments out of the frame, run f', and construct the next frame
-- (f',env') is f (since f may contain a saved environment/closure env we want to use for each iteration)
unsizedRecursionWrapper :: UnsizedRecursionToken -> BreakState' RecursionPieceFrag UnsizedRecursionToken
  -> BreakState' RecursionPieceFrag UnsizedRecursionToken
  -> BreakState' RecursionPieceFrag UnsizedRecursionToken
  -> BreakState' RecursionPieceFrag UnsizedRecursionToken
unsizedRecursionWrapper urToken t r b =
  let firstArgF = pure $ LeftFrag EnvFrag
      secondArgF = pure $ LeftFrag (RightFrag EnvFrag)
      thirdArgF = pure . LeftFrag . RightFrag . RightFrag $ EnvFrag
      fourthArgF = pure . LeftFrag . RightFrag . RightFrag . RightFrag $ EnvFrag
      fifthArgF = pure . LeftFrag . RightFrag . RightFrag . RightFrag . RightFrag $ EnvFrag
      abortToken = PairFrag ZeroFrag ZeroFrag
      -- b is on the stack when this is called, so args are (i, (b, 0))
      abrt = lamF (SetEnvFrag <$> (PairFrag (SetEnvFrag (PairFrag AbortFrag abortToken)) <$> appF secondArgF firstArgF))
      applyF = SetEnvFrag $ RightFrag EnvFrag
      env' = RightFrag (RightFrag (RightFrag EnvFrag))
      -- takes (rf, (f', (x, env'))), executes f' with (x, env') and creates a new frame
      rf = deferF . pure $ PairFrag (LeftFrag EnvFrag) (PairFrag (LeftFrag EnvFrag) (PairFrag (LeftFrag (RightFrag EnvFrag))
                                                                                                (PairFrag applyF env')))
      -- construct the initial frame from f and x ((b, (rWrap, 0)) -> (rf, (rf, (f', (x, env')))))
      frameSetup = (\ff a -> PairFrag ff (PairFrag ff (PairFrag (LeftFrag (LeftFrag (RightFrag EnvFrag)))
                                                     (PairFrag a (RightFrag (LeftFrag (RightFrag EnvFrag)))))))
                   <$> rf <*> abrt
      -- run the iterations x' number of times, then unwrap the result from the final frame
      unwrapFrame = LeftFrag . RightFrag . RightFrag . RightFrag . AuxFrag $ NestedSetEnvs urToken
      wrapU = fmap (AuxFrag . SizingWrapper urToken . FragExprUR)
      -- \t r b r' i -> if t i then r r' i else b i -- t r b are already on the stack when this is evaluated
      rWrap = lamF . lamF $ iteF (appF fifthArgF firstArgF)
                                 (appF (appF fourthArgF secondArgF) firstArgF)
                                 (appF thirdArgF firstArgF)
      churchNum = clamF (lamF (SetEnvFrag <$> (PairFrag <$> deferF (pure unwrapFrame) <*> frameSetup)))
      -- hack to make sure recursion test wrapper can be put in a definite place when sizing
      tWrap = pairF (deferF $ appF secondArgF firstArgF) (pairF t $ pure ZeroFrag)
      trb = pairF b (pairF r (pairF tWrap (pure ZeroFrag)))
  in SetEnvFrag <$> wrapU (pairF (deferF $ appF (appF churchNum rWrap) firstArgF) trb)

nextBreakToken :: Enum b => BreakState a b b
nextBreakToken = do
  (token, fi, fm) <- State.get
  State.put (succ token, fi, fm)
  pure token

buildFragMap :: BreakState' a b -> Map FragIndex (FragExpr a)
buildFragMap bs = let (bf, (_,_,m)) = State.runState bs (undefined, FragIndex 1, Map.empty)
                  in Map.insert (FragIndex 0) bf m

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

instance Plated DataType where
  plate f = \case
    ArrType i o  -> ArrType <$> f i <*> f o
    PairType a b -> PairType <$> f a <*> f b
    x            -> pure x

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

instance Plated PartialType where
  plate f = \case
    ArrTypeP i o  -> ArrTypeP <$> f i <*> f o
    PairTypeP a b -> PairTypeP <$> f a <*> f b
    x             -> pure x

newtype PrettyPartialType = PrettyPartialType PartialType

showInternalP :: PartialType -> String
showInternalP at@(ArrTypeP _ _) = concat ["(", show $ PrettyPartialType at, ")"]
showInternalP t                 = show . PrettyPartialType $ t

instance Show PrettyPartialType where
  show (PrettyPartialType dt) = case dt of
    ZeroTypeP -> "Z"
    AnyType -> "A"
    (ArrTypeP a b) -> concat [showInternalP a, " -> ", showInternalP b]
    (PairTypeP a b) ->
      concat ["(", show $ PrettyPartialType a, ",", show $ PrettyPartialType b, ")"]
    (TypeVariable (-1)) -> "badType"
    (TypeVariable x) -> 'v' : show x

mergePairType :: DataType -> DataType
mergePairType = transform f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x                            = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = transform f where
  f (PairTypeP ZeroTypeP ZeroTypeP) = ZeroTypeP
  f x                               = x

containsFunction :: PartialType -> Bool
containsFunction = \case
  ArrTypeP _ _ -> True
  PairTypeP a b -> containsFunction a || containsFunction b
  _ -> False

cleanType :: PartialType -> Bool
cleanType = \case
  ZeroTypeP -> True
  PairTypeP a b -> cleanType a && cleanType b
  _ -> False

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

i2gF :: Int -> BreakState' a b
i2gF 0 = pure ZeroFrag
i2gF n = PairFrag <$> i2gF (n - 1) <*> pure ZeroFrag

ints2gF :: [Int] -> BreakState' a b
ints2gF = foldr (\i g -> PairFrag <$> i2gF i <*> g) (pure ZeroFrag)

s2gF :: String -> BreakState' a b
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
toIndExpr (Gate l r) = GateA <$> toIndExpr l <*> toIndExpr r <*> nextI
toIndExpr (PLeft x)  = PLeftA <$> toIndExpr x <*> nextI
toIndExpr (PRight x) = PRightA <$> toIndExpr x <*> nextI
toIndExpr Trace      = TraceA <$> nextI

toIndExpr' :: IExpr -> IndExpr
toIndExpr' x = State.evalState (toIndExpr x) (EIndex 0)

instance TelomareLike (ExprT a) where
  fromTelomare = \case
    Zero     -> ZeroT
    Pair a b -> PairT (fromTelomare a) (fromTelomare b)
    Env      -> EnvT
    SetEnv x -> SetEnvT $ fromTelomare x
    Defer x  -> DeferT $ fromTelomare x
    Gate l r -> GateT (fromTelomare l) (fromTelomare r)
    PLeft x  -> LeftT $ fromTelomare x
    PRight x -> RightT $ fromTelomare x
    Trace    -> TraceT
  toTelomare = \case
    ZeroT     -> pure Zero
    PairT a b -> Pair <$> toTelomare a <*> toTelomare b
    EnvT      -> pure Env
    SetEnvT x -> SetEnv <$> toTelomare x
    DeferT x  -> Defer <$> toTelomare x
    AbortT    -> Nothing
    GateT l r -> Gate <$> toTelomare l <*> toTelomare r
    LeftT x   -> PLeft <$> toTelomare x
    RightT x  -> PRight <$> toTelomare x
    TraceT    -> pure Trace
    TagT x _  -> toTelomare x -- just elide tags

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
      Gate l r -> GateFrag <$> convert l <*> convert r
      PLeft x -> LeftFrag <$> convert x
      PRight x -> RightFrag <$> convert x
      Trace -> pure TraceFrag

fragmapToTelomare :: Map FragIndex (FragExpr a) -> Maybe IExpr
fragmapToTelomare fragMap = convert (rootFrag fragMap) where
    convert = \case
      ZeroFrag      -> pure Zero
      PairFrag a b  -> Pair <$> convert a <*> convert b
      EnvFrag       -> pure Env
      SetEnvFrag x  -> SetEnv <$> convert x
      DeferFrag ind -> Defer <$> (Map.lookup ind fragMap >>= convert)
      AbortFrag     -> Nothing
      GateFrag l r  -> Gate <$> convert l <*> convert r
      LeftFrag x    -> PLeft <$> convert x
      RightFrag x   -> PRight <$> convert x
      TraceFrag     -> pure Trace
      AuxFrag _     -> Nothing

instance TelomareLike Term3 where
  fromTelomare = Term3 . Map.map FragExprUR . telomareToFragmap
  toTelomare (Term3 fragMap) = fragmapToTelomare $ Map.map unFragExprUR fragMap

instance TelomareLike Term4 where
  fromTelomare = Term4 . telomareToFragmap
  toTelomare (Term4 fragMap) = fragmapToTelomare fragMap

-- general utility functions

insertAndGetKey :: (Ord e, Enum e) => a -> State (Map e a) e
insertAndGetKey v = do
  m <- State.get
  let nextKey = case Set.lookupMax $ Map.keysSet m of
        Nothing -> toEnum 0
        Just n  -> succ n
  State.put $ Map.insert nextKey v m
  pure nextKey

-- abort codes
-- t x = if x <= 1
-- fact1 r x = if x <= 1
--    then 1
--    else x * (r (x - 1))
-- fix fact1
-- (\f x -> f x) fact1 (\_ -> error!) 3 -- error!
-- (\f x -> f (f x)) fact1 (\_ -> error!) 3 -- error!
-- (\f x -> f (f (f x))) fact1 (\_ -> error!) 3 -- 3, happy!
-- setenv env -- church numeral 1
-- setenv (setenv env) -- church numeral 2


pattern AbortRecursion :: IExpr
pattern AbortRecursion = Pair Zero Zero
pattern AbortUser :: IExpr -> IExpr
pattern AbortUser m = Pair (Pair Zero Zero) m
pattern AbortAny :: IExpr
pattern AbortAny = Pair (Pair (Pair Zero Zero) Zero) Zero
pattern AbortUnsizeable :: IExpr -> IExpr
pattern AbortUnsizeable t = Pair (Pair (Pair (Pair Zero Zero) Zero) Zero) t
