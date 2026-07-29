{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

module Telomare where

import Control.Applicative (Applicative (liftA2), liftA, liftA3)
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Comonad.Trans.Cofree (CofreeF)
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..),
                                                          ComonadCofree)
import Control.DeepSeq (NFData (..))
import Control.Lens.Combinators (Plated (..), makePrisms, transform)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Bifunctor (Bifunctor (..))
import Data.Bool (bool)
import Data.Char (chr, ord)
import Data.Eq.Deriving (deriveEq1)
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Ord1, Show1 (..), Show2 (..),
                             eq1, showsUnary1)
import Data.Functor.Foldable (Base, Corecursive (embed),
                              Recursive (cata, project))
import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.GenValidity (GenValid)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord.Deriving (deriveOrd1)
import qualified Data.Set as Set
import Data.Validity (Validity)
import Data.Void (Void)
import Debug.Trace (trace, traceShow, traceShowId)
import GHC.Generics (Generic, Generic1, Generically1 (..))
import Text.Show.Deriving (deriveShow1)

{- top level TODO list
 - change AbortFrag form to something more convenient
 - extract abort logic from arbitrary expressions (like, make quick dynamic check the way we have static check)
 - make sure recur calls in unsized recursion combinator are structurally smaller ... although, we can fail sizing and report that to user
-}


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

-- note that this doesn't incorporate laziness necessary for things like sizing recursion
iteB_ :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w) => g -> g -> g -> g
iteB_ i t e = SetEnvB $ PairP (SetEnvB $ PairP GateB i) (PairP e t)

data BasicExprF f
  = ZeroSF
  | PairSF f f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 BasicExprF where
  liftEq test a b = case (a,b) of
    (ZeroSF, ZeroSF)         -> True
    (PairSF a b, PairSF c d) -> test a c && test b d
    _                        -> False

instance Show1 BasicExprF where
  liftShowsPrec showsPrec' showList prec = \case
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
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Show1 StuckF where
  liftShowsPrec showsPrec' showList prec = \case
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
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 AbortableF  where
  liftEq test a b = case (a,b) of
    (AbortF, AbortF)                  -> True
    (AbortedF a, AbortedF b) | a == b -> True
    _                                 -> False

instance Show1 AbortableF where
  liftShowsPrec showsPrec showList prec = \case
    AbortF     -> shows "AbortF"
    AbortedF x -> shows "(AbortedF " . shows x . shows ")"

data StuckExprF f
  = StuckExprB (BasicExprF f)
  | StuckExprS (StuckF f)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
instance BasicBase StuckExprF where
  embedB = StuckExprB
  extractB = \case
    StuckExprB x -> Just x
    _            -> Nothing
instance StuckBase StuckExprF where
  embedS = StuckExprS
  extractS = \case
    StuckExprS x -> Just x
    _            -> Nothing
instance Eq1 StuckExprF where
  liftEq test a b = case (a,b) of
    (StuckExprB x, StuckExprB y) -> liftEq test x y
    (StuckExprS x, StuckExprS y) -> liftEq test x y
    _                            -> False
instance Show1 StuckExprF where
  liftShowsPrec showsPrec showList prec = \case
    StuckExprB x -> liftShowsPrec showsPrec showList prec x
    StuckExprS x -> liftShowsPrec showsPrec showList prec x

type StuckExpr = Fix StuckExprF

data CompiledExprF f
  = CompiledExprB (BasicExprF f)
  | CompiledExprS (StuckF f)
  | CompiledExprA (AbortableF f)
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
instance BasicBase CompiledExprF where
  embedB = CompiledExprB
  extractB = \case
    CompiledExprB x -> Just x
    _              -> Nothing
instance StuckBase CompiledExprF where
  embedS = CompiledExprS
  extractS = \case
    CompiledExprS x -> Just x
    _ -> Nothing
instance AbortBase CompiledExprF where
  embedA = CompiledExprA
  extractA = \case
    CompiledExprA x -> Just x
    _ -> Nothing
instance Eq1 CompiledExprF where
  liftEq test a b = case (a,b) of
    (CompiledExprB x, CompiledExprB y) -> liftEq test x y
    (CompiledExprS x, CompiledExprS y) -> liftEq test x y
    (CompiledExprA x, CompiledExprA y) -> liftEq test x y
    _                                  -> False
instance Show1 CompiledExprF where
  liftShowsPrec showsPrec showList prec = \case
    CompiledExprB x -> liftShowsPrec showsPrec showList prec x
    CompiledExprS x -> liftShowsPrec showsPrec showList prec x
    CompiledExprA x -> liftShowsPrec showsPrec showList prec x

type CompiledExpr = Fix CompiledExprF

newtype UnsizedRecursionToken = UnsizedRecursionToken { unUnsizedRecursionToken :: Int } deriving (Eq, Ord, Show, Enum, NFData, Generic)

instance Validity UnsizedRecursionToken

data SourcePosition = SourcePosition
  { sourcePositionLine   :: Int
  , sourcePositionColumn :: Int
  , sourcePositionOffset :: Int
  }
  deriving (Eq, Show, Ord, Generic, NFData)

instance Validity SourcePosition
instance GenValid SourcePosition

data SourceSpan = SourceSpan
  { sourceSpanFile  :: Maybe FilePath
  , sourceSpanStart :: SourcePosition
  , sourceSpanEnd   :: SourcePosition
  }
  deriving (Eq, Show, Ord, Generic, NFData)

instance Validity SourceSpan
instance GenValid SourceSpan

data LocTag
  = SourceLoc SourceSpan
  | GeneratedLoc String (Maybe LocTag)
  | BuiltinLoc String
  | RuntimeLoc
  | DecompiledLoc
  | UnknownLoc
  deriving (Eq, Show, Ord, Generic, NFData)

instance Validity LocTag
instance GenValid LocTag

data Term3F f
  = Term3B (BasicExprF f)
  | Term3S (StuckF f)
  | Term3A (AbortableF f)
  | Term3Unsized UnsizedRecursionToken
  | Term3CheckingWrapper LocTag f f
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
instance BasicBase Term3F where
  embedB = Term3B
  extractB = \case
    Term3B x -> Just x
    _              -> Nothing
instance StuckBase Term3F where
  embedS = Term3S
  extractS = \case
    Term3S x -> Just x
    _ -> Nothing
instance AbortBase Term3F where
  embedA = Term3A
  extractA = \case
    Term3A x -> Just x
    _ -> Nothing
instance Show1 Term3F where
  liftShowsPrec showsPrec' showList prec = \case
    Term3B x -> liftShowsPrec showsPrec' showList prec x
    Term3S x -> liftShowsPrec showsPrec' showList prec x
    Term3A x -> liftShowsPrec showsPrec' showList prec x
    Term3Unsized urt -> shows $ "Term3Unsized" <> show urt
    Term3CheckingWrapper loc cf c -> shows "Term3CheckingWrapper(" . shows loc . shows ", " . showsPrec' 0 cf . shows ", " . showsPrec' 0 c . shows ")"

instance Show o => Show1 (PatternF o) where
  liftShowsPrec showsPrec' showList prec = \case
    PatternVarF s -> showString "PatternVar " . shows s
    PatternAnnotatedF p x -> showString "PatternAnnotated " . showsPrec' 0 p . showChar ' ' . shows x
    PatternIntF x -> showString "PatternInt " . shows x
    PatternStringF s -> showString "PatternString " . shows s
    PatternIgnoreF -> showString "PatternIgnore"
    PatternPairF a b -> showString "PatternPair " . showsPrec' 0 a . showChar ' ' . showsPrec' 0 b

instance (Show p) => Show1 (UnprocessedParsedTermF p) where
  liftShowsPrec showsPrecFunc showList d term = case term of

    UnprocessedParsedTermB x -> liftShowsPrec showsPrecFunc showList d x
    UnprocessedParsedTermH x -> liftShowsPrec showsPrecFunc showList d x
    UnprocessedParsedTermL x -> liftShowsPrec showsPrecFunc showList d x
    ImportQualifiedUPF s1 s2 -> showString "ImportQualifedUPF " . shows s1 . showString " " . shows s2
    ImportUPF s -> showString "ImportUPF " . shows s
    LetUPF bindings body ->
      let showBinding (str, x) = showChar '(' . shows (locatedNameText str) . showString ", "
                                 . showsPrecFunc 11 x . showChar ')'
          showBindings bs = showChar '[' . foldr1 (\a b -> a . showString ", " . b)
                           (fmap showBinding bs) . showChar ']'
      in showString "LetUPF " . showBindings bindings . showChar ' ' . showsPrecFunc 11 body
    ListUPF terms -> showString "ListUPF [" .
                     foldr1 (\a b -> a . showString ", " . b)
                           (fmap (showsPrecFunc 11) terms) .
                     showChar ']'
    IntUPF n -> showString "IntUPF " . shows n
    StringUPF s -> showString "StringUPF " . shows s
    UDTUPF ss x -> showString "UDTUPF " . shows ss . showChar ' ' . showsPrecFunc 11 x
    CaseUPF scrutinee patterns ->
      let showPattern (pat, x) = showChar '(' . shows pat . showString ", "
                                . showsPrecFunc 11 x . showChar ')'
          showPatterns ps = showChar '[' . foldr1 (\a b -> a . showString ", " . b)
                           (fmap showPattern patterns) . showChar ']'
      in showString "CaseUPF " . showsPrecFunc 11 scrutinee . showChar ' '
         . showPatterns patterns

-- |AST for patterns in `case` expressions
data PatternF t f
  = PatternVarF String
  | PatternAnnotatedF f t
  | PatternIntF Int
  | PatternStringF String
  | PatternIgnoreF
  | PatternPairF f f
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (PatternF t))

-- |Firstly parsed AST
data UnprocessedParsedTermF p f
  = UnprocessedParsedTermH (HighTermF f)
  | UnprocessedParsedTermL (LamTermF LocatedName String f)
  | UnprocessedParsedTermB (BasicExprF f)
  | LetUPF [(LocatedName, f)] f
  | ListUPF [f]
  | IntUPF Int
  | StringUPF String
  | UDTUPF [String] f
  | CaseUPF f [(p, f)]
  -- TODO: check if adding this doesn't create partial functions
  | ImportQualifiedUPF String String
  | ImportUPF String
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (UnprocessedParsedTermF p))
instance HighBase (UnprocessedParsedTermF p) where
  embedH = UnprocessedParsedTermH
  extractH = \case
    UnprocessedParsedTermH x -> Just x
    _                        -> Nothing
instance BasicBase (UnprocessedParsedTermF p) where
  embedB = UnprocessedParsedTermB
  extractB = \case
    UnprocessedParsedTermB x -> Just x
    _                        -> Nothing
instance LamBase (UnprocessedParsedTermF p) where
  type LamVar (UnprocessedParsedTermF p) = String
  type LamT (UnprocessedParsedTermF p) = LocatedName

  embedL = UnprocessedParsedTermL
  extractL = \case
    UnprocessedParsedTermL x -> Just x
    _                        -> Nothing

type Pattern = Fix (PatternF UnprocessedParsedTerm)
newtype UnprocessedParsedTerm = UnprocessedParsedTerm { unUnprocessedParsedTerm :: UPT}
type UPT = Fix (UnprocessedParsedTermF Pattern)

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
  liftShowsPrec showsPrecFunc showList d = \case
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
  liftShowsPrec showsPrecFunc showList d = \case
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

newtype AnnotatedUPT = AnnotatedUPT { unAnnotatedUPT :: AUPT }
  deriving (Eq, Show)
type AUPT = Cofree (UnprocessedParsedTermF PatternA) LocTag
type PatternA = Fix (PatternF AnnotatedUPT)


-- | Parser AST
data ParserTermF l v f
  = ParserTermB (BasicExprF f)
  | ParserTermH (HighTermF f)
  | ParserTermL (LamTermF l v f)
  | TUnsizedRepeaterF
  deriving (Functor, Foldable, Traversable)
deriving instance (Show l, Show v, Show a) => Show (ParserTermF l v a)
instance (Show l, Show v) => Show1 (ParserTermF l v) where
  liftShowsPrec showsPrecFunc showList d = \case
    ParserTermB x -> liftShowsPrec showsPrecFunc showList d x
    ParserTermH x -> liftShowsPrec showsPrecFunc showList d x
    ParserTermL x -> liftShowsPrec showsPrecFunc showList d x
    TUnsizedRepeaterF -> showString "TUnsizedRepeaterF"
instance BasicBase (ParserTermF l v) where
  embedB = ParserTermB
  extractB = \case
    ParserTermB x -> Just x
    _              -> Nothing
instance HighBase (ParserTermF l v) where
  embedH = ParserTermH
  extractH = \case
    ParserTermH x -> Just x
    _             -> Nothing
instance LamBase (ParserTermF l v) where
  type LamVar (ParserTermF l v) = v
  type LamT (ParserTermF l v) = l

  embedL = ParserTermL
  extractL = \case
    ParserTermL x -> Just x
    _             -> Nothing

deriving instance (Eq l, Eq v, Eq a) => Eq (ParserTermF l v a)
instance (Eq l, Eq v) => Eq1 (ParserTermF l v) where
  liftEq eq (ParserTermB x) (ParserTermB y)    = liftEq eq x y
  liftEq eq (ParserTermH x) (ParserTermH y)    = liftEq eq x y
  liftEq eq (ParserTermL x) (ParserTermL y)    = liftEq eq x y
  liftEq _ TUnsizedRepeaterF TUnsizedRepeaterF = True
  liftEq _ _ _                                 = False


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
  let sout = str <> " "
  State.put $ i + length sout
  x <- sx
  pure $ sout <> x

indentWithTwoChildren' :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren' str sl sr = do
  i <- State.get
  let sout = str <> " "
      newl = i + length sout
  State.put newl
  l <- sl
  State.put newl
  r <- sr
  pure $ sout <> l <> "\n" <> indent newl r

indentWithChildren' :: String -> [State Int String] -> State Int String
indentWithChildren' str l = do
  i <- State.get
  let sout = str <> " "
      newl = i + length sout
  let doLine = fmap (<> "\n" <> indent newl "") . (State.put newl >>)
  foldl (\s c -> (<>) <$> s <*> c) (pure sout) $ fmap doLine l

-- TODO replace with above version
-- |Two children indentation.
indentWithTwoChildren :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren str sl sr = do
  i <- State.get
  State.put $ i + 2
  l <- sl
  State.put $ i + 2
  r <- sr
  pure $ indent i (str <> "\n") <> l <> "\n" <> r

-- TODO replace with other version
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
  if p x1 then x else dropUntil p (drop 1 x)

locStartLineColumn :: LocTag -> Maybe (Int, Int)
locStartLineColumn = \case
  SourceLoc span ->
    let start = sourceSpanStart span
    in Just (sourcePositionLine start, sourcePositionColumn start)
  GeneratedLoc _ parent -> parent >>= locStartLineColumn
  _ -> Nothing

renderLocTag :: LocTag -> Maybe String
renderLocTag loc = case locStartLineColumn loc of
  Just (line, column) -> Just $ "line " <> show line <> ", column " <> show column
  Nothing             -> Nothing

renderLocTagVerbose :: LocTag -> String
renderLocTagVerbose loc = case (loc, renderLocTag loc) of
  (GeneratedLoc reason _, Just rendered) -> rendered <> " (generated by " <> reason <> ")"
  (GeneratedLoc reason Nothing, _)       -> "generated by " <> reason
  (BuiltinLoc name, _)                   -> "builtin " <> show name
  (RuntimeLoc, _)                        -> "runtime value"
  (DecompiledLoc, _)                     -> "decompiled value"
  (UnknownLoc, _)                        -> "unknown location"
  (_, Just rendered)                     -> rendered
  (_, Nothing)                           -> "unknown location"

type Term1 = Cofree (ParserTermF (LamType String) String) LocTag
type Term2 = Cofree (ParserTermF (LamType ()) Int) LocTag
type Term3 = Cofree Term3F LocTag

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

data ResolverError
  = NoMainFunction String
  | ModuleNotFound String
  | DefinitionCycle [String]
  | MissingDefinitions [String]
  | MissingDefinitionAt LocTag String
  | ParseError String
  deriving (Eq, Ord)

instance Show ResolverError where
  showsPrec d err = showParen (d > 10) $ showString (renderResolverError err)

renderResolverError :: ResolverError -> String
renderResolverError = \case
  NoMainFunction moduleName -> "NoMainFunction " <> show moduleName
  ModuleNotFound moduleName -> "ModuleNotFound " <> show moduleName
  DefinitionCycle names -> "DefinitionCycle " <> show names
  MissingDefinitions names -> "MissingDefinitions " <> show names
  MissingDefinitionAt loc name ->
    "missing definition " <> show name <> " at " <> renderLocTagVerbose loc
  ParseError err -> "ParseError " <> show err

data EvalError = RTE RunTimeError
    | TCE TypeCheckError
    | RE ResolverError
    | StaticCheckError String
    | CompileConversionError
    | RecursionLimitError UnsizedRecursionToken
    deriving (Eq, Show)

data RunTimeError
  = AbortRunTime BasicExpr
  | GenericRunTimeError String CompiledExpr
  | ResultConversionError String
  deriving (Eq)

instance Show RunTimeError where
  show (AbortRunTime a) = "Aborted, " <> convertAbortMessage a
  show (GenericRunTimeError s i) = "Generic Runtime Error: " <> s <> " -- " <> show i
  show (ResultConversionError s) = "Couldn't convert runtime result to IExpr: " <> s

-- type RunResult = ExceptT RunTimeError IO

class TelomareLike a where
  fromTelomare :: StuckExpr -> a
  toTelomare :: a -> Maybe StuckExpr

class TelomareLike a => AbstractRunTime a where
  eval :: a -> Either RunTimeError a

instance TelomareLike StuckExpr where
  fromTelomare = id
  toTelomare = pure

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

type Term3Builder g = State (FunctionIndex, UnsizedRecursionToken) g

buildTerm :: (Corecursive g) => Term3Builder g -> g
buildTerm = flip State.evalState (toEnum 0, toEnum 0)

deferS :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => g -> Term3Builder g
deferS x = do
  fi <- State.gets fst
  State.modify (\(_, urt) -> (succ fi, urt))
  pure . StuckEE $ DeferSF fi x

-- TODO: replace with PairP?
pairS :: (Base g ~ CofreeT.CofreeF f a, BasicBase f, Recursive g, Corecursive g, Monad m) => m g -> m g -> m g
pairS a b = do
  a' <- a
  b' <- b
  let l CofreeT.:< _ = project a'
  pure . embed $ l CofreeT.:< embedB (PairSF a' b')

clamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
clamS x = pairS (x >>= deferS) $ pure ZeroB

lamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
lamS x = pairS (x >>= deferS) $ pure EnvB

twiddleS :: forall g f w. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w)
  => Term3Builder g
twiddleS = deferS . PairP (LeftB $ RightB EnvB) . PairP (LeftB EnvB) $ RightB (RightB EnvB)

appS :: forall g f w. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w)
  => Term3Builder g -> Term3Builder g -> Term3Builder g
appS c i = SetEnvB . SetEnvB <$> pairS twiddleS (pairS i c)

-- inside three lambdas (\r f x -> ...)
-- r is the repeater function
-- creates and iterates on a function "frame" (rf, (rf, (f', (x, env'))))
-- rf is the function to pull arguments out of the frame, run f', and construct the next frame
-- (f',env') is f (since f may contain a saved environment/closure env we want to use for each iteration)
repeatFunctionS :: LocTag -> Term3Builder Term3
repeatFunctionS l =
  let applyF = SetEnvB $ RightB EnvB
      env' = RightB . RightB $ RightB EnvB
      -- takes (rf, (f', (x, env'))), executes f' with (x, env') and creates a new frame
      rf = deferS $ PairP (LeftB EnvB)
                          (PairP (LeftB EnvB)
                                 (PairP (LeftB (RightB EnvB))
                                        (PairP applyF env')))
      r = LeftB . LeftB . RightB $ RightB EnvB
      x = LeftB EnvB
      f' = LeftB . LeftB $ RightB EnvB
      fenv = RightB . LeftB $ RightB EnvB
      -- (r, (x, ((f', fenv), 0))) -> (rf, (rf, (f', (x, fenv))))
      frameSetup = pairS rf (pairS rf (pure $ PairP f' (PairP x fenv)))
  in clamS . lamS . lamS $ SetEnvB <$> pairS (pure r) frameSetup

unsizedRepeater :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
unsizedRepeater l tok = clamS . pure . LeftB . RightB . RightB . RightB . embed $ l CofreeT.:< Term3Unsized tok

repeaterAndAbort :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
repeaterAndAbort l tok = pairS (unsizedRepeater l tok) abrt where
  -- args are (i, (b, ...)) since trb is on the stack
  -- abrt = (>>= deferS) $ SetEnvB . PairP (SetEnvB $ PairP AbortB abortToken) <$> appS (pure secondArgB) (pure firstArgB)
  abrt = (>>= deferS) $ SetEnvB . PairP (SetEnvB $ PairP AbortB abortToken) <$> appS (pure $ varB 1) (pure $ varB 0)
  abortToken = PairP ZeroB . i2B $ fromEnum tok

-- to construct a church numeral (\f x -> f ... (f x))
-- the core is nested setenvs around an env, where the number of setenvs is magnitude of church numeral
i2CB :: LocTag -> Int -> Term3Builder Term3
i2CB l n = appS (repeatFunctionS l) . clamS . pure . LeftB . RightB . RightB . RightB $ iterate SetEnvB EnvB !! n

-- function is called with (r,a), where r is the repeating function, and a is the abort function
unsizedRecursionWrapper :: LocTag -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3
unsizedRecursionWrapper loc t r b =
  let repeater = LeftB $ LeftB EnvB
      abrt = PairP (RightB $ LeftB EnvB) EnvB
      -- drop first arg (repeater)
      nsLamS :: Term3Builder Term3 -> Term3Builder Term3
      nsLamS x = pairS (x >>= deferS) (pure $ RightB EnvB)
      -- \t r b r' i -> if t i then r r' i else b i -- t r b are already on the stack when this is evaluated
      rWrap = nsLamS . lamS $ iteB_ <$> appS (pure $ varB 4) (pure $ varB 0)
                                    <*> appS (appS (pure $ varB 3) (pure $ varB 1)) (pure $ varB 0)
                                    <*> appS (pure $ varB 2) (pure $ varB 0)
      -- hack to make sure recursion test wrapper can be put in a definite place when sizing
      tWrap = pairS ((>>= deferS) (appS (pure $ varB 1) (pure $ varB 0))) (pairS t $ pure ZeroB)
      trb = pairS b . pairS r . pairS tWrap $ pure ZeroB
  in pairS (appS (appS (appS (repeatFunctionS loc) (pure repeater)) rWrap) (pure abrt) >>= deferS) trb

data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord, Generic)

instance Validity DataType
instance GenValid DataType

instance Plated DataType where
  plate f = \case
    ArrType i o  -> ArrType <$> f i <*> f o
    PairType a b -> PairType <$> f a <*> f b
    x            -> pure x

data PartialTypeF f
  = ZeroTypeP
  | AnyType
  | TypeVariable LocTag Int
  | ArrTypeP f f
  | PairTypeP f f
  deriving (Eq, Ord, Show, Generic1, Functor, Foldable, Traversable)
  deriving Eq1 via (Generically1 PartialTypeF)
  deriving Ord1 via (Generically1 PartialTypeF)
instance Show1 PartialTypeF where
  liftShowsPrec showsPrecFunc showList d = \case
    ZeroTypeP -> showString "ZeroTypeP"
    AnyType -> showString "AnyType"
    TypeVariable l i -> showString "TypeVariable " . shows l . showString " " . shows i
    ArrTypeP i o -> showString "ArrTypeP (" . showsPrecFunc 0 i . showString " -> " . showsPrecFunc 0 o . showString ")"
    PairTypeP a b -> showString "PairTypeP (" . showsPrecFunc 0 b . showString ", " . showsPrecFunc 0 b . showString ")"

type PartialType = Fix PartialTypeF

toPartialType :: DataType -> PartialType
toPartialType = \case
  ZeroType -> embed ZeroTypeP
  ArrType i o -> embed $ ArrTypeP (toPartialType i) (toPartialType o)
  PairType a b -> embed $ PairTypeP (toPartialType a) (toPartialType b)

mergePairType :: DataType -> DataType
mergePairType = transform f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x                            = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = cata f where
  f = \case
    (PairTypeP (Fix ZeroTypeP) (Fix ZeroTypeP)) -> embed ZeroTypeP
    x -> embed x

containsFunction :: PartialType -> Bool
containsFunction = cata f where
  f = \case
    ArrTypeP _ _ -> True
    x -> or x

cleanType :: PartialType -> Bool
cleanType = cata f where
  f = \case
    ZeroTypeP -> True
    PairTypeP a b -> a && b
    _ -> False

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

instance TelomareLike Term3 where
  fromTelomare = verify . cata (convertBasic (convertStuck (\z -> Left "failed converting to Term3"))) where
    verify = \case
      Right x -> x
      Left e -> error e
  toTelomare = cata f . forget' where
    forget' :: Term3 -> Fix Term3F
    forget' = forget
    f = \case
      Term3Unsized _ -> Nothing
      Term3CheckingWrapper _ _ _ -> Nothing
      Term3A _ -> Nothing
      Term3B b -> embed . StuckExprB <$> sequence b
      Term3S s -> embed . StuckExprS <$> sequence s

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

newtype LocatedName = LocatedName (LocTag, String)
  deriving (Eq, Ord, Show)

locatedNameLoc :: LocatedName -> LocTag
locatedNameLoc (LocatedName (loc, _)) = loc

locatedNameText :: LocatedName -> String
locatedNameText (LocatedName (_, name)) = name

locatedName :: LocTag -> String -> LocatedName
locatedName loc name = LocatedName (loc, name)

letBindingName :: (LocatedName, a) -> String
letBindingName (name, _) = locatedNameText name

letBindingValue :: (LocatedName, a) -> a
letBindingValue (_, value) = value

letBindingLoc :: (LocatedName, a) -> LocTag
letBindingLoc (name, _) = locatedNameLoc name

class CarryAnno g where
  type CarryWrap g :: * -> *

  getEmbed :: g -> (CarryWrap g) g -> g

instance CarryAnno (Fix (UnprocessedParsedTermF PatternA)) where
  type CarryWrap (Fix (UnprocessedParsedTermF PatternA)) = UnprocessedParsedTermF PatternA

  getEmbed _ = Fix
instance CarryAnno AUPT where
  type CarryWrap AUPT = UnprocessedParsedTermF PatternA

  getEmbed (a :< _) = (a :<)

instance CarryAnno UPT where
  type CarryWrap UPT = UnprocessedParsedTermF Pattern

  getEmbed _ = Fix
instance CarryAnno BasicExpr where
  type CarryWrap BasicExpr = BasicExprF

  getEmbed _ = Fix
instance CarryAnno StuckExpr where
  type CarryWrap StuckExpr = StuckExprF

  getEmbed _ = Fix
instance CarryAnno (Cofree (ParserTermF (LamType l) v) LocTag) where
  type CarryWrap (Cofree (ParserTermF (LamType l) v) LocTag) = ParserTermF (LamType l) v

  getEmbed (a :< _) = (a :<)

instance CarryAnno Term3 where
  type CarryWrap Term3 = Term3F

  getEmbed (a :< _) = (a :<)
instance CarryAnno (Cofree CompiledExprF LocTag) where
  type CarryWrap (Cofree CompiledExprF LocTag) = CompiledExprF

  getEmbed (a :< _) = (a :<)

pattern GFix :: (Recursive g, Corecursive g, Base g ~ f) => f g -> g
pattern GFix x <- (project -> x) where
  GFix x = embed x
pattern VarFP :: (LamBase f, LamVar f ~ n) => n -> f x
pattern VarFP n <- (extractL -> Just (VarF n)) where
  VarFP n = embedL $ VarF n
pattern VarAFP :: (LamBase f, LamVar f ~ n) => a -> n -> CofreeF f a x
pattern VarAFP a n <- (a CofreeT.:< (extractL -> Just (VarF n))) where
  VarAFP a n = a CofreeT.:< embedL (VarF n)
pattern VarP :: (Recursive g, Corecursive g, Base g ~ f, LamBase f, LamVar f ~ n) => n -> g
pattern VarP n = GFix (VarFP n)
pattern AppAFP :: (LamBase f) => a -> b -> b -> CofreeF f a b
pattern AppAFP a f i <- (a CofreeT.:< (extractL -> Just (AppF f i))) where
  AppAFP a f i = a CofreeT.:< embedL (AppF f i)
pattern AppP :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, LamBase w, LamBase f) => g -> g -> g
pattern AppP f i <- (project -> (extractL -> Just (AppF f i))) where
  AppP f i = getEmbed f (embedL (AppF f i))
pattern LamAFP :: (LamBase f, LamT f ~ n) => a -> n -> b -> CofreeF f a b
pattern LamAFP a n x <- (a CofreeT.:< (extractL -> Just (LamF n x))) where
  LamAFP a n x = (a CofreeT.:<) . embedL $ LamF n x
pattern LamP :: (Recursive g, CarryAnno g, Base g ~ f, LamBase f, CarryWrap g ~ w, LamBase w, LamT w ~ n, LamT f ~ n) => n -> g -> g
pattern LamP n x <- (project -> (extractL -> Just (LamF n x))) where
  LamP n x = getEmbed x (embedL (LamF n x))
pattern ITEAFP :: (HighBase f) => LocTag -> b -> b -> b -> CofreeF f LocTag b
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
pattern PairAFP :: (BasicBase f) => LocTag -> x -> x -> CofreeF f LocTag x
pattern PairAFP a x y <- (a CofreeT.:< (extractB -> Just (PairSF x y))) where
  PairAFP a x y = a CofreeT.:< embedB (PairSF x y)
pattern PairP :: (Recursive g, CarryAnno g, Base g ~ f, CarryWrap g ~ w, BasicBase f, BasicBase w) => g -> g -> g
pattern PairP a b <- (project -> (extractB -> Just (PairSF a b))) where
  PairP a b = getEmbed a (embedB (PairSF a b))
