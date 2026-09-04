{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}

-- |The lowered IRs. In pipeline order: 'Term1' (named lambdas, produced by
-- resolution), 'Term2' (de Bruijn indices), 'Term3' (core with unsized
-- recursion stubs, consumed by the type checker and the sizing pass),
-- 'CompiledExpr' (sized, executable core) and 'StuckExpr' (abort-free
-- executable core). 'TelomareLike'/'AbstractRunTime' connect any of these
-- to the reference evaluator.
module Telomare.IR.Core where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (..))
import Data.Functor.Foldable (Recursive (cata))
import GHC.Generics (Generic)
import Telomare.IR.Base (AbortBase (..), AbortableF (..), BasicBase (..),
                         BasicExpr, BasicExprF (..), CarryAnno (..),
                         HighBase (..), HighTermF (..), LamBase (..),
                         LamTermF (..), LamType (..), StuckBase (..),
                         StuckF (..), UnsizedRecursionToken,
                         convertAbortMessage, convertBasic, convertStuck,
                         forget)
import Telomare.IR.Loc (LocTag (GeneratedLoc))

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
  liftShowsPrec showsPrec' showList' prec = \case
    StuckExprB x -> liftShowsPrec showsPrec' showList' prec x
    StuckExprS x -> liftShowsPrec showsPrec' showList' prec x

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
  liftShowsPrec showsPrec' showList' prec = \case
    CompiledExprB x -> liftShowsPrec showsPrec' showList' prec x
    CompiledExprS x -> liftShowsPrec showsPrec' showList' prec x
    CompiledExprA x -> liftShowsPrec showsPrec' showList' prec x

type CompiledExpr = Fix CompiledExprF

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
  liftShowsPrec showsPrec' showList' prec = \case
    Term3B x -> liftShowsPrec showsPrec' showList' prec x
    Term3S x -> liftShowsPrec showsPrec' showList' prec x
    Term3A x -> liftShowsPrec showsPrec' showList' prec x
    Term3Unsized urt -> shows $ "Term3Unsized" <> show urt
    Term3CheckingWrapper loc cf c -> shows "Term3CheckingWrapper(" . shows loc . shows ", " . showsPrec' 0 cf . shows ", " . showsPrec' 0 c . shows ")"

-- | Parser AST
data ParserTermF l v f
  = ParserTermB (BasicExprF f)
  | ParserTermH (HighTermF f)
  | ParserTermL (LamTermF l v f)
  | TUnsizedRepeaterF
  deriving (Functor, Foldable, Traversable)
deriving instance (Show l, Show v, Show a) => Show (ParserTermF l v a)
instance (Show l, Show v) => Show1 (ParserTermF l v) where
  liftShowsPrec showsPrecFunc showListFunc d = \case
    ParserTermB x -> liftShowsPrec showsPrecFunc showListFunc d x
    ParserTermH x -> liftShowsPrec showsPrecFunc showListFunc d x
    ParserTermL x -> liftShowsPrec showsPrecFunc showListFunc d x
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

type Term1 = Cofree (ParserTermF (LamType String) String) LocTag
type Term2 = Cofree (ParserTermF (LamType ()) Int) LocTag
type Term3 = Cofree Term3F LocTag

-- | Inject a sized, runnable term back into Term3 ('CompiledExprF' is a
-- strict subset of 'Term3F'), so Term3-based analyses — EAL tagging in
-- particular — can run on the post-sizing form. Source locations are gone
-- by this point, so every node carries a generated tag.
compiled2Term3 :: CompiledExpr -> Term3
compiled2Term3 = cata f where
  anno = GeneratedLoc "compiled2Term3" Nothing
  f = \case
    CompiledExprB x -> anno :< Term3B x
    CompiledExprS x -> anno :< Term3S x
    CompiledExprA x -> anno :< Term3A x

data RunTimeError
  = AbortRunTime BasicExpr
  | GenericRunTimeError String CompiledExpr
  | ResultConversionError String
  deriving (Eq)

instance Show RunTimeError where
  show (AbortRunTime a) = "Aborted, " <> convertAbortMessage a
  show (GenericRunTimeError s i) = "Generic Runtime Error: " <> s <> " -- " <> show i
  show (ResultConversionError s) = "Couldn't convert runtime result to IExpr: " <> s

class TelomareLike a where
  fromTelomare :: StuckExpr -> a
  toTelomare :: a -> Maybe StuckExpr

class TelomareLike a => AbstractRunTime a where
  eval :: a -> Either RunTimeError a

instance TelomareLike StuckExpr where
  fromTelomare = id
  toTelomare = pure

instance TelomareLike Term3 where
  fromTelomare = verify . cata (convertBasic (convertStuck (\_z -> Left "failed converting to Term3"))) where
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
      Term3B b -> embed' . StuckExprB <$> sequence b
      Term3S s -> embed' . StuckExprS <$> sequence s
    embed' = Fix

instance TelomareLike CompiledExpr where
  fromTelomare = verify . cata (convertBasic (convertStuck (\_z -> Left "failed to convert to CompiledExpr"))) where
    verify = \case
      Left e  -> error e
      Right x -> x
  toTelomare = cata (convertBasic (convertStuck (const Nothing)))

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
