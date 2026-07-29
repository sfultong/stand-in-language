{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}

module PrettyPrint where

import Control.Monad.State (State)
import Data.Map (Map)
import Telomare (AbortableF (..), BasicExprF (..), CompiledExpr,
                 CompiledExprF (..), DataType (..), FunctionIndex,
                 HighTermF (..), LamTermF (..), LamType (..), LocTag,
                 ParserTermF (..), PartialType, PartialTypeF (..),
                 PatternF (..), StuckExpr, StuckExprF (..), StuckF (..), Term1,
                 Term3 (..), Term3F (..), UnprocessedParsedTerm (..),
                 UnprocessedParsedTermF (..), b2i, convertAbortMessage, forget,
                 indentWithChildren', indentWithOneChild',
                 indentWithTwoChildren', locatedNameText, pattern BasicEE)

import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import qualified Control.Monad.State as State
import qualified Data.Map as Map

import Control.Comonad.Cofree
import Data.Fix (Fix (..))
import Data.Functor.Foldable
import Data.List (elemIndex)
import Text.Read (readMaybe)
-- import Data.SBV (sFPHalf)


class PrettyPrintable p where
  showP :: p -> State Int String

class PrettyPrintable1 p where
  showP1 :: PrettyPrintable a => p a -> State Int String

instance (PrettyPrintable1 f, PrettyPrintable x) => PrettyPrintable (f x) where
  showP = showP1

prettyPrint :: PrettyPrintable p => p -> String
prettyPrint x = State.evalState (showP x) 0

indentation :: Int -> String
indentation 0 = []
indentation n = ' ' : ' ' : indentation (n - 1)

instance (Show l, Show v) => PrettyPrintable1 (LamTermF l v) where
  showP1 = \case
      VarF v                  -> pure $ show v
      AppF c i                -> indentWithTwoChildren' "($)" (showP c) (showP i)
      LamF l x -> indentWithOneChild' ("\\" <> show l) $ showP x

instance PrettyPrintable1 HighTermF where
  showP1 = \case
      CheckF cf i             -> indentWithTwoChildren' ":" (showP cf)  (showP i)
      ITEF i t e              -> indentWithChildren' "ITE" $ showP <$> [i,t,e]
      HLeftF x                 -> indentWithOneChild' "L" $ showP x
      HRightF x                -> indentWithOneChild' "R" $ showP x
      HTraceF x                -> indentWithOneChild' "T" $ showP x
      HashF x                 -> indentWithOneChild' "#" $ showP x
      ChurchF n               -> pure $ "$" <> show n
  {-
      TLamF (Open v) x         -> indentWithOneChild' ("\\" <> show v) $ showP x
      TLamF (Closed v) x       -> indentWithOneChild' ("[\\" <> show v) $ showP x
      TLamF (LetBinding c v) x -> indentWithOneChild' ("{\\(" <> show c <> ") " <> show v) $ showP x
-}
      RecursionF t r b -> indentWithChildren' "TRB" $ showP <$> [t,r,b]

instance (Show l, Show v) => PrettyPrintable1 (ParserTermF l v) where
  showP1 = \case
      ParserTermB x            -> showP1 x
      TUnsizedRepeaterF        -> pure "*"

indentSansFirstLine :: Int -> String -> String
indentSansFirstLine i x = removeLastNewLine res where
  res = unlines $ (\(s:ns) -> s:((indentation i <>) <$> ns)) (lines x)
  removeLastNewLine str =
    case reverse str of
      '\n' : rest -> reverse rest
      x           -> str

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

newtype PrettyPartialType = PrettyPartialType PartialType

showInternalP :: PartialType -> String
showInternalP at@(Fix (ArrTypeP _ _)) = concat ["(", show $ PrettyPartialType at, ")"]
showInternalP t                 = show . PrettyPartialType $ t

instance Show PrettyPartialType where
  show (PrettyPartialType dt) = case project dt of
    ZeroTypeP -> "Z"
    AnyType -> "A"
    (ArrTypeP a b) -> concat [showInternalP a, " -> ", showInternalP b]
    (PairTypeP a b) ->
      concat ["(", show $ PrettyPartialType a, ",", show $ PrettyPartialType b, ")"]
    (TypeVariable _ (-1)) -> "badType"
    (TypeVariable _ x) -> 'v' : show x

prettyPrintPattern :: (s -> String) -> Fix (PatternF s) -> String
prettyPrintPattern pp = go . project where
  go = \case
    (PatternIntF x) -> show x
    (PatternVarF x) -> x
    (PatternStringF x) ->  show x
    (PatternPairF x y) -> "(" <> prettyPrintPattern pp x <> ", " <> prettyPrintPattern pp y <> ")"
    PatternIgnoreF -> "_"
    PatternAnnotatedF x upt -> "{anno " <> prettyPrintPattern pp x <> " }" <> pp upt

instance PrettyPrintable1 PartialTypeF where
  showP1 = \case
      ZeroTypeP -> pure "Z"
      AnyType -> pure "A"
      TypeVariable _ n -> pure $ "V" <> show (fromEnum n)
  {-
      ArrTypeP a b -> case project a of
        -- ArrTypeP _ _ -> "(" <> showP a <> ") -> " <> showP b
        ArrTypeP _ _ -> (\a' b' -> "(" <> a' <> ") -> " <> b') <$> showP a <*> showP b
        _            -> f a <> " -> " <> f b
-}
      ArrTypeP a b -> (\a' b' -> "(" <> a' <> ") -> " <> b') <$> showP a <*> showP b
      PairTypeP a b -> (\a' b' -> "(" <> a' <> "," <> b' <> ")") <$> showP a <*> showP b

newtype MultiLineShowUPT = MultiLineShowUPT UnprocessedParsedTerm
instance Show MultiLineShowUPT where
  show (MultiLineShowUPT (UnprocessedParsedTerm upt)) = cata alg upt where
    ind = indentSansFirstLine 2
    -- alg :: Base UnprocessedParsedTerm String -> String
    alg = \case
      UnprocessedParsedTermB x -> case x of
        PairSF x y -> "PairUP\n" <>
                          "  " <> ind x <> "\n" <>
                          "  " <> ind y
      UnprocessedParsedTermH x -> case x of
        (ITEF x y z) -> "ITEUP\n" <>
                          "  " <> ind x <> "\n" <>
                          "  " <> ind y <> "\n" <>
                          "  " <> ind z
        (ChurchF x) -> "ChurchUP " <> show x
        (HLeftF x) -> "LeftUP\n" <>
                        "  " <> ind x
        (HRightF x) -> "RightUP\n" <>
                          "  " <> ind x
        (HTraceF x) -> "TraceUP\n" <>
                          "  " <> ind x
        (RecursionF x y z) -> "UnsizedRecursionUP\n" <>
                          "  " <> ind x <> "\n" <>
                          "  " <> ind y <> "\n" <>
                          "  " <> ind z
        (HashF x) -> "HashUP\n" <>
                        "  " <> ind x
        (CheckF x y) -> "CheckUP\n" <>
                          "  " <> ind x <> "\n" <>
                          "  " <> ind y
      UnprocessedParsedTermL x -> case x of
        VarF str -> "VarUP " <> str
        (AppF x y) -> "AppUP\n" <>
                          "  " <> ind x <> "\n" <>
                          "  " <> ind y
        (LamF str y) -> "LamUP " <> locatedNameText str <> "\n" <>
                          "  " <> ind y
      IntUPF i -> "IntUP " <> show i
      StringUPF str -> "StringUP " <> show str
      (ListUPF []) -> "ListUP []"
      (ListUPF [x]) -> "ListUP [" <> x <> "]"
      (ListUPF ls) -> "ListUP\n" <>
                        concatMap (\x -> "  , " <> ind x <> "\n") ls <>
                        "  ]"
      (LetUPF ls x) -> "LetUP\n" <>
                         concatMap (\(n,v) -> "  , (" <> locatedNameText n <> ", " <> ind v <> ")\n") ls <>
                         "  ]\n" <>
                         "  " <> ind x
      (CaseUPF x ls) -> "CaseUP\n" <>
                          "  " <> ind x <> "\n" <>
                          concatMap (\(p,v) -> "  , (" <> prettyPrintPattern (show . MultiLineShowUPT) p <> ",\n    " <> ind v <> ")\n") ls <>
                          "  ]"
      (UDTUPF ss x) -> "UDTUP " <> show ss <> "\n" <>
                        "  " <> ind x
      (ImportUPF s) -> "ImportUP " <> show s
      (ImportQualifiedUPF s1 s2) -> "ImportQualifiedUP " <> show s1 <> " " <> show s2

newtype PrettyUPT = PrettyUPT UnprocessedParsedTerm

instance Show PrettyUPT where
  show (PrettyUPT (UnprocessedParsedTerm upt)) = cata alg upt where
    -- alg :: Base UnprocessedParsedTerm String -> String
    alg = \case
      UnprocessedParsedTermB x -> case x of
        PairSF x y -> if length (lines (x <> y)) > 1
                        then "( " <> indentSansFirstLine 2 x <> "\n" <>
                              ", " <> indentSansFirstLine 2 y <> "\n" <>
                              ")"
                        else "(" <> x <> ", " <> y <>")"
      UnprocessedParsedTermL x -> case x of
        VarF str -> str
        (AppF x y) -> (if (length . words $ x) == 1 then x else "(" <> x <> ")") <> " " <>
                        if (length . words $ y) == 1 then y else "(" <> y <> ")"
        (LamF str y) -> "\\ " <> locatedNameText str <> " -> " <> indentSansFirstLine (6 + length (locatedNameText str)) y
      UnprocessedParsedTermH x -> case x of
        (ITEF x y z) -> "if " <> indentSansFirstLine 3 x <> "\n" <>
                            "  then " <> indentSansFirstLine 7 y <> "\n" <>
                            "  else " <> indentSansFirstLine 7 z
        (ChurchF x) -> "$" <> show x
        (HLeftF x) -> "left (" <> indentSansFirstLine 6 x <> ")"
        (HRightF x) -> "right (" <> indentSansFirstLine 7 x <> ")"
        (HTraceF x) -> "trace (" <> indentSansFirstLine 7 x <> ")"
        (RecursionF x y z) -> "{ " <> indentSansFirstLine 2 x <>
                                      ", " <> indentSansFirstLine 2 y <>
                                      ", " <> indentSansFirstLine 2 z <>
                                      "}"
        (HashF x) -> "# " <> indentSansFirstLine 2 x
        (CheckF x y) -> if length (lines (x <> y)) > 1
                            then "(" <> indentSansFirstLine 2 y <> " : " <> "\n" <>
                                "    " <> indentSansFirstLine 4 y <> ")"
                            else "(" <> y <> " : " <> x <> ")"
      IntUPF i -> show i
      StringUPF str -> show str
      (LetUPF ls x) ->
        "let " <> indentSansFirstLine 4 (unlines (assignList <$> ls)) <> "\n" <>
        "in " <> indentSansFirstLine 3 x
          where
            assignList (name, upt) = locatedNameText name <> " = " <> indentSansFirstLine (3 + length (locatedNameText name)) upt
      (ListUPF []) -> "[]"
      (ListUPF [x]) -> "[" <> x <> "]"
      (ListUPF ls) ->
        "[" <> removeFirstComma (unlines (indentSansFirstLine 2 . (", " <>) <$> ls)) <>
        "]"
          where
            removeFirstComma = \case
              (',':str) -> str
              _         -> error "removeFirstComma: input does not start with a comma"
      (CaseUPF x ls) -> "case " <> x <> " of\n" <>
                        "  " <> indentSansFirstLine 2 (unlines ((\(p, r) -> indentSansFirstLine 2 (prettyPrintPattern (show . PrettyUPT) p <> " -> " <> r))
                                                                <$> ls))

instance PrettyPrintable LocTag where
  showP = const $ pure ""

showFI :: FunctionIndex -> String
showFI = ("F" <>) . show . fromEnum

instance PrettyPrintable1 StuckF where
  showP1 = \case
    DeferSF ind x -> indentWithOneChild' (showFI ind) $ showP x
    EnvSF      -> pure "E"
    SetEnvSF x -> indentWithOneChild' "S" $ showP x
    GateSF     -> pure "G"
    LeftSF x   -> indentWithOneChild' "L" $ showP x
    RightSF x  -> indentWithOneChild' "R" $ showP x

instance PrettyPrintable1 BasicExprF where
  showP1 = \case
    ZeroSF     -> pure "Z"
    PairSF a b -> indentWithTwoChildren' "P" (showP a) (showP b)

instance PrettyPrintable1 AbortableF where
  showP1 = \case
    AbortF      -> pure "!"
    AbortedF am -> pure $ "(aborted - " <> convertAbortMessage am <> ")"

instance PrettyPrintable1 StuckExprF where
  showP1 = \case
    StuckExprB x -> showP1 x
    StuckExprS x -> showP1 x

instance PrettyPrintable1 CompiledExprF where
  showP1 = \case
    CompiledExprB x -> showP1 x
    CompiledExprS x -> showP1 x
    CompiledExprA x -> showP1 x

instance PrettyPrintable1 Term3F where
  showP1 = \case
    Term3B x -> showP1 x
    Term3S x -> showP1 x
    Term3A x -> showP1 x
    Term3Unsized urt -> pure $ "#" <> show urt
    Term3CheckingWrapper _ t c -> indentWithTwoChildren' ":" (showP t) (showP c)

instance (Functor f, PrettyPrintable1 f) => PrettyPrintable (Fix f) where
  showP = showP1 . project

instance {-# OVERLAPPING #-} (PrettyPrintable a, PrettyPrintable1 f) => PrettyPrintable (Cofree f a) where
  showP (a :< x) = (<>) <$> showP a <*> showP1 x

newtype PrettyStuckExpr = PrettyStuckExpr StuckExpr

instance Show PrettyStuckExpr where
  show (PrettyStuckExpr x) = f x where
    f :: StuckExpr -> String
    f x = case b2i x of
      Just n -> show n
      _ -> case x of
        BasicEE (PairSF a b) -> "(" <> f a <> "," <> f b <> ")"
        z                    -> show z

newtype PrettyCompiledExpr = PrettyCompiledExpr CompiledExpr

instance Show PrettyCompiledExpr where
  show (PrettyCompiledExpr x) = f x where
    f :: CompiledExpr -> String
    f x = case b2i x of
      Just n -> show n
      _ -> case x of
        BasicEE (PairSF a b) -> "(" <> f a <> "," <> f b <> ")"
        z                    -> show z
