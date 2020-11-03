{-# LANGUAGE LambdaCase #-}
module Telomare.Possible where

import           Control.Applicative
import           Data.Char
import qualified Data.DList          as DList
import           Data.Foldable
import           Data.Monoid
import           Data.Void
import           Debug.Trace
import           Telomare

data PossibleExpr a b
  = ZeroX
  | AnyX
  | PairX (PossibleExpr a b) (PossibleExpr a b)
  | EitherX (PossibleExpr a b) (PossibleExpr a b)
  | FunctionX (FragExpr b)
  | AnnotateX a (PossibleExpr a b)
  deriving (Eq, Ord, Show)

instance (Eq a, Eq b) => Semigroup (PossibleExpr a b) where
  (<>) a b = case (a,b) of
    (ZeroX, ZeroX)                      -> ZeroX
    (AnyX, _)                           -> AnyX
    (_, AnyX)                           -> AnyX
    (AnnotateX x a, b)                  -> AnnotateX x $ a <> b
    (a, AnnotateX x b)                  -> AnnotateX x $ a <> b
    (FunctionX a, FunctionX b) | a == b -> FunctionX a
    (PairX a b, PairX c d) | a == c     -> PairX a (b <> d)
    (PairX a b, PairX c d) | b == d     -> PairX (a <> c) b
    (EitherX a b, EitherX c d)          -> EitherX (a <> c) (b <> d)
    _                                   -> EitherX a b

booleanPossibilities :: PossibleExpr a b -> DList.DList Bool
booleanPossibilities = \case
  ZeroX -> DList.singleton False
  PairX _ _ -> DList.singleton True
  EitherX a b -> booleanPossibilities a <> booleanPossibilities b
  _ -> DList.empty

getFirstNonZero :: PossibleExpr a b -> Maybe (PossibleExpr a b)
getFirstNonZero = \case
  ZeroX -> Nothing
  p@(PairX _ _) -> pure p
  EitherX a b -> getFirstNonZero a <|> getFirstNonZero b
  AnnotateX _ x -> getFirstNonZero x
  FunctionX _ -> Nothing
  AnyX -> pure AnyX

possibleString :: PossibleExpr a b -> String
possibleString =
  let p2i = \case
        ZeroX -> pure 0
        PairX a b -> fmap succ . (+) <$> p2i a <*> p2i b
        _ -> Nothing
      p2is = \case
        ZeroX -> pure []
        PairX n g -> (:) <$> p2i n <*> p2is g
        _ -> Nothing
      cleanString = \case
        Just s -> s
        _ -> "unknown error"
  in cleanString . fmap (map chr) . p2is

possibleString' :: PossibleExpr a b -> String
possibleString' x = case getFirstNonZero x of
  Nothing -> error "shouldn't happen error in possibleString'"
  Just es -> possibleString es

type BasicPossible = PossibleExpr Void

toPossible :: (Show a, Eq a, Show b, Eq b, Monad m) => (FragIndex -> FragExpr b)
  -> ((PossibleExpr a b -> FragExpr b -> m (PossibleExpr a b)) -> PossibleExpr a b-> PossibleExpr a b-> PossibleExpr a b -> m (PossibleExpr a b))
  -> PossibleExpr a b -> FragExpr b -> m (PossibleExpr a b)
toPossible fragLookup setEval env =
  let toPossible' = toPossible fragLookup setEval
      recur = toPossible' env
  in \case
  ZeroFrag -> pure ZeroX
  PairFrag a b -> PairX <$> recur a <*> recur b
  EnvFrag -> pure env
  LeftFrag x -> let process = \case
                      AnnotateX a px -> AnnotateX a <$> process px
                      PairX ln _ -> pure ln
                      z@ZeroX -> pure z
                      a@AnyX -> pure a
                      EitherX a b -> EitherX <$> process a <*> process b
                      z -> error $ "buildTestMap leftFrag unexpected: " <> show z
                in recur x >>= process
  RightFrag x -> let process = \case
                       AnnotateX a px -> AnnotateX a <$> process px
                       PairX _ rn -> pure rn
                       z@ZeroX -> pure z
                       a@AnyX -> pure a
                       EitherX a b -> EitherX <$> process a <*> process b
                       z -> error $ "buildTestMap rightFrag unexpected: " <> show z
                 in recur x >>= process
  SetEnvFrag x -> recur x >>=
    let processSet = \case
          AnnotateX a px -> AnnotateX a <$> processSet px
          PairX ft it -> setEval toPossible' env ft it
          EitherX a b -> (<>) <$> processSet a <*> processSet b
          z -> error $ "buildTestMap setenv not pair: " <> show z
    in processSet
  DeferFrag ind -> pure . FunctionX $ fragLookup ind -- process Defer here rather than SetEnvFrag to reduce arguments to setEval
  g@(GateFrag _ _) -> pure $ FunctionX g
  AbortFrag -> pure $ FunctionX AbortFrag
  a@(AuxFrag ur) -> pure $ FunctionX a -- TODO, poison here? pure $ PoisonedBy ur $ ArrTypeN a
  TraceFrag -> pure env


-- f x = if x == 0 then abort "divide by zero" else 2 / x
-- main x = f x + f 0

{-
staticAbortSetEval :: (BasicPossible -> FragExpr BreakExtras -> Maybe BasicPossible)
  -> BasicPossible -> BasicPossible -> BasicPossible -> Maybe BasicPossible
-}
staticAbortSetEval :: (Show a, Eq a, Show b, Eq b) => (PossibleExpr a b -> FragExpr b -> Either String (PossibleExpr a b))
  -> PossibleExpr a b -> PossibleExpr a b -> PossibleExpr a b -> Either String (PossibleExpr a b)
staticAbortSetEval sRecur env ft' it' =
  let sRecur' = sRecur env
      setEval ft it = case ft of
        FunctionX af -> case af of
          GateFrag l r -> case it of
            AnnotateX _ px -> setEval ft px --abortingSetEval sRecur env f px
            ZeroX -> sRecur' l
            PairX _ _ -> sRecur' r
            -- zo | zeroOption zo -> pCombine <$> sRecur' l <*> sRecur' r -- this takes care of EitherTypeN with an embedded ZeroTypeN
            zo | not . getAll . foldMap All $ booleanPossibilities zo -> (<>) <$> sRecur' l <*> sRecur' r -- this takes care of EitherX with an embedded ZeroX
            EitherX _ _ -> sRecur' r
            AnyX -> (<>) <$> sRecur' l <*> sRecur' r
            z -> error $ "abortingSetEval Gate unexpected input: " <> show z
          AbortFrag -> case it of
            AnnotateX _ px -> setEval ft px
            ZeroX -> pure $ FunctionX EnvFrag
            -- nzo | nonZeroOption nzo -> Nothing
            nzo | getAll . foldMap All $ booleanPossibilities nzo -> Left . possibleString' $ nzo
            z -> error $ "abortingSetEval Abort unexpected input: " <> show z
          -- From Defer
          x -> sRecur it x
        AnnotateX _ nf -> setEval nf it
  in setEval ft' it'
