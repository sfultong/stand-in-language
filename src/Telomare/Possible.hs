{-# LANGUAGE LambdaCase #-}
module Telomare.Possible where

import           Control.Applicative
import Control.Monad
import Control.Monad.Reader (Reader)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State (StateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class
import qualified Data.DList          as DList
import           Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import           Data.Monoid
import Data.Set (Set)
import qualified Data.Set            as Set
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

-- notice that AnyX will translate to an empty list, which may not be expected
toIExprList :: PossibleExpr a b -> DList.DList IExpr
toIExprList = \case
  ZeroX -> pure Zero
  PairX a b -> Pair <$> toIExprList a <*> toIExprList b
  EitherX a b -> toIExprList a <> toIExprList b
  AnnotateX _ x -> toIExprList x
  _ -> mempty

annotations :: Ord a => PossibleExpr a b -> Set a
annotations = \case
  PairX a b -> annotations a <> annotations b
  EitherX a b -> annotations a <> annotations b
  AnnotateX a x -> Set.insert a $ annotations x
  _ -> mempty

noAnnotatedFunctions :: PossibleExpr a b -> Bool
noAnnotatedFunctions =
  let testF = \case
        AnnotateX _ x -> testF x
        FunctionX _ -> False
        EitherX a b -> testF a && testF b
        x -> noAnnotatedFunctions x
  in \case
    PairX a b -> noAnnotatedFunctions a && noAnnotatedFunctions b
    EitherX a b -> noAnnotatedFunctions a && noAnnotatedFunctions b
    AnnotateX _ x -> testF x
    _ -> True

type BasicPossible = PossibleExpr BreakExtras BreakExtras
type RecursionTest = Reader Int BasicPossible
type TestMapBuilder = StateT (Map BreakExtras RecursionTest) (Reader (BreakExtras -> Int))

toPossible :: (Show a, Eq a, Show b, Eq b, Monad m) => (FragIndex -> FragExpr b)
  -> ((PossibleExpr a b -> FragExpr b -> m (PossibleExpr a b)) -> PossibleExpr a b-> PossibleExpr a b-> PossibleExpr a b -> m (PossibleExpr a b))
  -> (b -> m (PossibleExpr a b))
  -> PossibleExpr a b -> FragExpr b -> m (PossibleExpr a b)
toPossible fragLookup setEval doAnnotation env =
  let toPossible' = toPossible fragLookup setEval doAnnotation
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
          PairX ft it    -> setEval toPossible' env ft it
          EitherX a b    -> (<>) <$> processSet a <*> processSet b
          z              -> error $ "buildTestMap setenv not pair: " <> show z
    in processSet
  DeferFrag ind -> pure . FunctionX $ fragLookup ind -- process Defer here rather than SetEnvFrag to reduce arguments to setEval
  g@(GateFrag _ _) -> pure $ FunctionX g
  AbortFrag -> pure $ FunctionX AbortFrag
  a@(AuxFrag ur) -> doAnnotation ur
  TraceFrag -> pure env

abortSetEval :: (Show a, Eq a, Show b, Eq b) => (IExpr -> Maybe IExpr -> Maybe IExpr)
  -> Maybe IExpr
  -> (PossibleExpr a b -> FragExpr b -> Either IExpr (PossibleExpr a b))
  -> PossibleExpr a b -> PossibleExpr a b -> PossibleExpr a b -> Either IExpr (PossibleExpr a b)
abortSetEval abortCombine abortDefault sRecur env ft' it' =
  let sRecur' = sRecur env
      setEval ft it = case ft of
        FunctionX af -> case af of
          GateFrag l r -> case it of
            AnnotateX _ px -> setEval ft px
            ZeroX -> sRecur' l
            PairX _ _ -> sRecur' r
            zo | foldl (\b a -> a == Zero || b) False (toIExprList zo) -> (<>) <$> sRecur' l <*> sRecur' r -- this takes care of EitherX with an embedded ZeroX
            EitherX _ _ -> sRecur' r
            AnyX -> (<>) <$> sRecur' l <*> sRecur' r
            z -> error $ "abortingSetEval Gate unexpected input: " <> show z
          AbortFrag -> case it of
            AnnotateX _ px -> setEval ft px
            ZeroX -> pure $ FunctionX EnvFrag
            nzo | not . null . foldr abortCombine abortDefault $ toIExprList nzo
                  -> case foldr abortCombine abortDefault $ toIExprList nzo of
                    Nothing -> error "abortSetEval: impossible"
                    Just x -> Left x
            z -> error $ "abortingSetEval Abort unexpected input: " <> show z
          -- From Defer
          x -> sRecur it x
        AnnotateX _ nf -> setEval nf it
  in setEval ft' it'

staticAbortSetEval :: (Show a, Eq a, Show b, Eq b) =>
  (PossibleExpr a b -> FragExpr b -> Either IExpr (PossibleExpr a b))
  -> PossibleExpr a b -> PossibleExpr a b -> PossibleExpr a b -> Either IExpr (PossibleExpr a b)
staticAbortSetEval = let combine a b = case (a,b) of
                           (Zero, _) -> Nothing
                           (_, Nothing) -> Nothing
                           (x, _) -> Just x
                     in abortSetEval combine (Just Zero) -- Just Zero is a dummy value. It shouldn't be returned

sizingAbortSetEval :: (Show a, Eq a, Show b, Eq b) => (PossibleExpr a b -> FragExpr b -> Either IExpr (PossibleExpr a b))
  -> PossibleExpr a b -> PossibleExpr a b -> PossibleExpr a b -> Either IExpr (PossibleExpr a b)
sizingAbortSetEval = let combine a b = case (a,b) of
                                         (_,Just x) -> Just x
                                         (Pair Zero Zero, _) -> Just $ Pair Zero Zero
                                         _ -> Nothing
                     in abortSetEval combine Nothing

testBuildingSetEval :: (BasicPossible -> FragExpr BreakExtras -> TestMapBuilder BasicPossible)
  -> BasicPossible -> BasicPossible -> BasicPossible -> TestMapBuilder BasicPossible
testBuildingSetEval sRecur env ft' it' =
  let sRecur' = sRecur env
      setEval poisonedSet ft it = case ft of
        AnnotateX p pf -> AnnotateX p <$> setEval (Set.insert p poisonedSet) pf it
        FunctionX af -> case af of
          AbortFrag -> pure $ FunctionX EnvFrag
          GateFrag l r -> let doGate = \case
                                AnnotateX p pf -> AnnotateX p <$> doGate pf
                                ZeroX -> sRecur' l
                                PairX _ _ -> sRecur' r
                                zo | foldl (\b a -> a == Zero || b) False (toIExprList zo) -> (<>) <$> sRecur' l <*> sRecur' r -- this takes care of EitherX with an embedded ZeroX
                                EitherX _ _ -> sRecur' r
                                AnyX -> (<>) <$> sRecur' l <*> sRecur' r
                                z -> error $ "buildingSetEval Gate unexpected input: " <> show z
                       in doGate it
          AuxFrag ind -> do
            cLimit <- ($ ind) <$> lift Reader.ask
            let (c,e,ii) = case it of
                  (PairX i' (PairX (PairX c' e') _)) -> (c',e',i')
                  z -> error $ "buildingSetEval AuxF app - bad environment: " <> show z
                appP ii = sRecur (PairX c (PairX ii e)) $ SetEnvFrag EnvFrag -- simple hack to simulate function application
            iterate (>>= appP) (pure ii) !! cLimit
          x -> let alterSizeTest v = \case
                     Nothing -> pure v
                     Just e -> pure $ (<>) <$> e <*> v
                   addSizeTest :: BreakExtras -> RecursionTest -> TestMapBuilder ()
                   addSizeTest k v = State.modify $ Map.alter (alterSizeTest v) k
                   hasContamination = not . null . annotations
                   conditionallyAddTests :: TestMapBuilder BasicPossible -> TestMapBuilder BasicPossible
                   conditionallyAddTests opt =
                     let truncatedResult = flip Reader.runReader (const 1) $ State.evalStateT opt Map.empty -- force church numerals to 1 to evaluate poison typing
                     in do
                       when (hasContamination ft && noAnnotatedFunctions truncatedResult) $
                         mapM_ (flip addSizeTest (pure $ PairX ft it)) poisonedSet
                       opt
               in conditionallyAddTests $ sRecur it x
  in setEval mempty ft' it'
