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
  | ClosureX (FragExpr b) (PossibleExpr a b) -- hack for lazy evaluation
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
  ClosureX _ x -> annotations x
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
    -- ClosureX _ 
    _ -> True

containsAux :: (FragIndex -> FragExpr a) -> FragExpr a -> Bool
containsAux fragLookup = let recur = containsAux fragLookup in \case
  PairFrag a b -> recur a || recur b
  SetEnvFrag x -> recur x
  DeferFrag ind -> recur $ fragLookup ind
  GateFrag l r -> recur l || recur r
  LeftFrag x -> recur x
  RightFrag x -> recur x
  AuxFrag _ -> True
  _ -> False

containsAux' :: (FragIndex -> FragExpr b) -> PossibleExpr a b -> Bool
containsAux' fragLookup = let recur = containsAux' fragLookup in \case
  PairX a b -> recur a || recur b
  EitherX a b -> recur a || recur b
  FunctionX f -> containsAux fragLookup f
  AnnotateX _ x -> recur x
  ClosureX f i -> containsAux fragLookup f || recur i
  _ -> False

type BasicPossible = PossibleExpr BreakExtras BreakExtras
type RecursionTest = Reader Int BasicPossible
type TestMapBuilder = StateT (Map BreakExtras RecursionTest) (Reader (BreakExtras -> Int))

toPossible :: (Show a, Eq a, Show b, Eq b, Monad m) => (FragIndex -> FragExpr b)
  -> ((PossibleExpr a b -> FragExpr b -> m (PossibleExpr a b)) -> PossibleExpr a b-> PossibleExpr a b-> PossibleExpr a b -> m (PossibleExpr a b))
  -> (b -> m (PossibleExpr a b))
  -> PossibleExpr a b -> FragExpr b -> m (PossibleExpr a b)
toPossible fragLookup setEval doAnnotation env =
  let toPossible' = toPossible fragLookup setEval doAnnotation
      traceThrough x = x -- trace ("toPossible dump: " <> show x) x
      recur = toPossible' env . traceThrough
      envWrap x = case x of
        DeferFrag ind -> FunctionX $ fragLookup ind
        x -> ClosureX x env
      force x = case x of
        ClosureX x env -> toPossible' env x
        _ -> pure x
  in \case
  ZeroFrag -> pure ZeroX
  -- PairFrag a b -> PairX <$> recur a <*> recur b
  PairFrag a b -> pure $ PairX (envWrap a) (envWrap b)
  EnvFrag -> pure env
  LeftFrag x -> let process = \case
                      AnnotateX a px -> AnnotateX a <$> process px
                      -- PairX ln _ -> pure ln
                      PairX ln _ -> force ln
                      z@ZeroX -> pure z
                      a@AnyX -> pure a
                      EitherX a b -> EitherX <$> process a <*> process b
                      z -> error $ "toPossible leftFrag unexpected: " <> show z
                in recur x >>= process
  RightFrag x -> let process = \case
                       AnnotateX a px -> AnnotateX a <$> process px
                       -- PairX _ rn -> pure rn
                       PairX _ rn -> force rn
                       z@ZeroX -> pure z
                       a@AnyX -> pure a
                       EitherX a b -> EitherX <$> process a <*> process b
                       z -> error $ "toPossible rightFrag unexpected: " <> show z
                 in recur x >>= process
  SetEnvFrag x -> recur x >>=
    let processSet = \case
          AnnotateX a px -> AnnotateX a <$> processSet px
          -- PairX ft it -> setEval toPossible' env ft it
          PairX ft it -> do
            ft' <- force ft
            it' <- force it
            setEval toPossible' env ft' it'
          EitherX a b -> (<>) <$> processSet a <*> processSet b
          z -> error $ "toPossible setenv not pair: " <> show z
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
      -- toExprList' :: PossibleExpr a b -> Either IExpr (DList.DList IExpr)
      toExprList' x = let pure' = pure . pure -- should I use Compose here?
                      in case x of
        ZeroX -> pure' Zero
        PairX a b -> do
          na <- toExprList' a
          nb <- toExprList' b
          pure $ Pair <$> na <*> nb
        -- EitherX a b -> (<>) <$> toExprList' a <*> toExprList' b
        EitherX a b -> let comb :: DList.DList a -> DList.DList a -> DList.DList a
                           comb = (<>)
                       in comb <$> toExprList' a <*> toExprList' b
        AnnotateX _ x -> toExprList' x
        ClosureX f i -> sRecur i f >>= toExprList'
      setEval ft it = case ft of
        FunctionX af -> case af of
          {-
          GateFrag l r -> case it of
            AnnotateX _ px -> setEval ft px
            ZeroX -> sRecur' l
            PairX _ _ -> sRecur' r
            -- zo | foldl (\b a -> a == Zero || b) False (toIExprList zo) -> (<>) <$> sRecur' l <*> sRecur' r -- this takes care of EitherX with an embedded ZeroX
            zo | foldl (\b a -> a == Zero || b) False (toIExprList zo) -> (<>) <$> sRecur' l <*> sRecur' r -- this takes care of EitherX with an embedded ZeroX
            EitherX _ _ -> sRecur' r
            AnyX -> (<>) <$> sRecur' l <*> sRecur' r
            z -> error $ "abortingSetEval Gate unexpected input: " <> show z
-}
          GateFrag l r -> case (it, toExprList' it) of
            (_, Left e) -> Left e -- if evaluating input aborts, bubble up abort result
            (AnyX, _) -> (<>) <$> sRecur' l <*> sRecur' r
            (_, Right iList) -> case (elem Zero iList, length iList > 1) of
              (True, True) -> (<>) <$> sRecur' l <*> sRecur' r
              (True, False) -> sRecur' l
              _ -> sRecur' r
  {-
          AbortFrag -> case it of
            AnnotateX _ px -> setEval ft px
            ZeroX -> pure $ FunctionX EnvFrag
            nzo | not . null . foldr abortCombine abortDefault $ toIExprList nzo
                  -> case foldr abortCombine abortDefault $ toIExprList nzo of
                    Nothing -> error "abortSetEval: impossible"
                    Just x -> Left x
            z -> error $ "abortingSetEval Abort unexpected input: " <> show z
-}
          AbortFrag -> case (filter (/= Zero) . toList) <$> toExprList' it of
            Left e -> Left e -- if evaluating input aborts, bubble up abort result
            Right l -> case foldr abortCombine abortDefault $ l of
              Nothing -> pure $ FunctionX EnvFrag
              -- Just e -> trace ("aborting from input of " <> show it) Left e
              Just e -> trace ("aborting with " <> show l) Left e
          -- From Defer
          AuxFrag _ -> error "abortSetEval: should be no AuxFrag here"
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
      force x = case x of
        ClosureX x env -> sRecur env x
        _ -> pure x
      deepForce = \case
        PairX a b -> PairX <$> deepForce a <*> deepForce b
        EitherX a b -> EitherX <$> deepForce a <*> deepForce b
        AnnotateX a x -> AnnotateX a <$> deepForce x -- we could probably prune annotations for where this will be used
        ClosureX f i -> sRecur i f
        x -> pure x
      initialPoisoned = annotations it'
      setEval poisonedSet ft it = case ft of
        AnnotateX p pf -> AnnotateX p <$> trace "tbse doing some annotate" setEval (Set.insert p poisonedSet) pf it
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
            error "should not be directly in auxfrag"
  {-
            cLimit <- ($ ind) <$> lift Reader.ask
-}
            cLimit <- ((\c -> if c < 0 then error ("climit is " <> show (ind, c)) else c) . ($ ind)) <$> lift Reader.ask
            let appP ii = sRecur ii $ SetEnvFrag EnvFrag -- simple hack to simulate function application
            iterate (>>= appP) (pure it) !! cLimit
          LeftFrag (RightFrag (RightFrag (RightFrag (AuxFrag ind)))) -> do
            {-
            cLimit <- ($ ind) <$> lift Reader.ask
-}
            cLimit <- ((\c -> if c < 0 then error ("climit is " <> show (ind, c)) else c) . ($ ind)) <$> lift Reader.ask
            let appP ii = sRecur ii $ SetEnvFrag EnvFrag -- simple hack to simulate function application
	    	pruneAnnotations (annoSet, AnnotateX i x) = pruneAnnotations (Set.insert i annoSet, x)
		pruneAnnotations (annoSet, x) = (annoSet, x)
                extractR (aSet, pairA) = do
                  pairB <- case pairA of
                    PairX _ wrappedB -> force wrappedB
                    _ -> error ("extractR bad " <> show pairA)
                  pairC <- case pairB of
                    PairX _ wrappedC -> force wrappedC
                    _ -> error ("extractR bad " <> show pairA)
                  pairD <- case pairC of
                    PairX _ wrappedD -> force wrappedD
                    _ -> error ("extractR bad " <> show pairA)
                  case pairD of
                    PairX wrappedR _ -> (\r -> foldr AnnotateX r aSet) <$> force wrappedR
                    _ -> error ("extractR bad " <> show pairA)
            itResult <- iterate (>>= appP) (pure $ AnnotateX ind it) !! cLimit
            extractR $ pruneAnnotations (mempty, itResult)
  {-
            case pruneAnnotations (mempty, itResult) of
              --PairX (PairX _ (PairX _ (PairX _ r))) _ -> pure r
              (aSet, PairX _ (PairX _ (PairX _ (PairX r _)))) -> pure $ foldr AnnotateX r aSet -- pure r
              z -> error ("testBuildingSetEval AuxFrag part, unexpected " <> show z)
-}
          x -> let alterSizeTest v = \case
                     Nothing -> pure v
                     Just e -> pure $ (<>) <$> e <*> v
                   addSizeTest :: BreakExtras -> RecursionTest -> TestMapBuilder ()
                   addSizeTest k v = State.modify $ Map.alter (alterSizeTest v) k
                   -- hasContamination = not . null . annotations
		   hasContamination = not . null $ poisonedSet
                   conditionallyAddTests :: TestMapBuilder BasicPossible -> TestMapBuilder BasicPossible
                   conditionallyAddTests opt =
                     let truncatedResult = flip Reader.runReader (const 1) $ State.evalStateT opt Map.empty -- force church numerals to 1 to evaluate poison typing
                     in do
                       {-
                       let showAuxed x = if containsAux' x
                             then trace ("adding size test, but it has aux: " <> show x) x
                             else x
-}
                       let showAuxed = id
                       when (hasContamination && noAnnotatedFunctions truncatedResult) . showAuxed $ do
                         -- mapM_ (flip addSizeTest (pure . PairX ft $ deepForce it)) poisonedSet
                         fit <- deepForce it
                         mapM_ (flip addSizeTest (pure $ PairX ft fit)) poisonedSet
			 {-
                       if not (null poisonedSet)
		       then trace ("contaminated thing " <> show ft') pure ()
		       else pure ()
		       -}
                       -- trace ("hc " <> show hasContamination <> " naf " <> show (noAnnotatedFunctions truncatedResult)) opt
                       -- trace ("itdump " <> show it') opt
                       opt
               in conditionallyAddTests $ sRecur it x
  in setEval initialPoisoned ft' it'
