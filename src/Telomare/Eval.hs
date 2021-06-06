{-# LANGUAGE LambdaCase #-}
module Telomare.Eval where

import           Control.Lens.Plated
import           Control.Monad.Except
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State (StateT)
import qualified Control.Monad.State  as State
import Data.DList (DList)
import           Data.Map             (Map)
import qualified Data.Map             as Map
import Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void
import           Debug.Trace
import           Telomare
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.Possible
import           Telomare.RunTime
import           Telomare.Serializer
import           Telomare.TypeChecker

data ExpP = ZeroP
    | PairP ExpP ExpP
    | VarP
    | SetEnvP ExpP Bool
    | DeferP ExpP
    | AbortP
    | GateP ExpP ExpP
    | LeftP ExpP
    | RightP ExpP
    | TraceP
    deriving (Eq, Show, Ord)

instance Plated ExpP where
  plate f = \case
    PairP a b -> PairP <$> f a <*> f b
    SetEnvP x b -> SetEnvP <$> f x <*> pure b
    DeferP x -> DeferP <$> f x
    GateP l r -> GateP <$> f l <*> f r
    LeftP x -> LeftP <$> f x
    RightP x -> RightP <$> f x
    x -> pure x

data EvalError = RTE RunTimeError
    | TCE TypeCheckError
    | StaticCheckError String
    | CompileConversionError
    | RecursionLimitError BreakExtras
    deriving (Eq, Ord, Show)

type ExpFullEnv = ExprA Bool

newtype BetterMap k v = BetterMap { unBetterMap :: Map k v}

instance Functor (BetterMap k) where
  fmap f (BetterMap x) = BetterMap $ fmap f x

instance (Ord k, Semigroup m) => Semigroup (BetterMap k m) where
  (<>) (BetterMap a) (BetterMap b) = BetterMap $ Map.unionWith (<>) a b

annotateEnv :: IExpr -> (Bool, ExpP)
annotateEnv Zero = (True, ZeroP)
annotateEnv (Pair a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, PairP na nb)
annotateEnv Env = (False, VarP)
annotateEnv (SetEnv x) = let (xt, nx) = annotateEnv x in (xt, SetEnvP nx xt)
annotateEnv (Defer x) = let (_, nx) = annotateEnv x in (True, DeferP nx)
annotateEnv (Gate a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, GateP na nb)
annotateEnv (PLeft x) = LeftP <$> annotateEnv x
annotateEnv (PRight x) = RightP <$> annotateEnv x
annotateEnv Trace = (False, TraceP)

fromFullEnv :: Applicative a => (ExpP -> a IExpr) -> ExpP -> a IExpr
fromFullEnv _ ZeroP         = pure Zero
fromFullEnv f (PairP a b)   = Pair <$> f a <*> f b
fromFullEnv _ VarP          = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x)    = Defer <$> f x
fromFullEnv f (GateP a b)   = Gate <$> f a <*> f b
fromFullEnv f (LeftP x)     = PLeft <$> f x
fromFullEnv f (RightP x)    = PRight <$> f x
fromFullEnv _ TraceP        = pure Trace

instance TelomareLike ExpP where
  fromTelomare = snd . annotateEnv
  toTelomare = fix fromFullEnv

partiallyEvaluate :: ExpP -> Either RunTimeError IExpr
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= (pureEval . optimize))
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

eval' :: IExpr -> Either String IExpr
eval' = pure

convertPT :: (BreakExtras -> Int) -> Term3 -> Term4
convertPT limitLookup (Term3 termMap) =
  let changeTerm = \case
        AuxFrag n -> innerChurchF $ limitLookup n
        ZeroFrag -> pure ZeroFrag
        PairFrag a b -> PairFrag <$> changeTerm a <*> changeTerm b
        EnvFrag -> pure EnvFrag
        SetEnvFrag x -> SetEnvFrag <$> changeTerm x
        DeferFrag fi -> pure $ DeferFrag fi
        AbortFrag -> pure AbortFrag
        GateFrag l r -> GateFrag <$> changeTerm l <*> changeTerm r
        LeftFrag x -> LeftFrag <$> changeTerm x
        RightFrag x -> RightFrag <$> changeTerm x
        TraceFrag -> pure TraceFrag
      mmap = traverse changeTerm termMap
      startKey = succ . fst $ Map.findMax termMap
      newMapBuilder = do
        changedTermMap <- mmap
        State.modify (\(be,i,m) -> ((), i, Map.union changedTermMap m))
      (_,_,newMap) = State.execState newMapBuilder ((), startKey, Map.empty)
  in Term4 newMap

findChurchSize :: Term3 -> Either EvalError Term4
--findChurchSize = pure . convertPT (const 255)
findChurchSize = calculateRecursionLimits'

-- we should probably redo the types so that this is also a type conversion
removeChecks :: Term4 -> Term4
removeChecks (Term4 m) =
  let f = \case
        AbortFrag -> DeferFrag ind
        x -> x
      (ind, newM) = State.runState builder m
      builder = do
        envDefer <- insertAndGetKey EnvFrag
        insertAndGetKey $ DeferFrag envDefer
  in Term4 $ Map.map (transform f) newM

convertAbortMessage :: IExpr -> String
convertAbortMessage = \case
  Pair Zero Zero -> "recursion overflow (should be caught by other means)"
  Pair (Pair Zero Zero) s -> "user abort: " <> g2s s
  x -> "unexpected abort: " <> show x

runStaticChecks :: Term4 -> Either EvalError Term4
runStaticChecks t@(Term4 termMap) =
  let result :: Either IExpr (PossibleExpr Void Void)
      result = toPossible (termMap Map.!) staticAbortSetEval (pure . FunctionX . AuxFrag) AnyX (rootFrag termMap)
  in case result of
            Left x -> Left . StaticCheckError $ convertAbortMessage x
            _      -> pure t

compile :: Term3 -> Either EvalError IExpr
compile t = case toTelomare . removeChecks <$> (findChurchSize t >>= runStaticChecks) of
  Right (Just i) -> pure i
  Right Nothing -> Left CompileConversionError
  Left e -> Left e

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case eval' iexpr of
  Left err -> putStrLn . concat $ ["Failed compiling main, ", show err]
  Right peExp ->
    let mainLoop s = do
          -- result <- optimizedEval (app peExp s)
          result <- simpleEval (app peExp s)
          case result of
            Zero -> putStrLn "aborted"
            (Pair disp newState) -> do
              putStrLn . g2s $ disp
              case newState of
                Zero -> putStrLn "done"
                _ -> do
                  inp <- s2g <$> getLine
                  mainLoop $ Pair inp newState
            r -> putStrLn $ concat ["runtime error, dumped ", show r]
    in mainLoop Zero

-- |Same as `evalLoop`, but keeping what was displayed.
evalLoop_ :: IExpr -> IO String
evalLoop_ iexpr = case eval' iexpr of
  Left err -> pure . concat $ ["Failed compiling main, ", show err]
  Right peExp ->
    let mainLoop prev s = do
          -- result <- optimizedEval (app peExp s)
          result <- simpleEval (app peExp s)
          case result of
            Zero -> pure $ prev <> "\n" <> "aborted"
            (Pair disp newState) -> do
              let d = g2s $ disp
              case newState of
                Zero -> pure $ prev <> "\n" <> d <> "\ndone"
                _ -> do
                  inp <- s2g <$> getLine
                  mainLoop (prev <> "\n" <> d) $ Pair inp newState
            r -> pure $ concat ["runtime error, dumped ", show r]
    in mainLoop "" Zero

-- map of contamination indices to test functions
  {-
contaminationMap :: BasicPossible -> BetterMap BreakExtras (DList (FragExpr BreakExtras, BasicPossible))
contaminationMap =
  let makeMap cSet = \case
        EitherX a b -> makeMap cSet a <> makeMap cSet b
        AnnotateX p x -> makeMap (Set.insert p cSet) x
        PairX f i -> makeKeyVal cSet f i
        z -> error $ "contaminationMap-makeMap unexpected value: " <> show z
      makeKeyVal cSet f i = case f of
        EitherX a b -> makeKeyVal cSet a i <> makeKeyVal cSet b i
        AnnotateX p x -> makeKeyVal (Set.insert p cSet) x i
        FunctionX frag -> BetterMap $ foldr (\k -> Map.insert k (pure (frag, i))) mempty cSet
        z -> error $ "contaminationMap-makeKeyVal unexpected value: " <> show z
  in makeMap Set.empty . (\bp -> trace ("basicpossible encoded contamination map is" <> show bp) bp)
-}
splitTests :: BasicPossible -> DList (FragExpr BreakExtras, BasicPossible)
splitTests =
  let makeList = \case
        EitherX a b -> makeList a <> makeList b
        PairX f i -> makePair f i
        z -> error $ "splitTests-makeList unexpected value: " <> show z
      makePair f i = case f of
        EitherX a b -> makePair a i <> makePair b i
        FunctionX frag -> pure (frag, i)
        z -> error $ "splitTests-makePair unexpected value: " <> show z
      -- traceTests bl = trace ("basicpossible tests are " <> show bl) bl
      traceTests = id
  in traceTests . makeList

limitedMFix :: Monad m => (a -> m a) -> m a -> m a
limitedMFix f x = iterate (>>= trace "fixing again" f) x !! 10

calculateRecursionLimits' :: Term3 -> Either EvalError Term4
calculateRecursionLimits' t3@(Term3 termMap) =
  let testMapBuilder :: StateT (Map BreakExtras RecursionTest) (Reader (BreakExtras -> Int)) BasicPossible
      mapLookup' k = case Map.lookup k termMap of
          Just v -> v
          _ -> error ("calculateRecursionLimits outside mapLookup bad key " <> show k)
      testMapBuilder = toPossible mapLookup' testBuildingSetEval annotateAux AnyX (rootFrag termMap)
      annotateAux ur = trace "annotating AUX" . pure . AnnotateX ur . FunctionX $ AuxFrag ur
      step1 :: Reader (BreakExtras -> Int) (Map BreakExtras RecursionTest)
      step1 = State.execStateT testMapBuilder mempty
      findLimit :: BreakExtras -> RecursionTest -> Either BreakExtras Int
      findLimit churchSizingIndex tests =
        {-
        let unhandleableOther =
              let (lMap, kTests, gMap) = Map.splitLookup churchSizingIndex . unBetterMap . contaminationMap $ runReader tests 1
                  otherMap = lMap <> gMap
              in Set.lookupMin $ Map.keysSet otherMap
-}
        let unhandleableOther = Nothing
        in case unhandleableOther of
          Just o -> Left o
          _ -> let abortsAt i = let tests' = splitTests $ runReader tests i -- testsMapLookup . unBetterMap . contaminationMap $ runReader tests i
                                    traceTest (f, bp) t = if containsAux mapLookup' f || containsAux' mapLookup' bp
                                      then trace ("test with aux: " <> show f <> " *** " <> show bp) . t
                                      else t
                                    traceAuxes = foldr traceTest id tests'
                                    wrapAux = pure . FunctionX . AuxFrag
                                    mapLookup k = case Map.lookup k termMap of
                                      Just v -> v
                                      _ -> error ("calculateRecursionLimits findlimit mapLookup bad key " <> show k)
                                    testsMapLookup m = case Map.lookup churchSizingIndex m of
                                      Just v -> v
                                      _ -> error ("calculateRecursionLimits findlimit testsMapLookup bad key " <> show churchSizingIndex)
                                    runTest (frag, inp) = null . traceAuxes $ toPossible mapLookup sizingAbortSetEval wrapAux inp frag
                                in or $ fmap runTest tests'
                   (ib, ie) = if not (abortsAt 255) then (0, 255) else error "findchurchsize TODO" -- (256, maxBound)
                   findC b e | b > e = trace ("crl b is found at " <> show b) b
                   findC b e = let midpoint = div (b + e) 2
                               in trace ("midpoint is now " <> show midpoint) $ if abortsAt midpoint then findC (midpoint + 1) e else findC b (midpoint - 1)
               in pure $ findC ib ie
      mapLimits :: Map BreakExtras RecursionTest -> Either BreakExtras (Map BreakExtras Int)
      mapLimits = sequence . Map.mapWithKey findLimit
      unwrappedReader :: (BreakExtras -> Int) -> Map BreakExtras RecursionTest
      unwrappedReader = runReader step1
      fixableMapLookup m k = case (trace ("fml is m null? " <> show (null m)) null m, Map.lookup k m) of
          (True, _) -> 0
          (_, Just v) -> v
          _ -> error ("calculateRecursionLimits fixableMapLookup bad key " <> show k)
      fixable :: (BreakExtras -> Int) -> Either BreakExtras (BreakExtras -> Int)
      fixable = fmap fixableMapLookup . mapLimits . unwrappedReader
  -- in case mfix fixable of
  -- this limitedMFix solution is bad, and will eventually break on deeply-nested referentiality.
  in case limitedMFix fixable (Right (const 1)) of
    Left be -> Left $ RecursionLimitError be
    Right limits -> trace "found limits!" . pure $ convertPT limits t3
