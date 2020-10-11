{-# LANGUAGE LambdaCase #-}
module SIL.Eval where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State (State, StateT)
import Data.DList (DList)
import Data.Map (Map)
import Debug.Trace
import qualified Control.Monad.State as State
import qualified Data.DList as DList
import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer

data ExpP
  = ZeroP
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

instance EndoMapper ExpP where
  endoMap f ZeroP = f ZeroP
  endoMap f (PairP a b) = f $ PairP (endoMap f a) (endoMap f b)
  endoMap f VarP = f VarP
  endoMap f (SetEnvP x fe) = f $ SetEnvP (endoMap f x) fe
  endoMap f (DeferP x) = f . DeferP $ endoMap f x
  endoMap f AbortP = f AbortP
  endoMap f (GateP a b) = f $ GateP (endoMap f a) (endoMap f b)
  endoMap f (LeftP x) = f . LeftP $ endoMap f x
  endoMap f (RightP x) = f . RightP $ endoMap f x
  endoMap f TraceP = f TraceP

data EvalError
  = RTE RunTimeError
  | TCE TypeCheckError
  deriving (Eq, Ord, Show)

type ExpFullEnv = ExprA Bool

newtype BetterMap k v = BetterMap { unBetterMap :: Map k v}

instance Functor (BetterMap k) where
  fmap f (BetterMap x) = BetterMap $ fmap f x

instance (Ord k, Semigroup m) => Semigroup (BetterMap k m) where
  (<>) (BetterMap a) (BetterMap b) = BetterMap $ Map.unionWith (<>) a b

instance (Ord k, Monoid m) => Monoid (BetterMap k m) where
  mempty = BetterMap mempty

annotateEnv :: IExpr -> (Bool, ExpP)
annotateEnv Zero = (True, ZeroP)
annotateEnv (Pair a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, PairP na nb)
annotateEnv Env = (False, VarP)
annotateEnv (SetEnv x) = let (xt, nx) = annotateEnv x in (xt, SetEnvP nx xt)
annotateEnv (Defer x) = let (_, nx) = annotateEnv x in (True, DeferP nx)
annotateEnv Abort = (True, AbortP)
annotateEnv (Gate a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, GateP na nb)
annotateEnv (PLeft x) = LeftP <$> annotateEnv x
annotateEnv (PRight x) = RightP <$> annotateEnv x
annotateEnv Trace = (False, TraceP)

fromFullEnv :: Applicative a => (ExpP -> a IExpr) -> ExpP -> a IExpr
fromFullEnv _ ZeroP = pure Zero
fromFullEnv f (PairP a b) = Pair <$> f a <*> f b
fromFullEnv _ VarP = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x) = Defer <$> f x
fromFullEnv _ AbortP = pure Abort
fromFullEnv f (GateP a b) = Gate <$> f a <*> f b
fromFullEnv f (LeftP x) = PLeft <$> f x
fromFullEnv f (RightP x) = PRight <$> f x
fromFullEnv _ TraceP = pure Trace

instance SILLike ExpP where
  fromSIL = snd . annotateEnv
  toSIL = fix fromFullEnv

partiallyEvaluate :: ExpP -> Either RunTimeError IExpr
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= (pureEval . optimize))
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

eval' :: IExpr -> Either String IExpr
eval' = pure

convertPT :: (BreakExtras -> Int) -> Term3 -> Term4
convertPT limitLookup (Term3 termMap) =
  let changeTerm = \case
        AuxF n -> deferF . innerChurchF $ limitLookup n
        ZeroF -> pure ZeroF
        PairF a b -> PairF <$> changeTerm a <*> changeTerm b
        EnvF -> pure EnvF
        SetEnvF x -> SetEnvF <$> changeTerm x
        DeferF fi -> pure $ DeferF fi
        AbortF -> pure AbortF
        GateF l r -> GateF <$> changeTerm l <*> changeTerm r
        LeftF x -> LeftF <$> changeTerm x
        RightF x -> RightF <$> changeTerm x
        TraceF -> pure TraceF
      mmap = traverse changeTerm termMap
      startKey = succ . fst $ Map.findMax termMap
      newMapBuilder = do
        changedTermMap <- mmap
        State.modify (\(t,i,m) -> (t,i, Map.union changedTermMap m))
      (_,_,newMap) = State.execState newMapBuilder (0,startKey, Map.empty)
  in Term4 newMap

-- map of contamination indices to test functions
contaminationMap :: PoisonType -> BetterMap BreakExtras (DList (FragExpr BreakExtras, PoisonType))
contaminationMap =
  let makeMap cSet = \case
        EitherTypeN a b -> makeMap cSet a <> makeMap cSet b
        PoisonedBy p x -> makeMap (Set.insert p cSet) x
        PairTypeN f i -> makeKeyVal cSet f i
        z -> error $ "contaminationMap-makeMap unexpected value: " <> show z
      makeKeyVal cSet f i = case f of
        EitherTypeN a b -> makeKeyVal cSet a i <> makeKeyVal cSet b i
        PoisonedBy p x -> makeKeyVal (Set.insert p cSet) x i
        ArrTypeN frag -> BetterMap $ foldr (\k -> Map.insert k (pure (frag, i))) mempty cSet
        z -> error $ "contaminationMap-makeKeyVal unexpected value: " <> show z
  in makeMap Set.empty

limitedMFix :: Monad m => (a -> m a) -> m a -> m a
limitedMFix f x = iterate (>>= f) x !! 10

calculateRecursionLimits' :: Term3 -> Either CompileError Term4
calculateRecursionLimits' t3@(Term3 termMap) =
  let testMapBuilder :: StateT (Map BreakExtras RecursionTest) (Reader (Map BreakExtras Int)) PoisonType
      testMapBuilder = fragToPoison (termMap Map.!) buildingSetEval AnyTypeN (rootFrag termMap)
      step1 :: Reader (Map BreakExtras Int) (Map BreakExtras RecursionTest)
      step1 = State.execStateT testMapBuilder mempty
      findLimit :: BreakExtras -> RecursionTest -> Either BreakExtras Int
      findLimit churchSizingIndex tests =
        let unhandleableOther =
              let (lMap, kTests, gMap) = Map.splitLookup churchSizingIndex . unBetterMap . contaminationMap $ runReader tests 1
                  otherMap = lMap <> gMap
              in Set.lookupMin $ Map.keysSet otherMap
        in case unhandleableOther of
          Just o -> Left o
          _ -> let abortsAt i = let tests' = (Map.! churchSizingIndex) . unBetterMap . contaminationMap $ runReader tests i
                                    runTest (frag, inp) = null $ fragToPoison (termMap Map.!) abortingSetEval inp frag
                                in or $ fmap runTest tests'
                   (ib, ie) = if not (abortsAt 255) then (0, 255) else error "findchurchsize TODO" -- (256, maxBound)
                   findC b e | b > e = b
                   findC b e = let midpoint = div (b + e) 2
                               in trace ("midpoint is now " <> show midpoint) $ if abortsAt midpoint then findC (midpoint + 1) e else findC b (midpoint - 1)
               in pure $ findC ib ie
      mapLimits :: Map BreakExtras RecursionTest -> Either BreakExtras (Map BreakExtras Int)
      mapLimits = sequence . Map.mapWithKey findLimit
      unwrappedReader :: Map BreakExtras Int -> Map BreakExtras RecursionTest
      unwrappedReader = runReader step1
      fixable :: Map BreakExtras Int -> Either BreakExtras (Map BreakExtras Int)
      fixable = mapLimits . unwrappedReader
  -- in case mfix fixable of
  in case limitedMFix fixable (Right mempty) of
    Left be -> Left $ RecursionLimitError be
    Right limits -> trace "found limits!" . pure $ convertPT (limits Map.!) t3
  {-
      fixable :: Either BreakExtras (Map BreakExtras Int) -> Either BreakExtras (Map BreakExtras Int)
      fixable =  join . fmap (trace "searching..." . mapLimits . trace "uhh1" . unwrappedReader . trace "uhh2")
  in trace "unforgiveable" $ case fix fixable of
    Left be -> Left $ RecursionLimitError be
    Right limits -> pure $ convertPT (limits Map.!) t3
-}

findChurchSize :: Term3 -> Either CompileError Term4
{-
findChurchSize term =
  let abortsAt i = (\(PResult (_, b)) -> b) . fix pEval PZero . fromSIL $ convertPT i term
      -- evaluating large church numbers is currently impractical, just fail if found
      (ib, ie) = if not (abortsAt 255) then (0, 255) else error "findchurchsize TODO" -- (256, maxBound)
      findC b e | b > e = b
      findC b e = let midpoint = (\n -> trace ("midpoint is now " <> show n) n) $ div (b + e) 2
                  in if abortsAt midpoint then findC (midpoint + 1) e else findC b midpoint
  in convertPT (findC ib ie) term
-}
findChurchSize = calculateRecursionLimits' -- convertPT (const 255)
-- findChurchSize = pure . convertPT (const 255)

{-
findAllSizes :: Term2 -> (Bool, Term3)
findAllSizes = let doChild (True, x) = TTransformedGrammar $ findChurchSize x
                   doChild (_, x) = TTransformedGrammar $ convertPT 0 x
                   doChildren l = let nl = map findAllSizes l
                                  in case sum (map (fromEnum . fst) nl) of
                                       0 -> (False, map snd nl)
                                       1 -> (True, map snd nl)
                                       _ -> (False, map doChild nl)
               in \case
  TZero -> (False, TZero)
  TPair a b -> let (c, [na, nb]) = doChildren [a,b] in (c, TPair na nb)
  TVar n -> (False, TVar n)
  TApp a b -> let (c, [na, nb]) = doChildren [a,b] in (c, TApp na nb)
  TCheck a b -> let (c, [na, nb]) = doChildren [a,b] in (c, TCheck na nb)
  TITE i t e -> let (c, [ni, nt, ne]) = doChildren [i,t,e] in (c, TITE ni nt ne)
  TLeft x -> TLeft <$> findAllSizes x
  TRight x -> TRight <$> findAllSizes x
  TTrace x -> TTrace <$> findAllSizes x
  TLam lt x -> TLam lt <$> findAllSizes x
  TLimitedRecursion -> (True, TLimitedRecursion)
-}

resolveBinding :: String -> Bindings -> Either CompileError IExpr
resolveBinding name bindings = convert (Map.lookup name bindings) where
  wrapUp = \case
    Just r -> case r of
      Right d -> case toSIL d of
        Just c -> pure c
        _ -> Left IRConversionError
      Left e -> Left e
    _ -> Left $ MissingDefiniton "unknown from resolveBinding"
  convert = wrapUp . fmap (findChurchSize . splitExpr) . (>>= debruijinize [])

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case eval' iexpr of
  Left err -> putStrLn . concat $ ["Failed compiling main, ", show err]
  Right peExp ->
    let mainLoop s = do
             result <- optimizedEval (app peExp s)
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
