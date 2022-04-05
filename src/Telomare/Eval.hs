{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module Telomare.Eval where

import           Control.Lens.Plated
import           Control.Monad.Except
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Accum (AccumT)
import qualified Control.Monad.State  as State
import qualified Control.Monad.Trans.Accum as Accum
import           Data.Functor.Foldable (embed, project, cata)
import Data.DList (DList)
import           Data.Map             (Map)
import qualified Data.Map             as Map
import Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void
import           Debug.Trace
import           Telomare
import           Telomare.Decompiler
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
    PairP a b   -> PairP <$> f a <*> f b
    SetEnvP x b -> SetEnvP <$> f x <*> pure b
    DeferP x    -> DeferP <$> f x
    GateP l r   -> GateP <$> f l <*> f r
    LeftP x     -> LeftP <$> f x
    RightP x    -> RightP <$> f x
    x           -> pure x

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

convertPT' :: (BreakExtras -> Int) -> (FragIndex -> FragExpr BreakExtras) -> FragExpr BreakExtras -> BreakState' BreakExtras b
convertPT' limitLookup fragLookup =

  let changeTerm = \case
        AuxFrag n -> innerChurchF $ limitLookup n
        DeferFrag fi -> do
          newFrag <- transformM changeTerm $ fragLookup fi
          State.modify (\(uri, fii, fragMap) -> (uri, fii, Map.insert fi newFrag fragMap))
          pure $ DeferFrag fi
        x -> pure x
  in transformM changeTerm

convertPT :: (BreakExtras -> Int) -> Term3 -> Term4
convertPT ll (Term3 termMap) = let builder = convertPT' ll (termMap Map.!) (rootFrag termMap)
                                   startKey = succ . fst $ Map.findMax termMap
                                   (_,_,newMap) = State.execState builder ((), startKey, termMap)
                                   changeType :: FragExpr BreakExtras -> FragExpr Void
                                   changeType = \case
                                     ZeroFrag -> ZeroFrag
                                     PairFrag a b -> PairFrag (changeType a) (changeType b)
                                     EnvFrag -> EnvFrag
                                     SetEnvFrag x -> SetEnvFrag (changeType x)
                                     DeferFrag ind -> DeferFrag ind
                                     AbortFrag -> AbortFrag
                                     GateFrag l r -> GateFrag (changeType l) (changeType r)
                                     LeftFrag x -> LeftFrag (changeType x)
                                     RightFrag x -> RightFrag (changeType x)
                                     TraceFrag -> TraceFrag
                                     AuxFrag _ -> error "convertPT should be no AuxFrags here"
                               in Term4 $ fmap changeType newMap

findChurchSize :: Term3 -> Either EvalError Term4
--findChurchSize = pure . convertPT (const 255)
findChurchSize = calculateRecursionLimits

-- we should probably redo the types so that this is also a type conversion
removeChecks :: Term4 -> Term4
removeChecks (Term4 m) =
  let f = \case
        AbortFrag -> DeferFrag ind
        x         -> x
      (ind, newM) = State.runState builder m
      builder = do
        envDefer <- insertAndGetKey EnvFrag
        insertAndGetKey $ DeferFrag envDefer
  in Term4 $ Map.map (transform f) newM

convertAbortMessage :: IExpr -> String
convertAbortMessage = \case
  AbortRecursion -> "recursion overflow (should be caught by other means)"
  AbortUser s -> "user abort: " <> g2s s
  AbortAny -> "user abort of all possible abort reasons (non-deterministic input)"
  x -> "unexpected abort: " <> show x

runStaticChecks :: Term4 -> Either EvalError Term4
runStaticChecks t@(Term4 termMap) =
  let result = evalA combine (Just Zero) t
      combine a b = case (a,b) of
        (Nothing, _) -> Nothing
        (_, Nothing) -> Nothing
        (a, _) -> a
  in case result of
    Nothing -> pure t
    Just e -> Left . StaticCheckError $ convertAbortMessage e

runStaticChecksMain :: Term4 -> Either EvalError Term4
runStaticChecksMain t@(Term4 termMap) =
  let (PairFrag (DeferFrag i) y) = rootFrag termMap
      result = evalA' combine (Just Zero) (termMap Map.!) (termMap Map.! i)
      combine a b = case (a,b) of
        (Nothing, _) -> Nothing
        (_, Nothing) -> Nothing
        (a, _) -> a
  in case result of
    Nothing -> pure t
    Just e -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: Term3 -> Either EvalError IExpr
compileMain term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compile runStaticChecks term -- TODO fix runStaticChecksMain

compileUnitTest :: Term3 -> Either EvalError IExpr
compileUnitTest = compile runStaticChecks

compile :: (Term4 -> Either EvalError Term4) -> Term3 -> Either EvalError IExpr
compile staticCheck t = case toTelomare . removeChecks <$> (findChurchSize t >>= staticCheck) of
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

calculateRecursionLimits :: Term3 -> Either EvalError Term4
calculateRecursionLimits t3@(Term3 termMap) =
  let abortsAt n = not . null . evalA combine Nothing $ convertPT (const n) t3
      combine a b = case (a,b) of
        (Just AbortRecursion, _) -> Just AbortRecursion
        (_, Just AbortRecursion) -> Just AbortRecursion
        _ -> Nothing
      iterations = take 10 $ iterate (\(_,n) -> (abortsAt (n * 2), n * 2)) (True, 1)
  in case lookup False iterations of
    Just n -> trace ("crl found limit at " <> show n) pure $ convertPT (const n) t3
    _ -> Left . RecursionLimitError $ toEnum 0
