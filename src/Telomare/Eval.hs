{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.Eval where

import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import Control.Lens.Plated
import Control.Monad.Except
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State (StateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Accum (AccumT)
import qualified Control.Monad.Trans.Accum as Accum
import Data.DList (DList)
import Data.Functor.Foldable (cata, embed, project)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import System.IO
import System.Process

import PrettyPrint
import Telomare (BreakState, BreakState', ExprA (..), FragExpr (..),
                 FragExprF (..), FragIndex (FragIndex), IExpr (..), LocTag (..),
                 PartialType (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..), RunResult, RunTimeError (..),
                 TelomareLike (..), Term3 (Term3), Term4 (Term4),
                 UnsizedRecursionToken (..), app, appF, eval, convertAbortMessage, deferF, forget, g2s,
                 innerChurchF, insertAndGetKey, pairF, pattern AbortAny, pattern AbortRecursion,
                 pattern AbortUser, rootFrag, s2g, setEnvF, tag, unFragExprUR)
import Telomare.Optimizer (optimize)
import Telomare.Parser (AnnotatedUPT, UnprocessedParsedTerm (..), parsePrelude)
import Telomare.Possible (AbortExpr, VoidF, abortExprToTerm4, evalA, sizeTerm,
                          term3ToUnsizedExpr)
import Telomare.Resolver (parseMain)
import Telomare.RunTime (hvmEval, optimizedEval, pureEval, simpleEval)
import Telomare.TypeChecker (TypeCheckError (..), typeCheck)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

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
    | RecursionLimitError UnsizedRecursionToken
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
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= pureEval . optimize)
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

convertPT :: (UnsizedRecursionToken -> Int) -> Term3 -> Term4
convertPT ll (Term3 termMap) =
  let unURedMap = Map.map unFragExprUR termMap
      startKey = succ . fst $ Map.findMax termMap
      changeFrag :: Cofree (FragExprF RecursionPieceFrag) LocTag
                 -> State.State
                      ((), FragIndex,
                       Map
                         FragIndex
                         (Cofree (FragExprF RecursionPieceFrag) LocTag))
                      (Cofree (FragExprF RecursionPieceFrag) LocTag)
      changeFrag = \case
        anno :< AuxFragF (NestedSetEnvs n) -> innerChurchF anno $ ll n
        _ :< AuxFragF (SizingWrapper _ x) -> transformM changeFrag $ unFragExprUR x
        _ :< AuxFragF (CheckingWrapper anno tc c) ->
          let performTC = deferF ((\ia -> setEnvF (pairF (setEnvF (pairF (pure $ tag anno AbortFrag) ia))
                                                        (pure . tag anno $ RightFrag EnvFrag))) $ appF (pure . tag anno $ LeftFrag EnvFrag)
                                                                                                       (pure . tag anno $ RightFrag EnvFrag))
          in setEnvF (pairF performTC (pairF (transformM changeFrag $ unFragExprUR tc) (transformM changeFrag $ unFragExprUR c)))
        x -> pure x
      insertChanged :: FragIndex
                    -> Cofree (FragExprF RecursionPieceFrag) LocTag
                    -> BreakState RecursionPieceFrag () ()
      insertChanged nk nv = State.modify (\(_, k, m) -> ((), k, Map.insert nk nv m))
      builder = sequence $ Map.mapWithKey (\k v -> transformM changeFrag v >>= insertChanged k) unURedMap
      (_,_,newMap) = State.execState builder ((), startKey, unURedMap)
      changeType :: FragExprF a x -> FragExprF b x
      changeType = \case
        ZeroFragF      -> ZeroFragF
        PairFragF a b  -> PairFragF a b
        EnvFragF       -> EnvFragF
        SetEnvFragF x  -> SetEnvFragF x
        DeferFragF ind -> DeferFragF ind
        AbortFragF     -> AbortFragF
        GateFragF l r  -> GateFragF l r
        LeftFragF x    -> LeftFragF x
        RightFragF x   -> RightFragF x
        TraceFragF     -> TraceFragF
        AuxFragF z     -> error "convertPT should be no AuxFrags here TODO"
  in Term4 $ fmap (hoistCofree changeType) newMap

findChurchSize :: Term3 -> Either EvalError Term4
-- findChurchSize = pure . convertPT (const 255)
findChurchSize = calculateRecursionLimits -- works fine for unit tests, but uses too much memory for tictactoe

-- we should probably redo the types so that this is also a type conversion
removeChecks :: Term4 -> Term4
removeChecks (Term4 m) =
  let f = \case
        anno :< AbortFragF -> anno :< DeferFragF ind
        x                  -> x
      (ind, newM) = State.runState builder m
      builder = do
        envDefer <- insertAndGetKey $ DummyLoc :< EnvFragF
        insertAndGetKey $ DummyLoc :< DeferFragF envDefer
  in Term4 $ Map.map (transform f) newM

runStaticChecks :: Term4 -> Either EvalError Term4
runStaticChecks t@(Term4 termMap) =
  let result = evalA combine (Just Zero) t
      combine a b = case (a,b) of
        (Nothing, _) -> Nothing
        (_, Nothing) -> Nothing
        (a, _)       -> a
  in case debugTrace ("running static checks for:\n" <> prettyPrint t) result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: Term3 -> Either EvalError IExpr
compileMain term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compile pure term -- TODO add runStaticChecks back in

compileUnitTest :: Term3 -> Either EvalError IExpr
compileUnitTest = compile runStaticChecks

compile :: (Term4 -> Either EvalError Term4) -> Term3 -> Either EvalError IExpr
compile staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t)
  $ case toTelomare . removeChecks <$> (findChurchSize t >>= staticCheck) of
      Right (Just i) -> pure i
      Right Nothing  -> Left CompileConversionError
      Left e         -> Left e

runMain :: String -> String -> IO ()
runMain preludeString s =
  let prelude :: [(String, AnnotatedUPT)]
      prelude =
        case parsePrelude preludeString of
          Right p -> p
          Left pe -> error pe
  in
    case compileMain <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop g
      Right z -> putStrLn $ "compilation failed somehow, with result " <> show z

schemeEval :: IExpr -> IO ()
schemeEval iexpr = do
  writeFile "scheme.txt" ('(' : (show (app iexpr Zero) <> ")"))
  (_, Just mhout, _, _) <- createProcess (shell "chez-script runtime.so") { std_out = CreatePipe }
  scheme <- hGetContents mhout
  putStrLn scheme

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap' :: (IExpr -> IExpr) -> IExpr -> Maybe (String, IExpr) -> (String, Maybe IExpr)
funWrap' eval fun inp =
  let iexpInp = case inp of
        Nothing -> Zero
        Just (userInp, oldState) -> Pair (s2g userInp) oldState
  in case eval (app fun iexpInp) of
    Zero -> ("aborted", Nothing)
    Pair disp newState -> (g2s disp, Just newState)
    z -> ("runtime error, dumped:\n" <> show z, Nothing)

funWrap :: (IExpr -> RunResult IExpr) -> IExpr -> Maybe (String, IExpr) -> IO (String, Maybe IExpr)
funWrap eval fun inp =
  let iexpInp = case inp of
        Nothing -> Zero
        Just (userInp, oldState) -> Pair (s2g userInp) oldState
  in runExceptT (eval (app fun iexpInp)) >>= \case
    Right Zero -> pure ("aborted", Nothing)
    Right (Pair disp newState) -> pure (g2s disp, Just newState)
    z -> pure ("runtime error, dumped:\n" <> show z, Nothing)

evalLoop :: IExpr -> IO ()
evalLoop iexpr =
  let wrappedEval = funWrap eval iexpr
      mainLoop s = do
        (out, nextState) <- wrappedEval s
        putStrLn out
        case nextState of
          Nothing -> pure ()
          Just ns -> do
            inp <- getLine
            mainLoop $ pure (inp, ns)
  in mainLoop Nothing

-- |Same as `evalLoop`, but keeping what was displayed.
-- TODO: make evalLoop and evalLoop always share eval method (i.e. simpleEval, hvmEval)
evalLoop_ :: IExpr -> IO String
evalLoop_ iexpr =
  let mainLoop prev s = do
        -- result <- optimizedEval (app peExp s)
        result <- simpleEval (app iexpr s)
        --result <- simpleEval $ traceShowId $ app peExp s
        case result of
          Zero -> pure $ prev <> "\n" <> "aborted"
          (Pair disp newState) -> do
            let d = g2s disp
            case newState of
              Zero -> pure $ prev <> "\n" <> d <> "\ndone"
              _ -> do
                inp <- s2g <$> getLine
                mainLoop (prev <> "\n" <> d) $ Pair inp newState
          r -> pure ("runtime error, dumped " <> show r)
  in mainLoop "" Zero

calculateRecursionLimits :: Term3 -> Either EvalError Term4
calculateRecursionLimits t3 =
  let abortExprToTerm4' :: AbortExpr -> Either IExpr Term4
      abortExprToTerm4' = abortExprToTerm4
      limitSize = 256
  in case fmap abortExprToTerm4' . sizeTerm limitSize $ term3ToUnsizedExpr limitSize t3 of
    Left urt -> Left $ RecursionLimitError urt
    Right t  -> case t of
      Left a  -> Left . StaticCheckError . convertAbortMessage $ a
      Right t -> pure t
