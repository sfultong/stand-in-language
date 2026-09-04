{-# LANGUAGE LambdaCase #-}

-- |Running a program without sizing it first.
--
-- The compiler's usual route sizes every @{test, recursion, last}@ site — it
-- unrolls the recursion abstractly over a symbolic input until the test stops,
-- and bakes the resulting count in as a church tower
-- @iterate SetEnvB EnvB !! (n+1)@ (`Telomare.Eval.convertPT`). That is what
-- makes a telomare program total, and it is also what makes compiling one
-- cost minutes.
--
-- This module runs the same `Term3` with that pass skipped. Where sizing would
-- install an approximant chain, `term3ToFast` installs `FUnbounded`, and the
-- recursion ladder becomes a `VRec` value that unrolls one layer per
-- /demanded/ call.
-- Sizing only ever proved that a bound suffices — at runtime the base case
-- fires early, through the test's gate — so on every program the sizer accepts
-- this agrees with the sized run, and it additionally runs programs the sizer
-- rejects.
--
-- What it gives up is exactly what sizing is for: nothing here proves the
-- program terminates. A recursion that would not have sized runs until the
-- fuel cap stops it (`defaultFastFuel`). This is a way to run a program
-- quickly, never a claim that it is total — hence the flag, and hence sizing
-- staying the default.
--
-- == Two things that look like details and are not
--
-- __Lazy gate selection.__ Only the selected branch of the syntactic
-- if-then-else shape @SetEnv (Pair (Gate else then) scrutinee)@ is evaluated.
-- The sized evaluator gets this from Haskell: it maps over both branches but
-- discards the unselected thunk unforced. Here it has to be explicit, and it
-- is load-bearing — an unbounded ladder's "recurse" branch is still present at
-- the base case, and forcing it would unroll forever.
--
-- __Aborts are values.__ `VAborted` propagates through projections,
-- application heads and gate scrutinees, may sit inside a pair, and is
-- /discarded/ if the program never looks at it. Only an abort that survives
-- into the iteration's result ends the run (`findAbort`). Throwing at the
-- point an abort is created instead is wrong, and `simpleplus.tel` catches it:
-- its iteration builds one on the Zero input and never uses it.
module Telomare.Fast
  ( -- * The runtime IR
    FastExpr (..)
  , Value (..)
  , RecursionSite (..)
    -- * Measuring a run
  , FastMeter (..)
  , renderFastMeter
    -- * Running
  , FastError (..)
  , renderFastError
  , EvalM
  , runEval
  , defaultFastFuel
  , evalFast
  , forceValue
  , findAbort
  , runFastLoop
  , runFastWithInput
    -- * Compiling without sizing
  , compileFast
  , term3ToFast
  , ownerMap
  ) where

import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Monad ((<=<))
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, get, gets, modify', put, runState)
import Data.Bifunctor (first)
import Data.Functor.Foldable (cata, embed)
import Data.List (sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import System.IO (hFlush, isEOF, stdout)

import Telomare.Error
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Parse (runParseModule)
import Telomare.Resolve (main2Term3, main2Term3let)
import Telomare.TypeCheck (typeCheck)
import Telomare.Util (padRight, plural)

-- |A recursion site: the token the sizing pass would have sized, where it is
-- in the source, and the top-level definition it belongs to. The token keeps
-- sites distinct even when their generated locations coincide.
data RecursionSite = RecursionSite
  { rsToken :: !UnsizedRecursionToken
  , rsLoc   :: !LocTag
  , rsOwner :: !(Maybe String)
  }
  deriving (Eq, Ord, Show)

-- |The compiled core, with the node sizing would have replaced by a tower.
data FastExpr
  = FZero
  | FPair FastExpr FastExpr
  | FEnv
  | FSetEnv FastExpr
  | FDefer FastExpr
  | FGate
  | FLeft FastExpr
  | FRight FastExpr
  | FAbort
  | FUnbounded RecursionSite
  deriving (Eq, Show)

-- |Machine values. A closure is @VPair (VDefer code) env@, the calling
-- convention the resolver emits; `VRec` is the recursion ladder.
data Value
  = VZero
  | VPair Value Value
  | VDefer FastExpr
  | VGate
  | VAbort
  | VAborted BasicExpr
  -- ^An abort in flight: propagates, and may be discarded unused.
  | VRec RecursionSite Value
  -- ^@VRec site trb@ — the limit of the approximant chain @step^n(abort)@
  -- over the recursion's captured @(tWrap, (r, (b, 0)))@ triple.
  -- `forceValue` unrolls one layer into a step closure whose recur slot is
  -- the ladder itself.
  deriving (Eq, Show)

-- |What a fast run cost. Unlike the sized meter's step count, the unrolls here
-- are attributed per recursion site: before sizing, sites still have an
-- identity.
data FastMeter = FastMeter
  { fmApplies :: !Int
  -- ^Function applications.
  , fmGates   :: !Int
  -- ^Gate selections.
  , fmUnrolls :: !(Map RecursionSite Int)
  -- ^Recursion unrollings, per site.
  }
  deriving (Eq, Show)

instance Semigroup FastMeter where
  a <> b = FastMeter
    { fmApplies = fmApplies a + fmApplies b
    , fmGates = fmGates a + fmGates b
    , fmUnrolls = Map.unionWith (+) (fmUnrolls a) (fmUnrolls b)
    }

instance Monoid FastMeter where
  mempty = FastMeter 0 0 Map.empty

-- |What to print for a measured fast run: totals, then the sites that
-- iterated, hottest first.
--
-- An unroll count is a total over the whole run, not a depth: a recursion
-- entered ten times to a depth of five unrolled fifty times. So these are not
-- comparable with `--certificate`'s per-instantiation caps, and the closing
-- note says so — measuring 48 where the certificate says @<= 7@ is the
-- expected relationship between the two, not a violated bound.
renderFastMeter :: FastMeter -> String
renderFastMeter m = unlines $
  [ "function applications (measured): " <> commaInt (fmApplies m)
  , "gate selections (measured):       " <> commaInt (fmGates m)
  , "recursion unrolls (measured):     " <> commaInt totalUnrolls
      <> " across " <> show siteCount <> plural " site" siteCount
  ] <> siteTable
    <> [ ""
       , "Unrolls are totals over the run, not depths, so they are not the same"
       , "measurement as --certificate's per-instantiation iteration counts." ]
  where
    rows = sortOn rowSort
      [ (n, siteName site, renderSite site, fromMaybe "?" (rsOwner site))
      | (site, n) <- Map.toList (fmUnrolls m)
      ]
    rowSort (n, sid, _, _) = (negate n, sid)
    totalUnrolls = sum [n | (n, _, _, _) <- rows]
    siteCount = length rows
    width sel header = maximum (length header : [length (sel r) | r <- rows])
    sourceWidth = width (\(_, _, s, _) -> s) "source"
    ownerWidth = width (\(_, _, _, f) -> f) "function"
    siteName site = '#' : show (unUnsizedRecursionToken (rsToken site))
    siteTable
      | null rows = []
      | otherwise =
          [ ""
          , "  " <> padRight 5 "site" <> "  "
              <> padRight sourceWidth "source" <> "  "
              <> padRight ownerWidth "function" <> "  unrolls"
          ] <>
          [ "  " <> padRight 5 sid <> "  "
              <> padRight sourceWidth source <> "  "
              <> padRight ownerWidth owner <> "  " <> commaInt n
          | (n, sid, source, owner) <- rows
          ]

-- |A site's source position, falling back to whatever the tag does say.
renderSite :: RecursionSite -> String
renderSite site = case renderLocTagCompact (rsLoc site) of
  Just spot -> spot
  Nothing   -> describe (rsLoc site)
  where
    describe = \case
      SourceLoc spn -> fromMaybe "<source>" (sourceSpanFile spn)
        <> ":" <> show (sourcePositionLine (sourceSpanStart spn))
      GeneratedLoc label parent ->
        "generated " <> label <> maybe "" ((" from " <>) . describe) parent
      BuiltinLoc label -> "builtin " <> label
      RuntimeLoc -> "runtime"
      DecompiledLoc -> "decompiled"
      UnknownLoc -> "unknown"

commaInt :: Int -> String
commaInt n
  | n < 0 = '-' : commaInt (negate n)
  | otherwise = reverse . go (0 :: Int) . reverse $ show n
  where
    go _ []       = []
    go 3 xs       = ',' : go 0 xs
    go k (x : xs) = x : go (k + 1) xs

data FastError
  = FastStuck String
  -- ^An ill-formed application or projection: the term is not what the
  -- resolver is supposed to emit.
  | FastOutOfFuel Int
  -- ^The fuel cap stopped the run. Carries the cap that was in force.
  deriving (Eq, Show)

renderFastError :: FastError -> String
renderFastError = \case
  FastStuck why -> "runtime error (stuck): " <> why
  FastOutOfFuel cap -> "runtime error: out of fuel after " <> commaInt cap
    <> " applications and unrollings.\nThis run is not sized, so nothing"
    <> " proved it terminates. Raise the cap with --fuel N, or lift it"
    <> " entirely with --fuel 0."

-- |The default cap on applications plus unrollings, per iteration of `main`.
-- Sizing bounds each call of `main`, so this does too. A tictactoe move costs
-- well under a million, so a program that is really total never meets this;
-- one that is not stops in seconds instead of hanging.
defaultFastFuel :: Int
defaultFastFuel = 2 ^ (24 :: Int)

type EvalM = ExceptT FastError (State (FastMeter, Maybe Int))

-- |Run a metered evaluation. `Nothing` fuel means no cap.
runEval :: Maybe Int -> EvalM a -> (FastMeter, Either FastError a)
runEval fuel m =
  let (r, (meter, _)) = runState (runExceptT m) (mempty, fuel)
  in (meter, either (Left . nameCap) Right r)
  where
    -- Only the caller knows what the cap was; `spend` just knows it is spent.
    nameCap = \case
      FastOutOfFuel _ -> FastOutOfFuel (fromMaybe 0 fuel)
      e               -> e

spend :: EvalM ()
spend = gets snd >>= \case
  Nothing -> pure ()
  Just n
    | n <= 0 -> throwError (FastOutOfFuel 0)
    | otherwise -> get >>= \(m, _) -> put (m, Just (n - 1))

tickApply :: EvalM ()
tickApply = modify' (\(m, f) -> (m { fmApplies = fmApplies m + 1 }, f)) >> spend

tickGate :: EvalM ()
tickGate = modify' (\(m, f) -> (m { fmGates = fmGates m + 1 }, f))

tickUnroll :: RecursionSite -> EvalM ()
tickUnroll site =
  modify' (\(m, f) -> (m { fmUnrolls = Map.insertWith (+) site 1 (fmUnrolls m) }, f))
    >> spend

-- |Unroll a recursion ladder one layer; the identity on everything else.
forceValue :: Value -> EvalM Value
forceValue = \case
  VRec site trb -> do
    tickUnroll site
    pure $ VPair (VDefer approxBody) (VPair (VRec site trb) trb)
  v -> pure v

-- |Application through the twiddle calling convention, as the compiler
-- emits it.
app :: FastExpr -> FastExpr -> FastExpr
app c i = FSetEnv (FSetEnv (FPair twiddle (FPair i c)))
  where twiddle = FDefer (FPair (FLeft (FRight FEnv))
                                (FPair (FLeft FEnv) (FRight (FRight FEnv))))

-- |One approximant step: @\\recur i -> if tWrap i then r recur i else b i@,
-- executing with env @(i, (recur, (tWrap, (r, (b, 0)))))@. The conditional
-- uses the gate-switch shape `evalFast` fast-paths lazily, so the recur
-- ladder in the then branch only unrolls when the test passes.
approxBody :: FastExpr
approxBody = iteFast (app arg3 arg1)
                     (app (app arg4 arg2) arg1)
                     (app arg5 arg1)
  where
    arg1 = FLeft FEnv
    arg2 = FLeft (FRight FEnv)
    arg3 = FLeft (FRight (FRight FEnv))
    arg4 = FLeft (FRight (FRight (FRight FEnv)))
    arg5 = FLeft (FRight (FRight (FRight (FRight FEnv))))
    iteFast s t e = FSetEnv (FPair (FSetEnv (FPair FGate s)) (FPair e t))

-- |An abort's payload keeps its pair structure and nothing else.
truncateV :: Value -> BasicExpr
truncateV = \case
  VPair a b -> PairB (truncateV a) (truncateV b)
  _         -> ZeroB

-- |The leftmost abort anywhere in a result. `VDefer` holds code, not a value,
-- so there is nothing to look at inside one.
findAbort :: Value -> Maybe BasicExpr
findAbort = \case
  VAborted e -> Just e
  VPair a b  -> firstJust (findAbort a) (findAbort b)
  _          -> Nothing
  where
    firstJust (Just x) _ = Just x
    firstJust Nothing y  = y

-- |Evaluate an expression in an environment.
evalFast :: FastExpr -> Value -> EvalM Value
evalFast expr env = case expr of
  FZero -> pure VZero
  FEnv -> pure env
  FAbort -> pure VAbort
  FDefer d -> pure (VDefer d)
  FPair a b -> VPair <$> evalFast a env <*> evalFast b env
  FGate -> pure VGate
  FLeft x -> project x "left of something that is not a pair" $ \case
    VPair a _ -> Just a
    VZero     -> Just VZero
    _         -> Nothing
  FRight x -> project x "right of something that is not a pair" $ \case
    VPair _ b -> Just b
    VZero     -> Just VZero
    _         -> Nothing
  -- The if-then-else shape, kept lazy. See the module header. The branches
  -- sit in the argument pair of the outer application; evaluating that pair
  -- through the generic path would force both of them.
  FSetEnv (FPair (FSetEnv (FPair FGate s)) (FPair l r)) -> do
    sv <- evalFast s env >>= forceValue
    tickGate
    case sv of
      VZero          -> evalFast l env
      VPair _ _      -> evalFast r env
      a@(VAborted _) -> pure a
      _              -> throwError $ FastStuck "gate on a non-data scrutinee"
  FSetEnv x -> evalFast x env >>= forceValue >>= \case
    VPair f e      -> applyRaw f e
    a@(VAborted _) -> pure a
    _              -> throwError $ FastStuck "setenv of something that is not a pair"
  -- The sizing oracle's hole: its defer is applied to the recursion's
  -- captured triple, and the unbounded approximant ladder stands in for
  -- the sized chain.
  FUnbounded site -> case env of
    VPair trb _ -> pure $ VRec site trb
    _ -> throwError $ FastStuck
      "unexpected environment at a recursion site (encoding drift?)"
  where
    project x why pick = evalFast x env >>= forceValue >>= \case
      a@(VAborted _) -> pure a
      v -> case pick v of
        Just r  -> pure r
        Nothing -> throwError (FastStuck why)

-- |Application.
applyRaw :: Value -> Value -> EvalM Value
applyRaw fun arg = forceValue fun >>= \case
  VDefer d -> tickApply >> evalFast d arg
  a@(VAborted _) -> pure a
  -- A gate applied to its scrutinee yields the branch-selector function,
  -- which the next application feeds the branch pair.
  VGate -> tickGate >> forceValue arg >>= \case
    VZero          -> pure (VDefer (FLeft FEnv))
    VPair _ _      -> pure (VDefer (FRight FEnv))
    a@(VAborted _) -> pure a
    _              -> throwError $ FastStuck "gate applied to non-data"
  VAbort -> forceValue arg >>= \case
    -- `assert` on a passing value yields the identity function.
    VZero          -> pure (VDefer FEnv)
    p@(VPair _ _)  -> pure (VAborted (truncateV p))
    a@(VAborted _) -> pure a
    _              -> throwError $ FastStuck "abort applied to non-data"
  _ -> throwError $ FastStuck "application of something that is not a function"

-- |Apply the program's @main@ closure to one iteration's input.
applyClosure :: Value -> Value -> EvalM Value
applyClosure fun arg = case fun of
  VPair (VDefer d) cloEnv -> tickApply >> evalFast d (VPair arg cloEnv)
  _                       -> throwError $ FastStuck "main is not a closure"

-- Encodings over machine values, bridged through `s2b`/`b2s`.

b2v :: BasicExpr -> Value
b2v = cata $ \case
  ZeroSF     -> VZero
  PairSF a b -> VPair a b

v2b :: Value -> Maybe BasicExpr
v2b = \case
  VZero     -> Just ZeroB
  VPair a b -> PairB <$> v2b a <*> v2b b
  _         -> Nothing

s2v :: String -> Value
s2v = b2v . s2b

v2s :: Value -> Maybe String
v2s = b2s <=< v2b

-- |One iteration of the transcript protocol, framed exactly as
-- `Telomare.Eval.funWrap` frames it so that a fast transcript and a sized one
-- are the same bytes.
iterateMain :: Value -> Maybe (String, Value) -> EvalM (String, Either RunTimeError Value)
iterateMain mainClosure inp = do
  result <- applyClosure mainClosure inputValue
  pure $ case findAbort result of
    Just e -> ("runtime error:\n" <> show (AbortRunTime e), Left (AbortRunTime e))
    Nothing -> case result of
      VZero -> ("aborted", Left (AbortRunTime ZeroB))
      VPair disp newState -> case v2s disp of
        Just d  -> (d, Right newState)
        Nothing -> ("error converting display value", Left (AbortRunTime ZeroB))
      _ -> ("error converting iteration value", Left (AbortRunTime ZeroB))
  where
    inputValue = case inp of
      Nothing               -> VZero
      Just (line, oldState) -> VPair (s2v line) oldState

mainClosureOf :: FastExpr -> EvalM Value
mainClosureOf t = evalFast t VZero

-- |The interactive transcript loop, printing what `Telomare.Eval.evalLoop`
-- prints. Fuel is per iteration, so a long session cannot exhaust it.
--
-- Reaching end of input ends the loop instead of raising, which is the one
-- behavioural improvement kept from the branch this came from.
runFastLoop :: Maybe Int -> FastExpr -> IO FastMeter
runFastLoop fuel prog = go mempty Nothing
  where
    go measured inp = do
      let (m, r) = runEval fuel (mainClosureOf prog >>= \c -> iterateMain c inp)
          measured' = measured <> m
      case r of
        Left e -> do
          putStrLn (renderFastError e)
          pure measured'
        Right (out, nextState) -> do
          putStrLn out
          hFlush stdout
          case nextState of
            Left _     -> pure measured'
            Right VZero -> pure measured'
            Right ns -> isEOF >>= \case
              True -> pure measured'
              False -> do
                line <- getLine
                go measured' (Just (line, ns))

-- |The transcript for a fixed input list, accumulated exactly as
-- `Telomare.Eval.evalLoopWithInput` accumulates it — including the trailing
-- @done@ and the doubled error text — so the two can be compared directly.
runFastWithInput :: Maybe Int -> [String] -> FastExpr -> (FastMeter, Either FastError String)
runFastWithInput fuel inputs prog = runEval fuel $ do
  c <- mainClosureOf prog
  let go acc strInput inp = do
        (out, nextState) <- iterateMain c inp
        let acc' = if null acc then out else acc <> "\n" <> out
        case nextState of
          Left e -> pure $ acc' <> "\n" <> show e
          Right VZero -> pure $ acc' <> "\n" <> "done"
          Right ns -> case strInput of
            []       -> pure acc'
            l : rest -> go acc' rest (Just (l, ns))
  go "" inputs Nothing

-- |Parse, typecheck and resolve, then convert without sizing. This mirrors
-- `Telomare.Driver.compileMainReporting` up to the point where that calls the
-- sizing pass.
compileFast :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
            -> String -- ^Name of the module holding `main`
            -> Either String FastExpr
compileFast modulesStrings entry =
  case [ "Error in module " <> moduleName <> ":\n" <> err
       | (moduleName, Left err) <- parsed ] of
    errs@(_ : _) -> Left $ unlines errs
    [] -> do
      let modules = [(n, m) | (n, Right m) <- parsed]
          mainType = embed $ PairTypeP
            (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP))
            (embed AnyType)
      tcTerm <- resolved $ main2Term3 modules entry
      case typeCheck mainType tcTerm of
        Just e  -> Left . renderEvalError $ TCE e
        Nothing -> pure ()
      runtimeTerm <- resolved $ main2Term3let modules entry
      term3ToFast (ownerMap modules) runtimeTerm
  where
    parsed = fmap parseAndExpand modulesStrings
    parseAndExpand (n, content) =
      (n, runParseModule n content
            >>= first renderExpansionError . expandModule)
    resolved = either (Left . renderEvalError . RE) Right

-- |`Term3` to the runtime IR. There is no sizing here: `Term3Unsized` becomes
-- `FUnbounded`, and the refinement wrapper keeps its runtime shape so its
-- checks still run.
term3ToFast :: Map LocKey String -> Term3 -> Either String FastExpr
term3ToFast owners = cata go
  where
    go (anno CofreeT.:< t) = case t of
      Term3B ZeroSF -> Right FZero
      Term3B (PairSF a b) -> FPair <$> a <*> b
      Term3S EnvSF -> Right FEnv
      Term3S (SetEnvSF x) -> FSetEnv <$> x
      Term3S (DeferSF _ x) -> FDefer <$> x
      Term3S GateSF -> Right FGate
      Term3S (LeftSF x) -> FLeft <$> x
      Term3S (RightSF x) -> FRight <$> x
      Term3A AbortF -> Right FAbort
      Term3A (AbortedF _) -> Left "an already-aborted term in the source"
      Term3Unsized tok ->
        Right . FUnbounded $ RecursionSite tok anno (locKey anno >>= (`Map.lookup` owners))
      Term3CheckingWrapper _ tc c -> checkingWrapper <$> tc <*> c

    -- Run the check on the value: a nonzero result aborts carrying it as the
    -- message, and zero yields the identity, applied to the value.
    checkingWrapper tc c = FSetEnv (FPair performTC (FPair tc c))
      where
        performTC = FDefer
          (FSetEnv (FPair (FSetEnv (FPair FAbort innerTC)) (FRight FEnv)))
        innerTC = app (FLeft FEnv) (FRight FEnv)


-- |A source position, used to attribute a recursion site to the definition it
-- was written in.
type LocKey = (Maybe FilePath, Int)

-- |Which top-level definition each source position belongs to.
ownerMap :: ExpandedModules -> Map LocKey String
ownerMap parsed = Map.fromListWith keepFirst
  [ (key, moduleName <> "." <> defName)
  | (moduleName, entries) <- parsed
  , ExpandedModuleBinding name body <- entries
  , let defName = locatedNameText name
  , key <- positionsIn body
  ]
  where
    keepFirst _ old = old

positionsIn :: ExpandedSurfaceTerm -> [LocKey]
positionsIn (loc :< term) = maybe id (:) (locKey loc) (foldMap positionsIn term)

locKey :: LocTag -> Maybe LocKey
locKey = \case
  SourceLoc spn -> Just (sourceSpanFile spn, sourcePositionOffset (sourceSpanStart spn))
  GeneratedLoc _ parent -> parent >>= locKey
  _ -> Nothing
