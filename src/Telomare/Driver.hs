{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# LANGUAGE TupleSections       #-}

module Telomare.Driver where

import Control.Comonad.Cofree (Cofree)
import Control.Monad (void, (>=>))
import qualified Control.Monad.State as State
import Crypto.Hash (Digest, SHA256)
import Data.Bifunctor (first)
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Lens (Identity (runIdentity))
import Data.Functor.Foldable (cata, embed)
import Debug.Trace
import Telomare.Desugar (desugarTerm)
import Telomare.EAL (CodeGuidance (..), EALResult, certifyMain, ealGuidance,
                     ealLiftedMain, inferEALCompiled)
import Telomare.Error
import Telomare.Eval.IC (ICMeter, ICPlan (..), evalIC, renderRefusal)
import Telomare.Eval.Meter (Meter, evalMeter)
import Telomare.Eval.Reference ()
import Telomare.Expand (expandDefs, expandModule, expandTerm,
                        renderExpansionError, wrapMain)
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Machine (appB, deferB)
import Telomare.Parse (parseOneExprOrDefinitions, runParseModule)
import Telomare.PrettyPrint
import Telomare.Resolve (main2Term3, main2Term3let, process, resolveAllImports)
import Telomare.Size (SizingReport (..), SizingSettings (..),
                      buildUnsizedLocMap, evalStaticCheck, locateSizingFailure,
                      sizeTermM, term3ToUnsizedExpr)
import Text.Megaparsec (errorBundlePretty, runParser)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- note that function indexes may be changed in this process
convertPT :: (UnsizedRecursionToken -> Int) -> Term3 -> CompiledExpr
convertPT ll = forget . flip State.evalState (toEnum 0, toEnum 0) . cata (f (convertBasic (convertAbort failConvert))) where
  failConvert = error "convertPT failed"
  appTC :: Term3Builder (Cofree CompiledExprF LocTag)
  appTC = appS (pure $ LeftB EnvB) (pure $ RightB EnvB)
  f convertOther (_ CofreeT.:< g)= case g of
    StuckFW (DeferSF _ x) -> x >>= deferS
    Term3Unsized urt -> pure $ iterate SetEnvB EnvB !! ll urt
    Term3CheckingWrapper _ tc c ->
      let performTC = (>>= deferS) ((\ia -> SetEnvB (PairB (SetEnvB (PairB (AbortEE AbortF) ia))
                                                     (RightB EnvB))) <$> appTC)
      in (\tc' c' ptc -> SetEnvB (PairB ptc (PairB  tc' c'))) <$> tc <*> c <*> performTC
    x -> convertOther x

data SizingOption
  = NoSizing -- deprecated
  | UnitTestSizing
  | MainSizing
  | DebugSizing SizingSettings

sizingBudget :: SizingOption -> Int
sizingBudget = \case
  NoSizing       -> reallyBigNum
  UnitTestSizing -> reallyBigNum
  MainSizing     -> reallyBigNum
  DebugSizing ss -> maxSizingSize ss

reallyBigNum :: Int
reallyBigNum = 65536

findChurchSizeD :: SizingOption -> Term3 -> Either EvalError CompiledExpr
findChurchSizeD so = fmap snd . findChurchSizeReporting so

findChurchSizeReporting :: SizingOption -> Term3 -> Either EvalError (SizingReport, CompiledExpr)
findChurchSizeReporting so t3 = case so of
  NoSizing       -> pure (report mempty, convertPT (const reallyBigNum) t3)
  UnitTestSizing -> sized (SizingSettings reallyBigNum False)
  MainSizing     -> sized (SizingSettings reallyBigNum True)
  DebugSizing ss -> sized ss
  where
    locs = buildUnsizedLocMap t3
    report counts = SizingReport counts locs (sizingBudget so)
    sized settings = case sizeTermM settings $ term3ToUnsizedExpr t3 of
      Left failure      -> Left . RecursionLimitError $ locateSizingFailure locs failure
      Right (counts, t) -> pure (report counts, t)

runStaticChecks :: CompiledExpr -> Either EvalError CompiledExpr
runStaticChecks t =
  let result = evalStaticCheck False scTerm
      scTerm = runIdentity $ cata (convertBasic (convertStuck (convertAbort (\_ -> error "error converting for runStaticChecks")))) t
  in case debugTrace ("running static checks for:\n" <> prettyPrint t) result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: ExpandedModules -> String -> Either EvalError CompiledExpr
compileMain modules term = cpExpr <$> compileMainReporting MainSizing modules term

-- |The compilation product: the sized program together with everything
-- compilation proved about it. The EAL fields come from one post-sizing
-- inference over the code that will actually run — distinct from the
-- pre-sizing 'certifyMain' gate, whose verdict is about the recursion
-- scaffolding as well. They are lazy, so a run on the reference evaluator
-- never pays for them; writing an artifact or admitting the IC runtime
-- forces them once, and from then on they travel with the program.
data CompiledProgram = CompiledProgram
  { cpSizing   :: SizingReport
    -- ^ What sizing found, so reporting it never needs a second sizing run.
  , cpExpr     :: CompiledExpr
    -- ^ The sized program.
  , cpGuidance :: Map (Digest SHA256) CodeGuidance
    -- ^ Per-hash guidance for every body (all of them, when the program certified),
    -- post-sizing — the map runtime strategies draw on.
  , cpVerdict  :: Either String EALResult
    -- ^ The post-sizing whole-program verdict. The reference evaluator
    -- ignores it; IC admission ('programPlan') is exactly this field.
    -- A refusal is carried rendered: it is for showing, and keeping it
    -- structured would mean serializing blame chains into artifacts.
  }

-- |Package a sized program with its post-sizing EAL product.
certifiedProgram :: SizingReport -> CompiledExpr -> CompiledProgram
certifiedProgram report sized = CompiledProgram
  { cpSizing = report
  , cpExpr = sized
  , cpGuidance = Map.fromList
      [ (h, g) | (h, Right g) <- Map.toList (ealGuidance lr) ]
  , cpVerdict = first (const (renderRefusal lr)) (ealLiftedMain lr)
  }
  where lr = inferEALCompiled sized

-- |IC admission, read off the carried verdict: the plan when the program
-- certified post-sizing, the rendered refusal when it did not. Unlike
-- `Telomare.Eval.IC.admitIC` this runs no inference — compilation already
-- did — so admitting an artifact is a field access.
programPlan :: CompiledProgram -> Either String ICPlan
programPlan cp = case cpVerdict cp of
  Left refusal -> Left refusal
  Right _      -> Right . ICPlan $
    Map.mapMaybe cgCaptureLayout (cpGuidance cp)

-- |`compileMain`, keeping everything the compile proved. Sizing costs
-- minutes on Prelude-heavy programs and the post-sizing EAL inference is
-- the IC runtime's admission certificate, so anything that wants either
-- must come by them through here rather than derive them again.
compileMainReporting :: SizingOption
                     -> ExpandedModules
                     -> String
                     -> Either EvalError CompiledProgram
compileMainReporting so modules term = do
  certTerm <- first RE $ main2Term3 modules term
  _ <- first CertificationError $ certifyMain certTerm
  (report, sized) <- first RE (main2Term3let modules term)
    >>= compileReporting so pure
  pure $ certifiedProgram report sized

-- for testing
compileMain' :: SizingSettings -> Term3 -> Either EvalError CompiledExpr
compileMain' ss = compile (DebugSizing ss) pure

compileUnitTest :: Term3 -> Either EvalError CompiledExpr
compileUnitTest = compile UnitTestSizing runStaticChecks

-- TODO kind of a hack, really CompiledExpr should be the basis for TelomareLike
compileUnitTestNoAbort :: Term3 -> Either EvalError CompiledExpr
compileUnitTestNoAbort = fmap (cata f) . compileUnitTest where
  f = \case
    AbortFW _ -> deferB (toEnum (-9)) EnvB
    x -> embed x

compile :: SizingOption -> (CompiledExpr -> Either EvalError CompiledExpr) -> Term3 -> Either EvalError CompiledExpr
compile so staticCheck t = snd <$> compileReporting so staticCheck t

compileReporting :: SizingOption
                 -> (CompiledExpr -> Either EvalError CompiledExpr)
                 -> Term3
                 -> Either EvalError (SizingReport, CompiledExpr)
compileReporting so staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t) $ do
  (report, sized) <- findChurchSizeReporting so t
  checked <- staticCheck sized
  pure (report, checked)

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap :: forall a. (Show a, AbstractRunTime a) => a -> (a -> a -> a) -> Maybe (String, BasicExpr) -> (String, Either RunTimeError BasicExpr)
funWrap fun app inp = snd $ funWrapWith (\x -> ((), eval x)) fun app inp

-- |`funWrap` over an evaluator that also reports something about the run, so
-- the metered and plain loops share one conversion path.
funWrapWith :: forall a m. (Show a, TelomareLike a, Monoid m)
            => (a -> (m, Either RunTimeError a))
            -> a -> (a -> a -> a) -> Maybe (String, BasicExpr)
            -> (m, (String, Either RunTimeError BasicExpr))
funWrapWith evaluator fun app inp =
  let iexpInp = conv $ case inp of
        Nothing                  -> ZeroB
        Just (userInp, oldState) -> PairB (s2b userInp) oldState
      conv = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error"))
      conv2 = runIdentity . cata (convertBasic (convertStuck (\_ -> error "funWrap conversion error2")))
      conv3 = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error3"))
      (measured, outcome) = evaluator (app fun $ fromTelomare iexpInp)
  in (,) measured $ case outcome of
    Right x -> case toTelomare x of
      Nothing -> ("error converting iteration value:\n" <> show x, Left $ AbortRunTime ZeroB)
      Just ZeroB -> ("aborted", Left $ AbortRunTime ZeroB)
      -- Just (PairB disp newState) -> (b2s disp, pure $ fromTelomare newState)
      Just (PairB disp newState) -> case b2s disp of
        Just d -> (d, pure $ conv3 newState)
        _ -> ("error converting display value:\n" <> prettyPrint disp, Left . GenericRunTimeError "" $ conv2 disp)
      Just _ -> error "Telomare.Driver.funWrapWith: unexpected iteration value"
    Left e -> ("runtime error:\n" <> show e, Left e)

-- |Parse and compile a module set into the full compilation product. Every
-- problem comes back as text a user can act on rather than as an exception,
-- so callers decide how to report it.
--
-- Each module is parsed under its own name, so the locations in diagnostics
-- can say which file a term came from.
compileModules :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
               -> String -- ^Module's name with `main` function
               -> Either String CompiledProgram
compileModules = compileModulesWith MainSizing

-- |`compileModules` at a chosen sizing budget. Tests use a deliberately tiny
-- budget to reach the budget-exhaustion path without waiting for 65536
-- abstract unrollings.
compileModulesWith :: SizingOption
                   -> [(String, String)]
                   -> String
                   -> Either String CompiledProgram
compileModulesWith so modulesStrings s =
  case [ "Error in module " <> moduleName <> ":\n" <> err
       | (moduleName, Left err) <- parsed ] of
    [] -> first renderEvalError $ compileMainReporting so [ (n, m) | (n, Right m) <- parsed ] s
    errs -> Left $ unlines errs
  where
    parsed :: [(String, Either String ExpandedModule)]
    parsed = fmap parseAndExpand modulesStrings
    parseAndExpand (moduleName, content) =
      ( moduleName
      , runParseModule moduleName content
          >>= first renderExpansionError . expandModule )

runMainCore :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
            -> String -- ^Module's name with `main` function
            -> (CompiledExpr -> IO a)
            -> IO a
runMainCore modulesStrings s e = case compileModules modulesStrings s of
  -- Still an exception, since callers depend on that; the CLI takes the
  -- `compileModules` route instead so a user never sees this framing.
  Left err -> error $ "runMainCore failed: " <> err
  Right cp -> e (cpExpr cp)

runMain_ :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
         -> String -- ^Module's name with `main` function
         -> IO String
runMain_ modulesStrings s = runMainCore modulesStrings s evalLoop_

runMain :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
        -> String -- ^Module's name with `main` function
        -> IO ()
runMain modulesStrings s = runMainCore modulesStrings s evalLoop

runMainWithInput :: [String] -- ^Inputs
                 -> [(String, String)] -- ^All modules as (Module_Name, Module_Content)
                 -> String -- ^Module's name with `main` function
                 -> IO String
runMainWithInput inputList modulesStrings s = runMainCore modulesStrings s (evalLoopWithInput inputList)

-- |The one iteration loop every eval entry point goes through. The evaluator
-- reports a measurement per iteration (the unmetered wrappers use '()'), and
-- each iteration's display goes through @accumFn@; the loop returns the summed
-- measurements alongside the final accumulator.
evalLoopCore :: Monoid m
             => (CompiledExpr -> (m, Either RunTimeError CompiledExpr))
             -> CompiledExpr
             -> (String -> String -> IO String)
             -> String
             -> [String]
             -> IO (m, String)
evalLoopCore evaluator expr accumFn initAcc manualInput =
  let wrappedEval = funWrapWith evaluator expr appB
      mainLoop measured acc strInput s = do
        let (m, (out, nextState)) = wrappedEval s
            measured' = measured <> m
        newAcc <- accumFn acc out
        case nextState of
          Left e -> pure (measured', newAcc <> "\n" <> show e)
          Right ZeroB -> pure (measured', newAcc <> "\n" <> "done")
          Right ns -> do
            (inp, rest) <- case strInput of
              []               -> (, []) <$> getLine
              next : remaining -> pure (next, remaining)
            mainLoop measured' newAcc rest $ pure (inp, ns)
  in mainLoop mempty initAcc manualInput Nothing

-- |The evaluator the unmetered wrappers share: run and measure nothing.
plainEval :: CompiledExpr -> ((), Either RunTimeError CompiledExpr)
plainEval = ((),) . eval

-- |Print each iteration's display and keep nothing.
printAccum :: String -> String -> IO String
printAccum _ out = putStrLn out >> pure ""

-- |Keep each iteration's display, newline-separated.
keepAccum :: String -> String -> IO String
keepAccum acc out = pure $ if acc == "" then out else acc <> "\n" <> out

evalLoop :: CompiledExpr -> IO ()
evalLoop iexpr = void $ evalLoopCore plainEval iexpr printAccum "" []

evalLoopWithInput :: [String] -> CompiledExpr -> IO String
evalLoopWithInput inputList iexpr = snd <$> evalLoopCore plainEval iexpr keepAccum "" inputList

-- |`evalLoop`, measuring what the session costs. Prints exactly what
-- `evalLoop` prints; the caller decides what to do with the measurement.
evalLoopMetered :: [String] -> CompiledExpr -> IO Meter
evalLoopMetered manualInput expr = fst <$> evalLoopCore evalMeter expr printAccum "" manualInput

-- |`evalLoop` on the interaction-combinator runtime, measuring what the
-- session cost in interactions. The caller comes by the plan through
-- `Telomare.Eval.IC.admitIC`, so the certificate is computed once per
-- program rather than once per iteration.
evalLoopIC :: [String] -> ICPlan -> CompiledExpr -> IO ICMeter
evalLoopIC manualInput plan expr =
  fst <$> evalLoopCore (evalIC plan) expr printAccum "" manualInput

-- |Same as `evalLoop`, but keeping what was displayed.
evalLoop_ :: CompiledExpr -> IO String
evalLoop_ iexpr = snd <$> evalLoopCore plainEval iexpr keepAccum "" []

eval2IExpr :: ExpandedModules -> String -> Either String CompiledExpr
eval2IExpr extraModuleBindings str = do
  resolved <- first show $ resolveAllImports extraModuleBindings aux
  first errorBundlePretty (runParser parseOneExprOrDefinitions "" str)
    >>= first renderExpansionError
        . either (expandDefs >=> wrapMain resolved) expandTerm
    >>= first show . process . desugarTerm
    >>= tt . first show . compileUnitTest
    where
      tt = \case
        Left e -> Left $ show e
        Right x -> pure x
      aux = makeImport . fst <$> extraModuleBindings
      makeImport name =
        let loc = GeneratedLoc "eval2IExpr.import" Nothing
        in ExpandedModuleImport $ ImportDecl loc
             (locatedName loc name)
             (Just $ locatedName loc name)
