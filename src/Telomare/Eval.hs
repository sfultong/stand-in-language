{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# LANGUAGE TupleSections       #-}

module Telomare.Eval where

import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import Control.Lens.Plated (Plated (..), transformM)
import Control.Monad (void)
import Control.Monad.State (State, evalState)
import qualified Control.Monad.State as State
import Data.Bifunctor (bimap, first, second)
import Data.Foldable (fold)
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isNothing)
import Data.Semigroup (Max (..), Min (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import System.IO
import System.Process

import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Lens (Identity (runIdentity))
import Data.Functor.Foldable (Base, cata, embed, para)
import PrettyPrint
import Telomare (AUPT, AbortableF (AbortF), AbstractRunTime, AnnotatedUPT (..),
                 BasicExpr, BasicExprF (..), CompiledExpr, CompiledExprF,
                 EvalError (..), LocTag (..), LocatedName (..),
                 PartialTypeF (..), Pattern, PatternA, ResolverError (..),
                 RunTimeError (..), StuckExpr, StuckF (..), TelomareLike (..),
                 Term2, Term3, Term3Builder, Term3F (..),
                 UnprocessedParsedTerm (..), UnprocessedParsedTermF (..),
                 UnsizedRecursionToken (..), appS, b2s, convertAbort,
                 convertAbortMessage, convertBasic, convertStuck, deferS,
                 embedB, embedS, eval, forget, insertAndGetKey,
                 locStartLineColumn, pattern AbortEE, pattern AbortFW,
                 pattern BasicEE, pattern BasicFW, pattern EnvB, pattern LeftB,
                 pattern PairB, pattern PairP, pattern RightB, pattern SetEnvB,
                 pattern StuckEE, pattern StuckFW, pattern ZeroB, s2b, tag)
import Telomare.Parser (parseModule, parseOneExprOrTopLevelDefs, parsePrelude)
import Telomare.Possible (SizingSettings (SizingSettings), appB, basicEval,
                          deferB, evalStaticCheck, getSizesM, sizeTermM,
                          term3ToUnsizedExpr)
import Telomare.PossibleData (SizedRecursion (..), VoidF)
import Telomare.Resolver (main2Term3, main2Term3let, process, resolveAllImports)
import Telomare.TypeChecker (typeCheck)
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

findChurchSizeD :: SizingOption -> Term3 -> Either EvalError CompiledExpr
findChurchSizeD so t3 = let reallyBigNum = 65536 in case so of
  NoSizing       -> pure (convertPT (const reallyBigNum) t3)
  UnitTestSizing -> calculateRecursionLimits (SizingSettings reallyBigNum False) t3
  MainSizing     -> calculateRecursionLimits (SizingSettings reallyBigNum True) t3
  DebugSizing ss -> calculateRecursionLimits ss t3

-- rather than remove checks, we should extract them so that they can be run separately, if that gives a performance benefit
{-
removeChecks :: Term4 -> Term4
removeChecks (Term4 m) =
  let f = \case
        anno :< AbortFragF -> anno :< DeferFragF ind
        x                  -> x
      (ind, newM) = State.runState builder m
      builder = do
        envDefer <- insertAndGetKey $ GeneratedLoc "removeChecks" Nothing :< EnvFragF
        insertAndGetKey $ GeneratedLoc "removeChecks" Nothing :< DeferFragF envDefer
  in Term4 $ Map.map (transform f) newM
-}
removeChecks :: CompiledExpr -> CompiledExpr
removeChecks = id

runStaticChecks :: CompiledExpr -> Either EvalError CompiledExpr
runStaticChecks t =
  let result = evalStaticCheck False scTerm
      scTerm = runIdentity $ cata (convertBasic (convertStuck (convertAbort (\_ -> error "error converting for runStaticChecks")))) t
  in case debugTrace ("running static checks for:\n" <> prettyPrint t) result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> String -> Either EvalError CompiledExpr
compileMain modules term = do
  let modules' = second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) <$> modules
      mainType = embed $ PairTypeP (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) (embed AnyType)
  tcTerm <- first RE $ main2Term3 modules' term
  case typeCheck mainType tcTerm of
    Just e -> Left $ TCE e
    _      -> first RE (main2Term3let modules' term) >>= compile MainSizing pure

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
compile so staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t)
  $ removeChecks <$> (findChurchSizeD so t >>= staticCheck)

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap :: forall a. (Show a, AbstractRunTime a) => a -> (a -> a -> a) -> Maybe (String, BasicExpr) -> (String, Either RunTimeError BasicExpr)
funWrap fun app inp =
  let iexpInp = conv $ case inp of
        Nothing                  -> ZeroB
        Just (userInp, oldState) -> PairB (s2b userInp) oldState
      conv = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error"))
      conv2 = runIdentity . cata (convertBasic (convertStuck (\_ -> error "funWrap conversion error2")))
      conv3 = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error3"))
  in case eval (app fun $ fromTelomare iexpInp) of
    Right x -> case toTelomare x of
      Nothing -> ("error converting iteration value:\n" <> show x, Left $ AbortRunTime ZeroB)
      Just ZeroB -> ("aborted", Left $ AbortRunTime ZeroB)
      -- Just (PairB disp newState) -> (b2s disp, pure $ fromTelomare newState)
      Just (PairB disp newState) -> case b2s disp of
        Just d -> (d, pure $ conv3 newState)
        _ -> ("error converting display value:\n" <> prettyPrint disp, Left . GenericRunTimeError "" $ conv2 disp)
    Left e -> ("runtime error:\n" <> show e, Left e)

runMainCore :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
            -> String -- ^Module's name with `main` function
            -> (CompiledExpr -> IO a)
            -> IO a
runMainCore modulesStrings s e =
  let parsedModules :: [(String, Either String [Either AnnotatedUPT (String, AnnotatedUPT)])]
      parsedModules = (fmap . fmap) parseModule modulesStrings
      parsedModulesErrors :: [(String, Either String [Either AnnotatedUPT (String, AnnotatedUPT)])]
      parsedModulesErrors = filter (\(moduleStr, parsed) -> case parsed of
                                      Left _  -> True
                                      Right _ -> False)
                                   parsedModules
      flattenLeft = \case
        Left a -> a
        Right a -> error "flattenLeft error: got a Right when it should be Left"
      flattenRight = \case
        Right a -> a
        Left a -> error "flattenRight error: got a Left when it should be Right"
      modules :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
      modules =
        case parsedModulesErrors of
          [] -> (fmap . fmap) flattenRight parsedModules
          errors -> let moduleWithError :: [(String, String)]
                        moduleWithError = (fmap . fmap) flattenLeft parsedModulesErrors
                        joinModuleError :: (String, String) -> String
                        joinModuleError (moduleName, errorStr) = "Error in module " <> moduleName <> ":\n" <> errorStr
                    in error . unlines $ joinModuleError <$> moduleWithError

  in
    case compileMain modules s of
      Left e  -> error $ "runMainCore failed: " <> show e
      Right g -> e g

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

{- TODO fix
schemeEval :: CompiledExpr -> IO ()
schemeEval iexpr = do
  writeFile "scheme.txt" ('(' : (show (app iexpr Zero) <> ")"))
  (_, Just mhout, _, _) <- createProcess (shell "chez-script runtime.so") { std_out = CreatePipe }
  scheme <- hGetContents mhout
  putStrLn scheme
-}

evalLoopCore :: CompiledExpr
             -> (String -> String -> IO String)
             -> String
             -> [String]
             -> IO String
evalLoopCore expr accumFn initAcc manualInput =
  let wrappedEval = funWrap expr appB
      mainLoop acc strInput s = do
        let (out, nextState) = wrappedEval s
        newAcc <- accumFn acc out
        case nextState of
          Left e -> pure $ newAcc <> "\n" <> show e
          Right ZeroB -> pure $ newAcc <> "\n" <> "done"
          Right ns -> do

            (inp, rest) <-
              if null strInput
              then (, []) <$> getLine
              else pure (head strInput, tail strInput)
            mainLoop newAcc rest $ pure (inp, ns)
  in mainLoop initAcc manualInput Nothing

evalLoop :: CompiledExpr -> IO ()
evalLoop iexpr = void $ evalLoopCore iexpr printAcc "" []
  where
    printAcc _ out = do
      putStrLn out
      pure ""

evalLoopWithInput :: [String] -> CompiledExpr -> IO String
evalLoopWithInput inputList iexpr = evalLoopCore iexpr printAcc "" inputList
  where
    printAcc acc out = if acc == ""
                       then pure out
                       else pure (acc <> "\n" <> out)

-- |Same as `evalLoop`, but keeping what was displayed.
evalLoop_ :: CompiledExpr -> IO String
evalLoop_ iexpr = evalLoopCore iexpr printAcc "" []
  where
    printAcc acc out = if acc == ""
                       then pure out
                       else pure (acc <> "\n" <> out)

calculateRecursionLimits :: SizingSettings -> Term3 -> Either EvalError CompiledExpr
calculateRecursionLimits sizingSettings t3 = case sizeTermM sizingSettings $ term3ToUnsizedExpr t3 of
    Left urt -> Left $ RecursionLimitError urt
    Right t  -> pure t

-- takes a main function and sizes the unsized recursion and then displays the results as comments in the original source
showSizingInSource :: String -> String -> String
showSizingInSource prelude s
  = let asLines = zip [0..] $ lines s
        parsed = first ParseError (parsePrelude prelude) >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr <$> first RE parsed
        sizedRecursion = unsizedExpr >>= (first RecursionLimitError . getSizesM 256)
        sizeLocs = error "TODO showSizingInSource implement sizeLocs" --Map.toAscList . buildUnsizedLocMap <$> unsizedExpr
        -- (orphanLocs, lineLocs) = partition (isNothing . locStartLineColumn . snd) sizeLocs
        (orphanLocs, lineLocs) = case sizeLocs of
          Left e   -> error "uh" -- ("Could not size: " <> show e)
          Right sl -> partition (isNothing . locStartLineColumn . snd) sl
        -- orphanList = map ((<> " ") . show . fst) orphanLocs
        -- orphans = "unsized with no location: " <> foldMap ((<> " ") . show . fst) orphanLocs
        orphans = error "TODO showSizingInSource thing"
        fromEnum' loc = case locStartLineColumn loc of
          Just (line, _) -> line
          Nothing        -> error "unexpected source-less location"
        lookupSize x = case sizedRecursion of
          Right (SizedRecursion sm) -> case Map.lookup x sm of
            Just (Just v) -> show v
            _             -> "?"
          _ -> "?"
        -- getSizeMatchingLine x = foldMap ((<> " ") . show) $ filter ((== x) . fromEnum' . snd) lineLocs
        getSizeMatchingLine x = case filter ((== x) . fromEnum' . snd) lineLocs of
          [] -> ""
          l -> ("   # " <>) $ foldMap ((\s -> show (fromEnum s) <> ":" <> lookupSize s <> " ") . fst) l
    in "showSizingInSource\n" <> orphans <> "\n" <> foldMap (\(l, s) -> s <> getSizeMatchingLine l <> "\n") asLines

parseMain :: [(String, AnnotatedUPT)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either ResolverError Term3               -- ^Error on Left.
parseMain prelude' str =
  let
      prelude = [("Prelude", Right . second unAnnotatedUPT <$> prelude')]
      parseAuxModule :: String -> (String, [Either AUPT (String, AUPT)])
      parseAuxModule str =
        case sequence ("AuxModule", parseModule ("import Prelude\n" <> str)) of
          Left e    -> error $ show e
          Right pam -> second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) pam
  in main2Term3 (parseAuxModule str:prelude) "AuxModule"

eval2IExpr :: [(String, [Either AUPT (String, AUPT)])] -> String -> Either String CompiledExpr
eval2IExpr extraModuleBindings str =
  first errorBundlePretty (runParser (parseOneExprOrTopLevelDefs resolved) "" str)
  >>= first show . process . AnnotatedUPT
  >>= tt . first show . compileUnitTest
    where
      tt = \case
        Left e -> Left $ show e
        Right x -> pure x
      aux = (\str -> Left (GeneratedLoc "eval2IExpr.import" Nothing :< ImportQualifiedUPF str str)) . fst <$> extraModuleBindings
      resolved = resolveAllImports extraModuleBindings aux

tagIExprWithEval :: CompiledExpr -> Cofree CompiledExprF (Int, CompiledExpr)
tagIExprWithEval iexpr = evalState (para alg iexpr) 0 where
  statePlus1 :: State Int Int
  statePlus1 = do
      i <- State.get
      State.modify (+ 1)
      pure i
  alg :: Base CompiledExpr
              ( CompiledExpr
              , State Int (Cofree CompiledExprF (Int, CompiledExpr))
              )
      -> State Int (Cofree CompiledExprF (Int, CompiledExpr))
  alg = \case
    BasicFW ZeroSF -> do
      i <- statePlus1
      pure ((i, basicEval ZeroB) :< embedB ZeroSF)
    StuckFW EnvSF -> do
      i <- statePlus1
      pure ((i, basicEval ZeroB) :< embedS EnvSF)
    StuckFW (SetEnvSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval $ SetEnvB iexpr0) :< embedS (SetEnvSF x')
    StuckFW (DeferSF ind (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval . StuckEE $ DeferSF (toEnum (-1)) iexpr0) :< embedS (DeferSF (toEnum (-1)) x')
    StuckFW (LeftSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval $ LeftB iexpr0) :< embedS (LeftSF x')
    StuckFW (RightSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval $ RightB iexpr0) :< embedS (RightSF x')
    BasicFW (PairSF (iexpr0, x) (iexpr1, y)) -> do
      i <- statePlus1
      x' <- x
      y' <- y
      pure $ (i, basicEval $ PairB iexpr0 iexpr1) :< embedB (PairSF x' y')
    StuckFW GateSF -> do
      i <- statePlus1
      pure $ (i, basicEval $ StuckEE GateSF) :< embedS GateSF

