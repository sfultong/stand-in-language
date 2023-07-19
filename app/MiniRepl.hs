{-# LANGUAGE CApiFFI               #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant $" #-}

module Main where

import Control.Monad.IO.Class
import qualified Control.Monad.State as State
import Data.Functor ((<&>))
import Data.List
import qualified Data.Map as Map
import Debug.Trace (trace)
import Naturals
import Options.Applicative hiding (ParseError, (<|>))
import qualified Options.Applicative as O
import PrettyPrint
import System.Console.Haskeline
import System.Exit (exitSuccess)
import qualified System.IO.Strict as Strict
import Text.Megaparsec
import Text.Megaparsec.Char
import Telomare (IExpr (..), PrettyIExpr (PrettyIExpr),
                 PrettyPartialType (PrettyPartialType),
                 TelomareLike (fromTelomare, toTelomare), Term3)
import Telomare.Eval (EvalError (..), compileUnitTest)
import Telomare.Parser (TelomareParser, UnprocessedParsedTerm (..),
                        parseAssignment, parseLongExpr, parsePrelude, process,
                        runTelomareParser)
import Telomare.RunTime (fastInterpretEval, simpleEval)
import Telomare.TypeChecker (inferType)

-- Parsers for assignments/expressions within REPL
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--   Things in the REPL behave slightly different
-- than in the compiler. For example it is possible.
-- to overwrite top-level bindings.

-- | Assignment parsing from the repl.
parseReplAssignment :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplAssignment = do
  (var, expr) <- parseAssignment <* eof
  pure [(var, expr)]

-- | Parse only an expression
parseReplExpr :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplExpr = do
  expr <- parseLongExpr <* eof
  pure [("_tmp_", expr)]

-- | Information about what has the REPL parsed.
data ReplStep a = ReplAssignment a
                | ReplExpr a
                deriving (Eq, Ord, Show, Functor)

-- | Combination of `parseReplExpr` and `parseReplAssignment`
parseReplStep :: TelomareParser (ReplStep [(String, UnprocessedParsedTerm )])
parseReplStep = try (parseReplAssignment <&> ReplAssignment)
                <|> (parseReplExpr <&> ReplExpr)

-- | Try to parse the given string and update the bindings.
runReplParser :: [(String, UnprocessedParsedTerm)]
              -> String
              -> Either String (ReplStep [(String, UnprocessedParsedTerm)])
runReplParser prelude str = fmap (prelude <>) <$> runTelomareParser parseReplStep str

-- Common functions
-- ~~~~~~~~~~~~~~~~

-- |Forget Left helper function.
rightToMaybe :: Either a b -> Maybe b
rightToMaybe (Right b) = Just b
rightToMaybe _         = Nothing

maybeToRight :: Maybe a -> Either EvalError a
maybeToRight (Just x) = Right x
-- This will become a Maybe right after being used, so it doesn't matter what error is present
maybeToRight Nothing  = Left CompileConversionError

-- |Extra processing (see `Telomare.Parser.process`) useful for the MinRepl's context.
process' :: [(String, UnprocessedParsedTerm)] -> UnprocessedParsedTerm -> Maybe Term3
process' bindings = rightToMaybe . process bindings

-- |Obtain expression from the bindings and transform them into maybe a Term3.
resolveBinding' :: String
                -> [(String, UnprocessedParsedTerm)]
                -> Maybe Term3
resolveBinding' name bindings = lookup name bindings >>= rightToMaybe . process bindings

-- |Obtain expression from the bindings and transform them maybe into a IExpr.
resolveBinding :: String -> [(String, UnprocessedParsedTerm)] -> Maybe IExpr
resolveBinding name bindings = rightToMaybe $ compileUnitTest =<< maybeToRight (resolveBinding' name bindings)

-- |Print last expression bound to
-- the _tmp_ variable in the bindings
printLastExpr :: (MonadIO m)
              => (String -> m ())    -- ^Printing function
              -> (IExpr -> m IExpr) -- ^Telomare backend
              -> [(String, UnprocessedParsedTerm)]
              -> m ()
printLastExpr printer eval bindings = case lookup "_tmp_" bindings of
  Nothing -> printer "Could not find _tmp_ in bindings"
  Just upt -> do
    let compile' x = case compileUnitTest x of
                       Left err -> Left . show $ err
                       Right r  -> Right r
    case compile' =<< process bindings (LetUP bindings upt) of
      Left err -> printer err
      Right iexpr' -> do
        iexpr <- eval (SetEnv (Pair (Defer iexpr') Zero))
        printer $ (show . PrettyIExpr) iexpr

-- REPL related logic
-- ~~~~~~~~~~~~~~~~~~

data ReplState = ReplState
  { replBindings :: [(String, UnprocessedParsedTerm)]
  , replEval     :: IExpr -> IO IExpr
  -- ^ Backend function used to compile IExprs.
  }

-- | Enter a single line assignment or expression.
replStep :: (IExpr -> IO IExpr)
         -> [(String, UnprocessedParsedTerm)]
         -> String
         -> InputT IO [(String, UnprocessedParsedTerm)]
replStep eval bindings s = do
  let e_new_bindings = runReplParser bindings s
  case e_new_bindings of
    Left err -> do
      outputStrLn ("Parse error: " <> err)
      pure bindings
    Right (ReplExpr new_bindings) -> do
      printLastExpr outputStrLn (liftIO . eval) new_bindings
      pure bindings
    Right (ReplAssignment new_bindings) -> pure new_bindings

-- | Obtain a multiline string.
replMultiline :: [String] -> InputT IO String
replMultiline buffer = do
  minput <- getInputLine ""
  case minput of
    Nothing   -> pure ""
    Just ":}" -> pure $ intercalate "\n" (reverse buffer)
    Just s    -> replMultiline (s : buffer)

-- | Main loop for the REPL.
replLoop :: ReplState -> InputT IO ()
replLoop (ReplState bs eval) = do
  minput <- getInputLine "telomare> "
  case minput of
    Nothing   -> pure ()
    Just ":q" -> liftIO exitSuccess
    Just ":{" -> do
      new_bs <- replStep eval bs =<< replMultiline []
      replLoop $ ReplState new_bs eval
    Just s | ":dn" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":dn" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
          Just iexpr -> do
            putStrLn . showNExprs $ fromTelomare iexpr
            putStrLn . showNIE $ fromTelomare iexpr
          _ -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval
    Just s | ":d" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":d" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
          Just iexpr -> putStrLn $ showPIE iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval
{-
    Just s | ":tt" `isPrefixOf` s -> do
      liftIO $ case (runReplParser bs . dropWhile (== ' ')) <$> stripPrefix ":tt" s of
        Just (Right (ReplExpr, new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
          Just iexpr -> print . showTraceTypes $ iexpr
          _ -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval
-}
    Just s | ":t" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":t" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding' "_tmp_" new_bindings of
          Just iexpr -> print $ PrettyPartialType <$> inferType iexpr
          _ -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval
    Just fileName | ":l " `isPrefixOf` fileName -> do
      let fileName' = drop 3 fileName
      fileString <- liftIO $ Strict.readFile fileName'
      let eitherFileBindings = parsePrelude fileString
      case parsePrelude fileString of
        Left errStr -> do
          liftIO . putStrLn $ "Error from loaded file: " <> errStr
          replLoop $ ReplState bs eval
        Right fileBindings -> replLoop $ ReplState (bs <> fileBindings) eval
    Just s -> do
      new_bs <- replStep eval bs s
      replLoop $ ReplState new_bs eval

-- Command line settings
-- ~~~~~~~~~~~~~~~~~~~~~

data ReplBackend = SimpleBackend
                 | NaturalsBackend
                 deriving (Show, Eq, Ord)

data ReplSettings = ReplSettings
  { _backend :: ReplBackend
  , _expr    :: Maybe String
  } deriving (Show, Eq)

-- | Choose a backend option between Haskell, Naturals.
-- Haskell is default.
backendOpts :: Parser ReplBackend
backendOpts = flag'       SimpleBackend   (long "haskell"  <> help "Haskell Backend (default)")
              O.<|> flag' NaturalsBackend (long "naturals" <> help "Naturals Interpretation Backend")
              O.<|> pure SimpleBackend

-- | Process a given expression instead of entering the repl.
exprOpts :: Parser (Maybe String)
exprOpts = optional $ strOption ( long "expr" <> short 'e' <> help "Expression to be computed")

-- | Combined options
opts :: ParserInfo ReplSettings
opts = info (settings <**> helper)
  ( fullDesc
  <> progDesc "Stand-in-language simple read-eval-print-loop")
    where settings = ReplSettings <$> backendOpts <*> exprOpts

-- Program
-- ~~~~~~~

-- | Start REPL loop.
startLoop :: ReplState -> IO ()
startLoop state = runInputT defaultSettings $ replLoop state

-- | Compile and output a Telomare expression.
startExpr :: (IExpr -> IO IExpr)
          -> [(String, UnprocessedParsedTerm)]
          -> String
          -> IO ()
startExpr eval bindings s_expr = case runReplParser bindings s_expr of
  Left err                 -> error $ ("Parse error: " <> err)
  Right (ReplAssignment _) -> error "Expression is an assignment"
  Right (ReplExpr binds)   -> printLastExpr putStrLn eval binds

main = do
  e_prelude <- parsePrelude <$> Strict.readFile "Prelude.tel"
  settings  <- execParser opts
  eval <- case _backend settings of
    SimpleBackend   -> pure simpleEval
    NaturalsBackend -> pure fastInterpretEval
  let bindings = case e_prelude of
                   Left  _   ->  []
                   Right bds -> bds
  case _expr settings of
    Just  s -> startExpr eval bindings s
    Nothing -> startLoop (ReplState bindings eval)
