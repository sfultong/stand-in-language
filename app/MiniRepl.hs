{-# LANGUAGE CApiFFI               #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}

module Main where

import           Control.Monad.IO.Class
import qualified Control.Monad.State      as State
import           Data.List
import qualified Data.Map                 as Map
import           Debug.Trace              (trace)
import           Naturals
import           Options.Applicative      hiding (ParseError, (<|>))
import qualified Options.Applicative      as O
import           PrettyPrint
import           System.Console.Haskeline
import           System.Exit              (exitSuccess)
import qualified System.IO.Strict         as Strict
import           Telomare
import           Telomare.Eval
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker
import           Text.Megaparsec
import           Text.Megaparsec.Char

foreign import capi "gc.h GC_INIT" gcInit :: IO ()
foreign import ccall "gc.h GC_allow_register_threads" gcAllowRegisterThreads :: IO ()

-- Parsers for assignments/expressions within REPL
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--   Things in the REPL behave slightly different
-- than in the compiler. For example it is possible.
-- to overwrite top-level bindings.

-- | Add a Telomare expression to the ParserState.
addReplBound :: String -> UnprocessedParsedTerm -> [(String, UnprocessedParsedTerm)]
addReplBound name expr = [(name, expr)]

-- | Assignment parsing from the repl.
parseReplAssignment :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplAssignment = do
  (var, expr) <- parseAssignment <* eof
  pure $ addReplBound var expr

-- | Parse only an expression
parseReplExpr :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplExpr = do
  expr <- parseLongExpr <* eof
  pure $ addReplBound "_tmp_" expr

-- | Information about what has the REPL parsed.
data ReplStep a = ReplAssignment a
                | ReplExpr a
                deriving (Eq, Ord, Show, Functor)

-- | Combination of `parseReplExpr` and `parseReplAssignment`
parseReplStep :: TelomareParser (ReplStep [(String, UnprocessedParsedTerm )])
parseReplStep = try (parseReplAssignment >>= (pure . ReplAssignment))
                <|> (parseReplExpr >>= (pure . ReplExpr))

-- | Try to parse the given string and update the bindings.
runReplParser :: [(String, UnprocessedParsedTerm)]
              -> String
              -> Either String (ReplStep [(String, UnprocessedParsedTerm)])
runReplParser prelude str = (fmap . fmap) (prelude <>) $ runTelomareParser parseReplStep str

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
process' bindings x = rightToMaybe . process bindings $ x

-- |Obtain expression from the bindings and transform them into maybe a Term3.
resolveBinding' :: String
                -> [(String, UnprocessedParsedTerm)]
                -> Maybe Term3
resolveBinding' name bindings = lookup name bindings >>= (rightToMaybe . process bindings)

-- |Obtain expression from the bindings and transform them maybe into a IExpr.
resolveBinding :: String -> [(String, UnprocessedParsedTerm)] -> Maybe IExpr
resolveBinding name bindings = rightToMaybe $ compileUnitTest =<< (maybeToRight $ resolveBinding' name bindings)

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
      case compile' =<< (process bindings (LetUP bindings upt)) of
        Left err -> printer err
        Right iexpr' -> do
          iexpr <- eval (SetEnv (Pair (Defer iexpr') Zero))
          printer $ (show . PrettyIExpr) iexpr


-- REPL related logic
-- ~~~~~~~~~~~~~~~~~~

data ReplState = ReplState
    { replBindings :: [(String, UnprocessedParsedTerm)]
    , replEval     :: (IExpr -> IO IExpr)
    -- ^ Backend function used to compile IExprs.
    }

-- | Enter a single line assignment or expression.
replStep :: (IExpr -> IO IExpr)
         -> [(String, UnprocessedParsedTerm)]
         -> String
         -> InputT IO ([(String,UnprocessedParsedTerm)])
replStep eval bindings s = do
    let e_new_bindings = runReplParser bindings s
    case e_new_bindings of
        Left err -> do
            outputStrLn $ "Parse error: " ++ err
            return bindings
        Right (ReplExpr new_bindings) -> do
            printLastExpr outputStrLn (liftIO . eval) new_bindings
            return bindings
        Right (ReplAssignment new_bindings) -> do
            return new_bindings

-- | Obtain a multiline string.
replMultiline :: [String] -> InputT IO String
replMultiline buffer = do
    minput <- getInputLine ""
    case minput of
        Nothing   -> return ""
        Just ":}" -> return $ concat $ intersperse "\n" $ reverse buffer
        Just s    -> replMultiline (s : buffer)

-- | Main loop for the REPL.
replLoop :: ReplState -> InputT IO ()
replLoop (ReplState bs eval) = do
    minput <- getInputLine "telomare> "
    case minput of
        Nothing   -> return ()
        Just ":q" -> liftIO exitSuccess
        Just ":{" -> do
            new_bs <- replStep eval bs =<< replMultiline []
            replLoop $ ReplState new_bs eval
        Just s | ":dn" `isPrefixOf` s -> do
                   liftIO $ case (runReplParser bs . dropWhile (== ' ')) <$> stripPrefix ":dn" s of
                     Just (Right (ReplExpr new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
                       Just iexpr -> do
                         putStrLn . showNExprs $ fromTelomare iexpr
                         putStrLn . showNIE $ fromTelomare iexpr
                       _ -> putStrLn "some sort of error?"
                     _ -> putStrLn "parse error"
                   replLoop $ ReplState bs eval
        Just s | ":d" `isPrefixOf` s -> do
                   liftIO $ case (runReplParser bs . dropWhile (== ' ')) <$> stripPrefix ":d" s of
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
                   liftIO $ case (runReplParser bs . dropWhile (== ' ')) <$> stripPrefix ":t" s of
                     Just (Right (ReplExpr new_bindings)) -> case resolveBinding' "_tmp_" new_bindings of
                       Just iexpr -> print $ PrettyPartialType <$> inferType iexpr
                       _ -> putStrLn "some sort of error?"
                     _ -> putStrLn "parse error"
                   replLoop $ ReplState bs eval
        Just s    -> do
            new_bs <- replStep eval bs s
            replLoop $ ReplState new_bs eval

-- Command line settings
-- ~~~~~~~~~~~~~~~~~~~~~

data ReplBackend = SimpleBackend
                 | LLVMBackend
                 | NaturalsBackend
                 deriving (Show, Eq, Ord)

data ReplSettings = ReplSettings {
      _backend :: ReplBackend
    , _expr    :: Maybe String
    } deriving (Show, Eq)

-- | Choose a backend option between Haskell, LLVM, Naturals.
-- Haskell is default.
backendOpts :: Parser ReplBackend
backendOpts = flag'       LLVMBackend     (long "llvm"     <> help "LLVM Backend")
              O.<|> flag' SimpleBackend   (long "haskell"  <> help "Haskell Backend (default)")
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
startExpr eval bindings s_expr = do
    case runReplParser bindings s_expr of
        Left err                 -> error $ "Parse error: " ++ err
        Right (ReplAssignment _) -> error $ "Expression is an assignment"
        Right (ReplExpr binds)   -> printLastExpr putStrLn eval binds

main = do
    e_prelude <- parsePrelude <$> Strict.readFile "Prelude.tel"
    settings  <- execParser opts
    eval <- case _backend settings of
        SimpleBackend -> return simpleEval
        LLVMBackend   -> do
            gcInit
            gcAllowRegisterThreads
            return optimizedEval
        NaturalsBackend -> return fastInterpretEval
    let bindings = case e_prelude of
            Left  _   ->  []
            Right bds -> bds
    case _expr settings of
        Just  s -> startExpr eval bindings s
        Nothing -> startLoop (ReplState bindings eval)
