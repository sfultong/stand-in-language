{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
module Main where

import           Options.Applicative hiding (ParseError, (<|>))
import qualified Options.Applicative as O
import System.Console.Haskeline

import Text.Parsec.Error (ParseError)
import Text.Parsec 

import Text.Parsec.Indent

import SIL.Parser
import SIL.RunTime
import SIL
import PrettyPrint

import Control.Monad.IO.Class
import Data.List

import qualified Data.Map         as Map
import qualified System.IO.Strict as Strict

foreign import capi "gc.h GC_INIT" gcInit :: IO ()
foreign import ccall "gc.h GC_allow_register_threads" gcAllowRegisterThreads :: IO ()


-- REPL parsing

addReplBound :: String -> Term1 -> ParserState -> ParserState
addReplBound name expr (ParserState bound) = ParserState (Map.insert name expr bound)

parseReplAssignment :: SILParser ()
parseReplAssignment = do
  var <- identifier
  annotation <- optionMaybe parseRefinementCheck
  reservedOp "=" <?> "assignment ="
  expr <- parseLongExpr
  let annoExp = case annotation of
        Just f -> f expr
        _ -> expr
      assign ps = addReplBound var annoExp ps 
  modifyState assign

parseReplExpr :: SILParser ()
parseReplExpr = do
  expr <- parseLongExpr
  let assign ps = addReplBound "_tmp_" expr ps 
  modifyState assign

data ReplStep = ReplAssignment
              | ReplExpr

parseReplStep :: SILParser (ReplStep, Bindings)
parseReplStep =  step >>= (\x -> (x,) <$> (bound <$> getState)) 
    where step = try (parseReplAssignment *> return ReplAssignment)
               <|>   (parseReplExpr       *> return ReplExpr)

runReplParser :: Bindings -> String -> Either ParseError (ReplStep, Bindings)
runReplParser prelude = let startState = ParserState prelude
                        in runIndentParser parseReplStep startState "sil"



-- Repl loop

data ReplState = ReplState 
    { replBindings :: Bindings
    , replEval     :: (IExpr -> IO IExpr)
    }

replStep :: (IExpr -> IO IExpr) -> Bindings -> String -> InputT IO Bindings
replStep eval bindings s = do
    let e_new_bindings = runReplParser bindings s
    case e_new_bindings of
        Left err -> do 
            outputStrLn $ "Parse error: " ++ show err
            return bindings
        Right (ReplExpr,new_bindings) -> do  
            case Map.lookup "_tmp_" new_bindings of
                Nothing -> outputStrLn "Could not find _tmp_ in bindings"
                Just e  -> do
                    let m_iexpr = convertPT <$> debruijinize [] e 
                    case m_iexpr of
                        Nothing     -> outputStrLn "conversion error"
                        Just iexpr' -> do
                            iexpr <- liftIO $ eval (SetEnv (Pair (Defer iexpr') Zero))
                            outputStrLn $ (show.PrettyIExpr) iexpr
            return bindings
        Right (ReplAssignment, new_bindings) -> do
            return new_bindings
            

replMultiline :: [String] -> InputT IO String
replMultiline buffer = do
    minput <- getInputLine ""
    case minput of
        Nothing -> return ""
        Just ":}" -> return $ concat $ intersperse "\n" $ reverse buffer
        Just s    -> replMultiline (s : buffer) 


replLoop :: ReplState -> InputT IO ()
replLoop (ReplState bs eval) = do 
    minput <- getInputLine "sil> "
    case minput of
        Nothing   -> return ()
        Just ":{" -> do
            new_bs <- replStep eval bs =<< replMultiline []
            replLoop $ ReplState new_bs eval 
        Just s | ":d" `isPrefixOf` s -> do
                   liftIO $ case (runReplParser bs . dropWhile (== ' ')) <$> stripPrefix ":d" s of
                     Just (Right (ReplExpr, new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
                       Just iexpr -> putStrLn $ showPIE iexpr
                       _ -> putStrLn "some sort of error?"
                     _ -> putStrLn "parse error"
                   replLoop $ ReplState bs eval
        Just s    -> do 
            new_bs <- replStep eval bs s
            replLoop $ (ReplState new_bs eval)

-- Parse options

data ReplBackend = SimpleBackend
                 | LLVMBackend 

backendOpts :: Parser ReplBackend
backendOpts = flag'     LLVMBackend (long "llvm" <> help "LLVM Backend")
              O.<|> flag' SimpleBackend (long "haskell" <> help "Haskell Backend")

opts :: ParserInfo ReplBackend
opts = info (backendOpts <**> helper)
    ( fullDesc
    <> progDesc "Stand-in-language simple read-eval-print-loop")

main = do
    e_prelude <- parsePrelude <$> Strict.readFile "Prelude.sil" 
    backend <- execParser opts
    eval <- case backend of
        SimpleBackend -> return simpleEval
        LLVMBackend   -> do 
            gcInit
            gcAllowRegisterThreads
            return optimizedEval
    let bindings = case e_prelude of
            Left  _   -> Map.empty
            Right bds -> bds
    runInputT defaultSettings $ replLoop (ReplState bindings eval)
