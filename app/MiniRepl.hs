{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
module Main where

import System.Console.Haskeline

import Text.Parsec.Error (ParseError)
import Text.Parsec 

import Text.Parsec.Indent

import SIL.Parser
import SIL.RunTime
import SIL

import Control.Monad.IO.Class
import Data.List

import qualified Data.Map         as Map
import qualified System.IO.Strict as Strict

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

data ReplState = ReplState Bindings

replStep :: Bindings -> String -> InputT IO Bindings
replStep bindings s = do
    let e_new_bindings = runReplParser bindings s
    case e_new_bindings of
        Left err -> do 
            outputStrLn $ "Parse error: " ++ show err
            return bindings
        Right (ReplExpr,new_bindings) -> do  
            case Map.lookup "_tmp_" new_bindings of
                Nothing -> outputStrLn "Could not find _tmp_ in bindings"
                Just e  -> do
                    iexpr <- convertPT <$> debruijinize [] e 
                    e_iexpr <- liftIO $ simpleEval iexpr
                    outputStrLn $ (show.PrettyIExpr) e_iexpr
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
replLoop (ReplState bs) = do 
    minput <- getInputLine "sil> "
    case minput of
        Nothing   -> return ()
        Just ":{" -> replLoop =<< (ReplState <$> (replStep bs =<< replMultiline [])) 
        Just s    -> replLoop =<< (ReplState <$> replStep bs s)

main = do
    e_prelude <- parsePrelude <$> Strict.readFile "Prelude.sil" 
    let bindings = case e_prelude of
            Left  _   -> Map.empty
            Right bds -> bds
    runInputT defaultSettings $ replLoop (ReplState bindings)
