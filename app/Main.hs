{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Data.Char
import           System.Environment   (getArgs)
import qualified System.IO.Strict     as Strict
import           Telomare
import           Telomare.Eval
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker (inferType, typeCheck)
--import Telomare.Llvm

main :: IO ()
main = do
  args :: [String] <- getArgs
  case args of
    [a] -> pure ()
    [] -> error "No telomare file specified. USAGE: ./telomare <program-file>.tel"
    _ -> error "Too many arguments. USAGE: ./telomare <program-file>.tel"
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude :: [(String, UnprocessedParsedTerm)]
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error pe
    runMain s = case compile <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop g
      Right z -> putStrLn $ "compilation failed somehow, with result " <> show z
  -- s.b. usage of `head` is safe because of the case expresion on `args`
  Strict.readFile (head args) >>= runMain
