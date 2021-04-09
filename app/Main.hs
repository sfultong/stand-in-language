module Main where

import           Data.Char
import qualified System.IO.Strict     as Strict
import           Telomare
import           Telomare.Eval
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker (inferType, typeCheck)
--import Telomare.Llvm

main = do
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
  -- Strict.readFile "tictactoe.tel" >>= runMain
  Strict.readFile "examples.tel" >>= runMain
