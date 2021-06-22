{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Data.Char
import qualified Options.Applicative  as O
import           System.Environment   (getArgs)
import qualified System.IO.Strict     as Strict
import           Telomare
import           Telomare.Eval
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker (inferType, typeCheck)
--import Telomare.Llvm

data TelomareOpts = TelomareOpts
  { telomareFile :: String
  , preludeFile  :: String
  } deriving Show

telomareOpts :: O.Parser TelomareOpts
telomareOpts = TelomareOpts
  <$> O.argument O.str (O.metavar "TELOMARE-FILE")
  <*> O.strOption
      ( O.long "prelude"
        <> O.metavar "PRELUDE-FILE"
        <> O.showDefault
        <> O.value "./Prelude.tel"
        <> O.short 'p'
        <> O.help "Telomare prelude file" )

main :: IO ()
main = do
  let opts = O.info (telomareOpts O.<**> O.helper)
        ( O.fullDesc
          <> O.progDesc "A simple but robust virtual machine" )
  topts <- O.execParser opts
  preludeString <- Strict.readFile $ preludeFile topts
  let
    prelude :: [(String, UnprocessedParsedTerm)]
    prelude = case parsePrelude preludeString of
      Right p -> p
      Left pe -> error pe
    runMain s = case compile <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop g
      Right z -> putStrLn $ "compilation failed somehow, with result " <> show z
  Strict.readFile (telomareFile topts) >>= runMain
