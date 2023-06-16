{-|
  Module: Cases.hs

  Defines parsers for cases for memory benchmark.
-}

{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant $" #-}

module MemoryBench.Cases where

import Text.Parsec hiding (label)
import Text.Parsec.Char

import qualified System.IO.Strict as Strict

import Data.Maybe
import Data.Functor (($>), (<$))

type Label    = String

data SrcType = SrcString   String
             | SrcFilePath FilePath
             deriving (Show)


data ParsedCase = ParsedCase Label SrcType
            deriving(Show)

data Case = Case Label String
            deriving(Show)

toCase :: ParsedCase -> IO Case
toCase (ParsedCase l (SrcString   str))  = return (Case l str)
toCase (ParsedCase l (SrcFilePath path)) = Case l <$> Strict.readFile path

-- Parsers
-- ~~~~~~~
endOfLineAndFile :: Stream s m Char => ParsecT s u m Char
endOfLineAndFile = endOfLine <|> (eof $> '\n')

label :: Stream s m Char => ParsecT s u m Label
label = between (char '"') (char '"') (many $ noneOf "\"")

-- TODO: If one's willing, catch wrong filepaths
srcType :: Stream s m Char => ParsecT s u m SrcType
srcType = srcString <|> srcFilename
    where srcFilename = SrcFilePath . remove <$> ((:) <$> anyChar <*> manyTill anyChar (lookAhead endOfLineAndFile))
          srcString   = SrcString   <$> try label
          remove s    = reverse $ takeWhile (not.(`elem` " \t")) $ reverse s

aCase :: Stream s m Char => ParsecT s u m ParsedCase
aCase = try labeled <|> srced
    where labeled = ParsedCase <$> label <*> (many1 (oneOf " \t") *> srcType)
          srced   = (\x -> ParsedCase (getStr x) x ) <$> srcType
          getStr (SrcString  str) = str
          getStr (SrcFilePath fp) = fp

fileParser :: Stream s m Char => ParsecT s u m [ParsedCase]
fileParser = catMaybes <$> many (spaces *> (commented <|> a_case) <* endOfLineAndFile)
    where commented = (Nothing <$ try (string "--")) <* manyTill anyChar (lookAhead endOfLineAndFile)
          a_case    = Just <$> aCase

loadCases :: FilePath -> IO [Case]
loadCases filepath = do
    loaded <- Strict.readFile filepath
    let e_parsed = parse fileParser filepath loaded
    case e_parsed of
        Right cases -> mapM toCase cases
        Left err    -> print err >> return []


