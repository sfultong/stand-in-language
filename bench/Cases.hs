{-|
  Module: Cases.hs

  Defines cases for memory benchmarks, as well as simple parsers.
-}

{-# LANGUAGE FlexibleContexts #-}

module Cases where

import Text.Parsec hiding (label)
import Text.Parsec.Char

import qualified System.IO.Strict as Strict

type Label    = String
type Filename = String

data SrcType = SrcString   String
             | SrcFilename Filename
             deriving (Show)

data Case = Case Label SrcType 
            deriving(Show)

label :: Stream s m Char => ParsecT s u m Label
label = between (char '"') (char '"') (many $ noneOf "\"")

-- TODO: If one's willing, catch wrong filepaths
srcType :: Stream s m Char => ParsecT s u m SrcType
srcType = srcString <|> srcFilename
    where srcFilename = SrcFilename <$> remove <$> ((:) <$> anyChar <*> manyTill anyChar endOfLine)
          srcString   = SrcString   <$> try label
          remove s    = reverse $ takeWhile (`elem` " \t") $ reverse s 

aCase :: Stream s m Char => ParsecT s u m Case
aCase = Case <$> label <*> (many1 (oneOf " \t") *> srcType)

fileParser :: Stream s m Char => ParsecT s u m [Case]
fileParser = spaces *> many (aCase <* endOfLine)

loadCases :: FilePath -> IO [Case]
loadCases filepath = do
    loaded <- Strict.readFile filepath
    let e_parsed = parse fileParser filepath loaded
    case e_parsed of
        Right cases -> return cases
        Left err -> print err >> return []

