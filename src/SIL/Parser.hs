module SIL.Parser where

import Data.List (elemIndex)
--import Data.Map (Map)
--import qualified Data.Map as Map
import SIL
--import Text.ParserCombinators.Parsec
import Text.Parsec

type VarList = [String]

type SILParser = Parsec String VarList

{-
symbol :: Parser Char
symbol = oneOf "{,}:()"
-}

data ParseResult
  = CResult CExpr
  | IResult IExpr
  | Identifier String

parseString :: SILParser IExpr
parseString = do
  char '"'
  x <- many (noneOf "\"")
  char '"' <* spaces
  return $ s2g x

parseVar :: SILParser String
parseVar = do
              first <- letter
              rest <- many (letter <|> digit)
              spaces
              return (first:rest)

parseVariable :: SILParser IExpr
parseVariable = do
              varName <- parseVar
              vars <- getState
              case elemIndex varName vars of
                Nothing -> fail $ concat ["identifier ", varName, " undeclared"]
                Just i -> return . Var $ i2g i

parseNumber :: SILParser IExpr
parseNumber = (i2g . read) <$> (many1 digit) <* spaces

parsePair :: SILParser IExpr
parsePair = do
  char '{' <* spaces
  a <- parseIExpr
  char ',' <* spaces
  b <- parseIExpr
  char '}' <* spaces
  return $ Pair a b

parseITE :: SILParser IExpr
parseITE = do
  string "if" <* spaces
  cond <- parseIExpr
  string "then" <* spaces
  thenExpr <- parseIExpr
  string "else" <* spaces
  elseExpr <- parseIExpr
  return $ ITE cond thenExpr elseExpr

parseAnnotation :: SILParser IExpr
parseAnnotation = do
  cexpr <- try parseCExpr
  char ':' <* spaces
  iexpr <- parseIExpr
  return $ Anno cexpr iexpr

parsePLeft :: SILParser IExpr
parsePLeft = do
  string "pleft" <* spaces
  iexpr <- parseIExpr
  return $ PLeft iexpr

parsePRight :: SILParser IExpr
parsePRight = do
  string "pright" <* spaces
  iexpr <- parseIExpr
  return $ PRight iexpr

parseTrace :: SILParser IExpr
parseTrace = do
  string "trace" <* spaces
  iexpr <- parseIExpr
  return $ Trace iexpr

parseParenthesis :: SILParser IExpr
parseParenthesis = do
  char '(' <* spaces
  iexpr <- parseIExpr
  char ')' <* spaces
  return $ iexpr

parseIExpr :: SILParser IExpr
parseIExpr = choice [ parseParenthesis
                    , parseString
                    , parseNumber
                    , parsePair
                    , parseITE
                    , parsePLeft
                    , parsePRight
                    , parseTrace
                    , parseAnnotation
                    , parseVariable]

parseApplied :: SILParser IExpr
parseApplied = let applicator = (CI <$> parseIExpr) <|> parseLambda
               in do
  iexpr <- parseIExpr
  applicants <- many applicator
  pure $ foldr (flip App) iexpr applicants

parseLambda :: SILParser CExpr
parseLambda = do
  char '\\' <* spaces
  variables <- many1 parseVar
  string "->" <* spaces
  oldVars <- getState
  setState $ reverse variables ++ oldVars
  iexpr <- parseIExpr
  setState oldVars
  return $ foldr (\v e -> Lam (e)) (CI iexpr) variables

parseCExpr :: SILParser CExpr
parseCExpr = parseLambda -- choice [parseLambda, CI <$> parseIExpr]

parseSIL = runParser parseApplied [] "SIL"
