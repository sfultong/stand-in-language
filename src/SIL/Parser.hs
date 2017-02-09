module SIL.Parser where

import Data.List (elemIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import SIL
import Text.Parsec
import Text.Parsec.Indent

type VarList = [String]

data ParserState = ParserState
  { unbound :: VarList
  , bound :: Map String IExpr
  }

addUnbound :: String -> ParserState -> Maybe ParserState
addUnbound s (ParserState unbound bound) = if Map.member s bound || elem s unbound
  then Nothing
  else pure $ ParserState (s:unbound) bound

addBound :: String -> IExpr -> ParserState -> Maybe ParserState
addBound name iexpr (ParserState unbound bound) = if Map.member name bound || elem name unbound
  then Nothing
  else pure $ ParserState unbound (Map.insert name iexpr bound)

resolve :: String -> ParserState -> Maybe IExpr
resolve name (ParserState unbound bound) = if Map.member name bound
  then Map.lookup name bound
  else (Var . i2g) <$> elemIndex name unbound

type SILParser a = IndentParser String ParserState a

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
              parserState <- getState
              case resolve varName parserState of
                Nothing -> fail $ concat ["identifier ", varName, " undeclared"]
                Just i -> pure i

parseNumber :: SILParser IExpr
parseNumber = (i2g . read) <$> (many1 digit) <* spaces

parsePair :: SILParser IExpr
parsePair = do
  char '{' <* spaces
  a <- parseApplied
  char ',' <* spaces
  b <- parseApplied
  char '}' <* spaces
  return $ Pair a b

parseITE :: SILParser IExpr
parseITE = do
  string "if" <* spaces
  cond <- parseApplied
  string "then" <* spaces
  thenExpr <- parseApplied
  string "else" <* spaces
  elseExpr <- parseApplied
  return $ ITE cond thenExpr elseExpr

parseAnnotation :: SILParser IExpr
parseAnnotation = do
  cexpr <- try parseLambda
  char ':' <* spaces
  iexpr <- parseApplied
  return $ Anno cexpr iexpr

parsePLeft :: SILParser IExpr
parsePLeft = do
  string "pleft" <* spaces
  iexpr <- parseApplied
  return $ PLeft iexpr

parsePRight :: SILParser IExpr
parsePRight = do
  string "pright" <* spaces
  iexpr <- parseApplied
  return $ PRight iexpr

parseTrace :: SILParser IExpr
parseTrace = do
  string "trace" <* spaces
  iexpr <- parseApplied
  return $ Trace iexpr

parseParenthesis :: SILParser IExpr
parseParenthesis = do
  char '(' <* spaces
  iexpr <- parseApplied
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
                    , parseLet
                    , parseAnnotation
                    , parseVariable]

parseApplied :: SILParser IExpr
parseApplied = let applicator = try parseCExpr <|> (CI <$> parseIExpr)
               in do
  iexpr <- parseIExpr
  applicants <- many applicator
  pure $ foldr (flip App) iexpr applicants

parseLambda :: SILParser CExpr
parseLambda = do
  char '\\' <* spaces
  variables <- many1 parseVar
  string "->" <* spaces
  oldState <- getState
  case foldl (\ps n -> ps >>= addUnbound n) (pure oldState) variables of
    Nothing -> fail $ concat ["shadowing of bindings not allowed, ", show variables]
    Just ps -> do
      setState ps
      iexpr <- parseApplied
      setState oldState
      return $ foldr (\v e -> Lam (e)) (CI iexpr) variables

parseLambdaParenthesis :: SILParser CExpr
parseLambdaParenthesis = do
  char '(' <* spaces
  lambda <- parseLambda
  char ')' <* spaces
  return lambda

parseCExpr :: SILParser CExpr
parseCExpr = choice [parseLambda, parseLambdaParenthesis]

parseAssignment :: SILParser ()
parseAssignment = do
  var <- parseVar
  char '=' <* spaces
  applied <- parseApplied
  modifyState (\ps -> ps {bound = Map.insert var applied $ bound ps})

parseLet :: SILParser IExpr
parseLet = withPos $ do
  initialState <- getState
  lets <- withBlock' (string "let" <* spaces) parseAssignment
  checkIndent *> string "in" *> spaces
  expr <- parseApplied
  setState initialState
  pure expr

parseTopLevel :: SILParser IExpr
parseTopLevel = do
  many parseAssignment
  (ParserState _ bound) <- getState
  case Map.lookup "main" bound of
    Nothing -> fail "no main method found"
    Just main -> pure main

parseSIL = let startState = ParserState [] Map.empty
           in runIndent "indent" . runParserT parseTopLevel startState "SIL"

testSIL = showResult . parseSIL
  where showResult (Left err) = "parse error: " ++ show err
        showResult (Right iexpr) = show iexpr
