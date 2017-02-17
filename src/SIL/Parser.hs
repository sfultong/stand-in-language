module SIL.Parser where

import Control.Monad.State
import Data.List (elemIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import SIL
import Text.Parsec
import Text.Parsec.Indent
import Text.Parsec.Language
import Text.Parsec.Pos
import qualified Text.Parsec.Token as Token

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
languageDef = haskellStyle
  { Token.reservedOpNames = ["\\","->", ":"]
  , Token.reservedNames = ["let", "in", "right", "left", "trace", "if", "then", "else"]
  }
  -}
languageDef = Token.LanguageDef
  { Token.commentStart   = "{-"
  , Token.commentEnd     = "-}"
  , Token.commentLine    = "--"
  , Token.nestedComments = True
  , Token.identStart     = letter
  , Token.identLetter    = alphaNum <|> oneOf "_'"
  , Token.opStart        = Token.opLetter languageDef
  , Token.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedOpNames = ["\\","->", ":", "=", "$"]
  , Token.reservedNames = ["let", "in", "right", "left", "trace", "if", "then", "else"]
  , Token.caseSensitive  = True
  }
lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
integer    = Token.integer    lexer

parseString :: SILParser IExpr
parseString = s2g <$> Token.stringLiteral lexer

parseVariable :: SILParser IExpr
parseVariable = do
              varName <- identifier
              parserState <- getState
              case resolve varName parserState of
                Nothing -> fail $ concat ["identifier ", varName, " undeclared"]
                Just i -> pure i

parseNumber :: SILParser IExpr
parseNumber = (i2g . fromInteger) <$> integer

parsePair :: SILParser IExpr
parsePair = withPos $ do
  char '{' <* spaces
  a <- parseIExpr2
  sameOrIndented <* char ',' <* spaces <?> "pair: ,"
  b <- parseIExpr2
  sameOrIndented <* char '}' <* spaces <?> "pair: }"
  return $ Pair a b

parseITE :: SILParser IExpr
parseITE = withPos $ do
  reserved "if"
  cond <- parseIExpr2
  sameOrIndented <* reserved "then" <?> "ITE: then"
  thenExpr <- parseIExpr2
  sameOrIndented <* reserved "else" <?> "ITE: else"
  elseExpr <- parseIExpr2
  return $ ITE cond thenExpr elseExpr

parseAnnotation :: SILParser IExpr
parseAnnotation = withPos $ do
  cexpr <- parseCExpr
  sameOrIndented <* reservedOp ":" <?> "annotation :"
  iexpr <- parseIExpr2
  return $ Anno cexpr iexpr

parsePLeft :: SILParser IExpr
parsePLeft = PLeft <$> (reserved "left" *> parseIExpr2)

parsePRight :: SILParser IExpr
parsePRight = PRight <$> (reserved "right" *> parseIExpr2)

parseTrace :: SILParser IExpr
parseTrace = Trace <$> (reserved "trace" *> parseIExpr2)

parseIExpr :: SILParser IExpr
parseIExpr = choice [ parseString
                    , parseNumber
                    , parsePair
                    , parseITE
                    , parsePLeft
                    , parsePRight
                    , parseTrace
                    , parseVariable]

parseApplied :: SILParser IExpr
parseApplied = let ciApp = CI <$> parseIExpr
                   ciApp2 = CI <$> parseIExpr2
                   applicator = sameOrIndented *> parens (parseLambda <|> ciApp2) <|> parseChurch
                     <|> ciApp
               in withPos $ do
  iexpr <- parens (parseAnnotation <|> parseApplied) <|> parseVariable
  applicants <- many1 applicator
  pure $ foldl App iexpr applicants

parseIExpr2 :: SILParser IExpr
parseIExpr2 = choice [ parseLet
                     , parseAnnotation
                     , try parseApplied
                     , parseIExpr
                     ]

parseLambda :: SILParser CExpr
parseLambda = do
  reservedOp "\\"
  variables <- many1 identifier
  sameOrIndented <* reservedOp "->" <?> "lambda ->"
  oldState <- getState
  case foldl (\ps n -> ps >>= addUnbound n) (pure oldState) variables of
    Nothing -> fail $ concat ["shadowing of bindings not allowed, ", show variables]
    Just ps -> do
      setState ps
      iexpr <- parseIExpr2
      setState oldState
      return $ foldr (\_ e -> Lam e) (CI iexpr) variables

parseChurch :: SILParser CExpr
parseChurch = (toChurch . fromInteger) <$> (reservedOp "$" *> integer)

parseCExpr :: SILParser CExpr
parseCExpr = choice [parseChurch, parseLambda]

parseAssignment :: SILParser ()
parseAssignment = do
  var <- identifier
  reservedOp "=" <?> "assignment ="
  expr <- parseIExpr2
  modifyState (\ps -> ps {bound = Map.insert var expr $ bound ps})

parseLet :: SILParser IExpr
parseLet = withPos $ do
  reserved "let" <* spaces
  initialState <- getState
  manyTill parseAssignment (reserved "in")
  expr <- parseIExpr2
  setState initialState
  pure expr

parseTopLevel :: SILParser (Map String IExpr)
parseTopLevel = do
  many parseAssignment <* eof
  (ParserState _ bound) <- getState
  pure bound

debugIndent i = show $ runState i (initialPos "debug")

parsePrelude = parseWithPrelude Map.empty

parseWithPrelude :: Map String IExpr -> String -> Either ParseError (Map String IExpr)
parseWithPrelude prelude = let startState = ParserState [] prelude
                           in runIndent "indent" . runParserT parseTopLevel startState "topLevel"

parseMain :: (Map String IExpr) -> String -> Either ParseError IExpr
parseMain prelude s = getMain <$> parseWithPrelude prelude s where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> error "no main method found"
    Just main -> main

testLet = let startState = ParserState [] Map.empty
          in debugIndent . runParserT parseLet startState "let"
