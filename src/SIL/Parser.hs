module SIL.Parser where

import Control.Monad.State
import Data.List (elemIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import SIL
import Text.Parsec
import Text.Parsec.Indent
import Text.Parsec.Pos
import qualified Text.Parsec.Token as Token

type VarList = [String]
type Bindings = Map String (Either CExpr IExpr)

data ParserState = ParserState
  { unbound :: VarList
  , bound :: Bindings
  }

addUnbound :: String -> ParserState -> Maybe ParserState
addUnbound s (ParserState unbound bound) = if Map.member s bound || elem s unbound
  then Nothing
  else pure $ ParserState (s:unbound) bound

addBound :: String -> (Either CExpr IExpr) -> ParserState -> Maybe ParserState
addBound name expr (ParserState unbound bound) = if Map.member name bound || elem name unbound
  then Nothing
  else pure $ ParserState unbound (Map.insert name expr bound)

resolve :: String -> ParserState -> Maybe (Either CExpr IExpr)
resolve name (ParserState unbound bound) = if Map.member name bound
  then Map.lookup name bound
  else (Right . Var . i2g) <$> elemIndex name unbound

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
brackets   = Token.brackets   lexer
braces     = Token.braces     lexer
commaSep   = Token.commaSep   lexer
commaSep1  = Token.commaSep1  lexer
integer    = Token.integer    lexer

parseString :: SILParser IExpr
parseString = s2g <$> Token.stringLiteral lexer

parseVariable :: SILParser (Either CExpr IExpr)
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
  a <- parseLongIExpr
  sameOrIndented <* char ',' <* spaces <?> "pair: ,"
  b <- parseLongIExpr
  sameOrIndented <* char '}' <* spaces <?> "pair: }"
  return $ Pair a b

parseList :: SILParser IExpr
parseList = do
  exprs <- brackets (commaSep parseLongIExpr)
  return $ foldr Pair Zero exprs

parseITE :: SILParser IExpr
parseITE = withPos $ do
  reserved "if"
  cond <- parseLongIExpr
  sameOrIndented <* reserved "then" <?> "ITE: then"
  thenExpr <- parseLongIExpr
  sameOrIndented <* reserved "else" <?> "ITE: else"
  elseExpr <- parseLongIExpr
  return $ ITE cond thenExpr elseExpr

parsePLeft :: SILParser IExpr
parsePLeft = PLeft <$> (reserved "left" *> parseSingleIExpr)

parsePRight :: SILParser IExpr
parsePRight = PRight <$> (reserved "right" *> parseSingleIExpr)

parseTrace :: SILParser IExpr
parseTrace = Trace <$> (reserved "trace" *> parseSingleIExpr)

parseSingleExpr :: SILParser (Either CExpr IExpr)
parseSingleExpr = Right <$> choice [ parseString
                                   , parseNumber
                                   , parsePair
                                   , parseList
                                   , parsePLeft
                                   , parsePRight
                                   , parseTrace
                                   ] <|> (Left <$> parseChurch)
                  <|> choice [ parseVariable
                             , parens parseLongExpr
                             ]

parseSingleIExpr :: SILParser IExpr
parseSingleIExpr = parseSingleExpr >>= promote where
  promote (Left g) = fail $ "(single) expecting typed expression " ++ show g
  promote (Right i) = pure i

parseApplied :: SILParser IExpr
parseApplied = let combine i (Right app) = combine i (Left $ CI app)
                   combine iexpr (Left cexpr) = App iexpr cexpr
               in withPos $ do
  exprs <- many1 (sameOrIndented *> parseSingleExpr)
  f <- case head exprs of
        (Left g) -> fail $ "(applied) expecting typed expression " ++ show g
        (Right i) -> pure i
  pure $ foldl combine f (tail exprs)

parseLongExpr :: SILParser (Either CExpr IExpr)
parseLongExpr = Right <$> choice [ parseLet
                                 , parseITE
                                 , parseApplied
                                 ] <|> (Left <$> parseLambda)

parseLongIExpr :: SILParser IExpr
parseLongIExpr = parseLongExpr >>= promote where
  promote (Left g) = fail $ "(long) expecting typed expression " ++ show g
  promote (Right i) = pure i

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
      iexpr <- parseLongIExpr
      setState oldState
      return $ foldr (\_ e -> Lam e) (CI iexpr) variables

parseChurch :: SILParser CExpr
parseChurch = (toChurch . fromInteger) <$> (reservedOp "$" *> integer)

parseAssignment :: SILParser ()
parseAssignment = do
  var <- identifier
  annotation <- optionMaybe (reservedOp ":" *> parseLongIExpr)
  reservedOp "=" <?> "assignment ="
  expr <- (Left <$> parseChurch) <|> parseLongExpr
  let annoExp = case (annotation, expr) of
        (Just a, Left cexpr) -> Right $ Anno cexpr a
        (Just a, Right iexpr) ->  Right $ Anno (CI iexpr) a
        _ -> expr
      assign ps = case addBound var annoExp ps of
        Just nps -> nps
        _ -> error $ "shadowing of binding not allowed " ++ var
  modifyState assign

parseLet :: SILParser IExpr
parseLet = withPos $ do
  reserved "let"
  initialState <- getState
  manyTill parseAssignment (reserved "in")
  expr <- parseLongIExpr
  setState initialState
  pure expr

parseTopLevel :: SILParser Bindings
parseTopLevel = do
  many parseAssignment <* eof
  (ParserState _ bound) <- getState
  pure bound

debugIndent i = show $ runState i (initialPos "debug")

parsePrelude = parseWithPrelude Map.empty

parseWithPrelude :: Bindings -> String -> Either ParseError Bindings
parseWithPrelude prelude = let startState = ParserState [] prelude
                           in runIndentParser parseTopLevel startState "sil"

parseMain :: Bindings -> String -> Either ParseError IExpr
parseMain prelude s = getMain <$> parseWithPrelude prelude s where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> error "no main method found"
    Just (Right main) -> main
    _ -> error "main must be a typed binding"
