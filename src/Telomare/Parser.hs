{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parser where

import Control.Lens.Combinators (Plated (..), makePrisms)
import Control.Lens.Plated (Plated (..))
import Control.Monad (void)
import Control.Monad.State (State)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Functor (($>))
import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.Maybe (fromJust)
import Data.Void (Void)
import Data.Word (Word8)
import qualified System.IO.Strict as Strict
import Telomare (ParserTerm (..), ParserTermF (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..), Term1 (..), Term2 (..),
                 Term3 (..), UnsizedRecursionToken, appF, clamF, deferF, lamF,
                 nextBreakToken, unsizedRecursionWrapper, varNF)
import Telomare.TypeChecker (typeCheck)
import Text.Megaparsec (MonadParsec (eof, notFollowedBy, try), Parsec, Pos,
                        between, choice, errorBundlePretty, many, manyTill,
                        optional, runParser, sepBy, some, (<?>), (<|>))
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Pos (Pos)
import Text.Read (readMaybe)

-- |AST for patterns in `case` expressions
data Pattern
  = PatternVar String
  | PatternInt Int
  | PatternIgnore
  | PatternPair Pattern Pattern
  deriving (Show, Eq, Ord)
makeBaseFunctor ''Pattern

data UnprocessedParsedTerm
  = VarUP String
  | ITEUP UnprocessedParsedTerm UnprocessedParsedTerm UnprocessedParsedTerm
  | LetUP [(String, UnprocessedParsedTerm)] UnprocessedParsedTerm
  | ListUP [UnprocessedParsedTerm]
  | IntUP Int
  | StringUP String
  | PairUP UnprocessedParsedTerm UnprocessedParsedTerm
  | AppUP UnprocessedParsedTerm UnprocessedParsedTerm
  | LamUP String UnprocessedParsedTerm
  | ChurchUP Int
  | UnsizedRecursionUP UnprocessedParsedTerm UnprocessedParsedTerm UnprocessedParsedTerm
  | LeftUP UnprocessedParsedTerm
  | RightUP UnprocessedParsedTerm
  | TraceUP UnprocessedParsedTerm
  | CheckUP UnprocessedParsedTerm UnprocessedParsedTerm
  | HashUP UnprocessedParsedTerm -- ^ On ad hoc user defined types, this term will be substitued to a unique Int.
  | CaseUP UnprocessedParsedTerm [(Pattern, UnprocessedParsedTerm)]
  deriving (Eq, Ord, Show)
makeBaseFunctor ''UnprocessedParsedTerm -- Functorial version UnprocessedParsedTerm
makePrisms ''UnprocessedParsedTerm

instance Plated UnprocessedParsedTerm where
  plate f = \case
    ITEUP i t e -> ITEUP <$> f i <*> f t <*> f e
    LetUP l x   -> LetUP <$> traverse sequenceA (second f <$> l) <*> f x
    CaseUP x l  -> CaseUP <$> f x <*> traverse sequenceA (second f <$> l)
    ListUP l    -> ListUP <$> traverse f l
    PairUP a b  -> PairUP <$> f a <*> f b
    AppUP u x   -> AppUP <$> f u <*> f x
    LamUP s x   -> LamUP s <$> f x
    LeftUP x    -> LeftUP <$> f x
    RightUP x   -> RightUP <$> f x
    TraceUP x   -> TraceUP <$> f x
    HashUP x    -> HashUP <$> f x
    CheckUP c x -> CheckUP <$> f c <*> f x
    x           -> pure x

-- |TelomareParser :: * -> *
type TelomareParser = Parsec Void String

-- |Parse a variable.
parseVariable :: TelomareParser UnprocessedParsedTerm
parseVariable = VarUP <$> identifier

-- |Line comments start with "--".
lineComment :: TelomareParser ()
lineComment = L.skipLineComment "--"

-- |A block comment starts with "{-" and ends at "-}".
-- Nested block comments are also supported.
blockComment :: TelomareParser ()
blockComment = L.skipBlockCommentNested "{-" "-}"

-- |Space Consumer: Whitespace and comment parser that does not consume new-lines.
sc :: TelomareParser ()
sc = L.space
  (void $ some (char ' ' <|> char '\t'))
  lineComment
  blockComment

-- |Space Consumer: Whitespace and comment parser that does consume new-lines.
scn :: TelomareParser ()
scn = L.space space1 lineComment blockComment

-- |This is a wrapper for lexemes that picks up all trailing white space
-- using sc
lexeme :: TelomareParser a -> TelomareParser a
lexeme = L.lexeme sc

-- |A parser that matches given text using string internally and then similarly
-- picks up all trailing white space.
symbol :: String -> TelomareParser String
symbol = L.symbol sc

-- |This is to parse reserved words.
reserved :: String -> TelomareParser ()
reserved w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

-- |List of reserved words
rws :: [String]
rws = ["let", "in", "if", "then", "else", "case", "of" ]

-- |Variable identifiers can consist of alphanumeric characters, underscore,
-- and must start with an English alphabet letter
identifier :: TelomareParser String
identifier = lexeme . try $ p >>= check
  where
    p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_' <?> "variable")
    check x = if x `elem` rws
              then fail ("keyword " <> (show x <> " cannot be an identifier"))
              else pure x

-- |Parser for parenthesis.
parens :: TelomareParser a -> TelomareParser a
parens = between (symbol "(") (symbol ")")

-- |Parser for brackets.
brackets :: TelomareParser a -> TelomareParser a
brackets = between (symbol "[") (symbol "]")

-- |Parser for curly braces
curlies :: TelomareParser a -> TelomareParser a
curlies = between (symbol "{") (symbol "}")

-- |Comma sepparated TelomareParser that will be useful for lists
commaSep :: TelomareParser a -> TelomareParser [a]
commaSep p = p `sepBy` symbol ","

-- |Integer TelomareParser used by `parseNumber` and `parseChurch`
integer :: TelomareParser Integer
integer = toInteger <$> lexeme L.decimal

-- |Parse string literal.
parseString :: TelomareParser UnprocessedParsedTerm
parseString = StringUP <$> (char '"' >> manyTill L.charLiteral (char '"'))

-- |Parse number (Integer).
parseNumber :: TelomareParser UnprocessedParsedTerm
parseNumber = IntUP . fromInteger <$> integer

-- |Parse a pair.
parsePair :: TelomareParser UnprocessedParsedTerm
parsePair = parens $ do
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  pure $ PairUP a b

-- |Parse unsized recursion triple
parseUnsizedRecursion :: TelomareParser UnprocessedParsedTerm
parseUnsizedRecursion = curlies $ do
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  _ <- symbol "," <* scn
  c <- parseLongExpr <* scn
  pure $ UnsizedRecursionUP a b c

-- |Parse a list.
parseList :: TelomareParser UnprocessedParsedTerm
parseList = do
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  pure $ ListUP exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: TelomareParser UnprocessedParsedTerm
parseITE = do
  reserved "if" <* scn
  cond <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "then" <* scn
  thenExpr <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "else" <* scn
  elseExpr <- parseLongExpr <* scn
  pure $ ITEUP cond thenExpr elseExpr

parseHash :: TelomareParser UnprocessedParsedTerm
parseHash = do
  symbol "#" <* scn
  upt <- parseSingleExpr :: TelomareParser UnprocessedParsedTerm
  pure $ HashUP upt

parseCase :: TelomareParser UnprocessedParsedTerm
parseCase = do
  reserved "case" <* scn
  iexpr <- parseLongExpr <* scn
  reserved "of" <* scn
  lpc <- many $ parseSingleCase <* scn
  pure $ CaseUP iexpr lpc

parseSingleCase :: TelomareParser (Pattern, UnprocessedParsedTerm)
parseSingleCase = do
  p <- parsePattern <* scn
  reserved "->" <* scn
  c <- parseLongExpr <* scn
  pure (p,c)

parsePattern :: TelomareParser Pattern
parsePattern = choice $ try <$> [ parsePatternIgnore
                                , parsePatternVar
                                , parsePatternInt
                                , parsePatternPair
                                ]

parsePatternPair :: TelomareParser Pattern
parsePatternPair = parens $ do
  p <- scn *> parsePattern <* scn
  _ <- symbol "," <* scn
  b <- parsePattern <* scn
  pure $ PatternPair p b

parsePatternInt :: TelomareParser Pattern
parsePatternInt = PatternInt . fromInteger <$> integer

parsePatternVar :: TelomareParser Pattern
parsePatternVar = PatternVar <$> identifier

parsePatternIgnore :: TelomareParser Pattern
parsePatternIgnore = symbol "_" >> pure PatternIgnore

-- |Parse a single expression.
parseSingleExpr :: TelomareParser UnprocessedParsedTerm
parseSingleExpr = choice $ try <$> [ parseHash
                                   , parseString
                                   , parseNumber
                                   , parsePair
                                   , parseUnsizedRecursion
                                   , parseList
                                   , parseChurch
                                   , parseVariable
                                   , parens (scn *> parseLongExpr <* scn)
                                   ]

-- |Parse application of functions.
parseApplied :: TelomareParser UnprocessedParsedTerm
parseApplied = do
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) ->
      pure $ foldl AppUP f args
    _ -> fail "expected expression"

-- |Parse lambda expression.
parseLambda :: TelomareParser UnprocessedParsedTerm
parseLambda = do
  symbol "\\" <* scn
  variables <- some identifier <* scn
  symbol "->" <* scn
  -- TODO make sure lambda names don't collide with bound names
  term1expr <- parseLongExpr <* scn
  pure $ foldr LamUP term1expr variables

-- |Parser that fails if indent level is not `pos`.
parseSameLvl :: Pos -> TelomareParser a -> TelomareParser a
parseSameLvl pos parser = do
  lvl <- L.indentLevel
  if pos == lvl then parser else fail "Expected same indentation."

-- |Parse let expression.
parseLet :: TelomareParser UnprocessedParsedTerm
parseLet = do
  reserved "let" <* scn
  lvl <- L.indentLevel
  bindingsList <- manyTill (parseSameLvl lvl parseAssignment) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  pure $ LetUP bindingsList expr

-- |Parse long expression.
parseLongExpr :: TelomareParser UnprocessedParsedTerm
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseApplied
                                 , parseCase
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: TelomareParser UnprocessedParsedTerm
parseChurch = ChurchUP . fromInteger <$> (symbol "$" *> integer)

-- |Parse refinement check.
parseRefinementCheck :: TelomareParser (UnprocessedParsedTerm -> UnprocessedParsedTerm)
parseRefinementCheck = CheckUP <$> (symbol ":" *> parseLongExpr)

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: TelomareParser (String, UnprocessedParsedTerm)
parseAssignment = do
  var <- identifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  scn *> symbol "=" <?> "assignment ="
  expr <- scn *> parseLongExpr <* scn
  case annotation of
    Just annot -> pure (var, annot expr)
    _          -> pure (var, expr)

-- |Parse top level expressions.
parseTopLevel :: TelomareParser UnprocessedParsedTerm
parseTopLevel = parseTopLevelWithPrelude []

-- |Parse top level expressions.
parseTopLevelWithPrelude :: [(String, UnprocessedParsedTerm)]    -- ^Prelude
                         -> TelomareParser UnprocessedParsedTerm
parseTopLevelWithPrelude lst = do
  bindingList <- scn *> many parseAssignment <* eof
  pure $ LetUP (lst <> bindingList) (fromJust $ lookup "main" bindingList)

parseDefinitions :: TelomareParser (UnprocessedParsedTerm -> UnprocessedParsedTerm)
parseDefinitions = do
  bindingList <- scn *> many parseAssignment <* eof
  pure $ LetUP bindingList

-- |Helper function to test parsers without a result.
runTelomareParser_ :: Show a => TelomareParser a -> String -> IO ()
runTelomareParser_ parser str = runTelomareParser parser str >>= print

-- |Helper function to debug parsers without a result.
runTelomareParserWDebug :: Show a => TelomareParser a -> String -> IO ()
runTelomareParserWDebug parser str = runTelomareParser (dbg "debug" parser) str >>= print

-- |Helper function to test Telomare parsers with any result.
runTelomareParser :: Monad m => TelomareParser a -> String -> m a
runTelomareParser parser str =
  case runParser parser "" str of
    Right x -> pure x
    Left e  -> error $ errorBundlePretty e

-- |Helper function to test if parser was successful.
parseSuccessful :: Monad m => TelomareParser a -> String -> m Bool
parseSuccessful parser str =
  case runParser parser "" str of
    Right _ -> pure True
    Left _  -> pure False

parsePrelude :: String -> Either String [(String, UnprocessedParsedTerm)]
parsePrelude str = let result = runParser (scn *> many parseAssignment <* eof) "" str
                    in first errorBundlePretty result

-- |Parse with specified prelude
parseWithPrelude :: [(String, UnprocessedParsedTerm)]   -- ^Prelude
                 -> String                              -- ^Raw string to be parsed
                 -> Either String UnprocessedParsedTerm -- ^Error on Left
parseWithPrelude prelude str = first errorBundlePretty $ runParser (parseTopLevelWithPrelude prelude) "" str
