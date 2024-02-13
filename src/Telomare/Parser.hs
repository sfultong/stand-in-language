{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parser where

import Control.Comonad.Cofree (Cofree (..), unwrap)
import Control.Lens.Combinators (Plated (..), makePrisms)
import Control.Lens.Plated (Plated (..))
import Control.Monad (void)
import Control.Monad.State (State)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Functor (($>))
import Data.Functor.Foldable (Base, Recursive (cata), para)
import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.Maybe (fromJust)
import Data.Void (Void)
import Data.Word (Word8)
import qualified System.IO.Strict as Strict
import Telomare (LocTag (..), ParserTerm (..), ParserTermF (..),
                 RecursionPieceFrag, RecursionSimulationPieces (..), Term1 (..),
                 Term2 (..), Term3 (..), UnsizedRecursionToken, appF, clamF,
                 deferF, forget, lamF, nextBreakToken, unsizedRecursionWrapper,
                 varNF)
import Telomare.TypeChecker (typeCheck)
import Text.Megaparsec (MonadParsec (eof, notFollowedBy, try), Parsec, Pos,
                        PosState (pstateSourcePos),
                        SourcePos (sourceColumn, sourceLine),
                        State (statePosState), between, choice,
                        errorBundlePretty, getParserState, many, manyTill,
                        optional, runParser, sepBy, some, unPos, (<?>), (<|>))
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Pos (Pos)
import Text.Read (readMaybe)
import Text.Show.Deriving (deriveShow1)
-- import Data.Fix hiding (cata)
-- import Control.Comonad (Comonad(..))

-- |AST for patterns in `case` expressions
data Pattern
  = PatternVar String
  | PatternInt Int
  | PatternString String
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
deriveShow1 ''UnprocessedParsedTermF

type AnnotatedUPT = Cofree UnprocessedParsedTermF LocTag

newtype PrettyPattern = PrettyPattern Pattern

instance Show PrettyPattern where
  show = \case
    (PrettyPattern (PatternInt x)) -> show x
    (PrettyPattern (PatternVar x)) -> x
    (PrettyPattern (PatternString x)) ->  show x
    (PrettyPattern (PatternPair x y)) -> "(" <> (show . PrettyPattern $ x) <> ", " <> (show . PrettyPattern $ y) <> ")"
    (PrettyPattern PatternIgnore) -> "_"

newtype PrettyUPT = PrettyUPT UnprocessedParsedTerm

instance Show PrettyUPT where
  show (PrettyUPT upt) = cata alg upt where
    indentSansFirstLine :: Int -> String -> String
    indentSansFirstLine i x = removeLastNewLine res where
      res = unlines ((\(s:ns) -> s:((indent i <>) <$> ns)) (lines x))
      indent 0 = []
      indent n = ' ' : indent (n - 1)
      removeLastNewLine str =
        case reverse str of
          '\n' : rest -> reverse rest
          x           -> str
    alg :: Base UnprocessedParsedTerm String -> String
    alg = \case
      IntUPF i -> show i
      VarUPF str -> str
      StringUPF str -> show str
      PairUPF x y -> if length (lines (x <> y)) > 1
                       then "( " <> indentSansFirstLine 2 x <> "\n" <>
                            ", " <> indentSansFirstLine 2 y <> "\n" <>
                            ")"
                       else "(" <> x <> ", " <> y <>")"
      (ITEUPF x y z) -> "if " <> indentSansFirstLine 3 x <> "\n" <>
                          "  then " <> indentSansFirstLine 7 y <> "\n" <>
                          "  else " <> indentSansFirstLine 7 z
      (LetUPF ls x) ->
        "let " <> indentSansFirstLine 4 (unlines (assignList <$> ls)) <> "\n" <>
        "in " <> indentSansFirstLine 3 x
          where
            assignList :: (String, String) -> String
            assignList (str, upt) = str <> " = " <> indentSansFirstLine (3 + length str) upt
      (ListUPF []) -> "[]"
      (ListUPF ls) ->
        "[" <> removeFirstComma (unlines (indentSansFirstLine 2 . (", " <>) <$> ls)) <>
        "]"
          where
            removeFirstComma = \case
              (',':str) -> str
              _         -> error "removeFirstComma: input does not start with a comma"
      (AppUPF x y) -> "(" <> x <> " " <> "(" <> y <> ")" <>")"
      (LamUPF str y) -> "\\ " <> str <> " -> " <> indentSansFirstLine (6 + length str) y
      (ChurchUPF x) -> "$" <> show x
      (LeftUPF x) -> "left (" <> indentSansFirstLine 6 x <> ")"
      (RightUPF x) -> "right (" <> indentSansFirstLine 7 x <> ")"
      (TraceUPF x) -> "trace (" <> indentSansFirstLine 7 x <> ")"
      (UnsizedRecursionUPF x y z) -> "{ " <> indentSansFirstLine 2 x <>
                                     ", " <> indentSansFirstLine 2 y <>
                                     ", " <> indentSansFirstLine 2 z <>
                                     "}"
      (HashUPF x) -> "# " <> indentSansFirstLine 2 x
      (CaseUPF x ls) -> "case " <> x <> " of\n" <>
                        "  " <> indentSansFirstLine 2 (unlines ((\(p, r) -> indentSansFirstLine 2 (show (PrettyPattern p) <> " -> " <> r)) <$> ls))
      (CheckUPF x y) -> if length (lines (x <> y)) > 1
                          then "(" <> indentSansFirstLine 2 y <> " : " <> "\n" <>
                               "    " <> indentSansFirstLine 4 y <> ")"
                          else "(" <> y <> " : " <> x <> ")"

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
    UnsizedRecursionUP x y z -> UnsizedRecursionUP <$> f x <*> f y <*> f z
    x           -> pure x

-- |TelomareParser :: * -> *
type TelomareParser = Parsec Void String


-- parseVariable :: TelomareParser UnprocessedParsedTerm
-- parseVariable = VarUP <$> identifier
-- |Parse a variable.
parseVariable :: TelomareParser AnnotatedUPT
parseVariable = do
  s <- getParserState
  let line = unPos . sourceLine . pstateSourcePos . statePosState $ s
      column = unPos . sourceColumn . pstateSourcePos . statePosState $ s
  (\str -> Loc line column :< VarUPF str) <$> identifier


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

getLineColumn = do
  s <- getParserState
  let line = unPos . sourceLine . pstateSourcePos . statePosState $ s
      column = unPos . sourceColumn . pstateSourcePos . statePosState $ s
  pure $ Loc line column

  -- (\str -> (line, column) :< VarUPF str) <$> identifier

-- |Parse string literal.
parseString :: TelomareParser AnnotatedUPT
parseString = do
  x <- getLineColumn
  (\str -> x :< StringUPF str) <$> (char '"' >> manyTill L.charLiteral (char '"' <* sc))

-- |Parse number (Integer).
parseNumber :: TelomareParser AnnotatedUPT
parseNumber = do
  x <- getLineColumn
  (\i -> x :< (IntUPF . fromInteger $ i)) <$> integer

-- |Parse a pair.
parsePair :: TelomareParser AnnotatedUPT
parsePair = parens $ do
  x <- getLineColumn
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  pure $ x :< PairUPF a b

-- |Parse unsized recursion triple
parseUnsizedRecursion :: TelomareParser AnnotatedUPT
parseUnsizedRecursion = curlies $ do
  x <- getLineColumn
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  _ <- symbol "," <* scn
  c <- parseLongExpr <* scn
  pure $ x :< UnsizedRecursionUPF a b c

-- |Parse a list.
parseList :: TelomareParser AnnotatedUPT
parseList = do
  x <- getLineColumn
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  pure $ x :< ListUPF exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: TelomareParser AnnotatedUPT
parseITE = do
  x <- getLineColumn
  reserved "if" <* scn
  cond <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "then" <* scn
  thenExpr <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "else" <* scn
  elseExpr <- parseLongExpr <* scn
  pure $ x :< ITEUPF cond thenExpr elseExpr

parseHash :: TelomareParser AnnotatedUPT
parseHash = do
  x <- getLineColumn
  symbol "#" <* scn
  upt <- parseSingleExpr
  pure $ x :< HashUPF upt

parseCase :: TelomareParser AnnotatedUPT
parseCase = do
  x <- getLineColumn
  reserved "case" <* scn
  iexpr <- parseLongExpr <* scn
  reserved "of" <* scn
  lpc <- some $ try parseSingleCase <* scn
  pure $ x :< CaseUPF iexpr lpc

parseSingleCase :: TelomareParser (Pattern, AnnotatedUPT)
parseSingleCase = do
  p <- parsePattern <* scn
  reserved "->" <* scn
  c <- parseLongExpr <* scn
  pure (p, c)

parsePattern :: TelomareParser Pattern
parsePattern = choice $ try <$> [ parsePatternIgnore
                                , parsePatternVar
                                , parsePatternString
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

parsePatternString :: TelomareParser Pattern
parsePatternString = PatternString <$> (char '"' >> manyTill L.charLiteral (char '"'))

parsePatternVar :: TelomareParser Pattern
parsePatternVar = PatternVar <$> identifier

parsePatternIgnore :: TelomareParser Pattern
parsePatternIgnore = symbol "_" >> pure PatternIgnore

-- |Parse a single expression.
parseSingleExpr :: TelomareParser AnnotatedUPT
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
parseApplied :: TelomareParser AnnotatedUPT
parseApplied = do
  x <- getLineColumn
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) ->
      pure $ foldl (\a b -> x :< AppUPF a b) f args
    _ -> fail "expected expression"

-- |Parse lambda expression.
parseLambda :: TelomareParser AnnotatedUPT
parseLambda = do
  x <- getLineColumn
  symbol "\\" <* scn
  variables <- some identifier <* scn
  symbol "->" <* scn
  -- TODO make sure lambda names don't collide with bound names
  term1expr <- parseLongExpr <* scn
  pure $ foldr (\str upt -> x :< LamUPF str upt) term1expr variables

-- |Parser that fails if indent level is not `pos`.
parseSameLvl :: Pos -> TelomareParser a -> TelomareParser a
parseSameLvl pos parser = do
  lvl <- L.indentLevel
  if pos == lvl then parser else fail "Expected same indentation."

-- |Parse let expression.
parseLet :: TelomareParser AnnotatedUPT
parseLet = do
  x <- getLineColumn
  reserved "let" <* scn
  lvl <- L.indentLevel
  bindingsList <- manyTill (parseSameLvl lvl parseAssignment) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  pure $ x :< LetUPF bindingsList expr

-- |Parse long expression.
parseLongExpr :: TelomareParser AnnotatedUPT
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseApplied
                                 , parseCase
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: TelomareParser AnnotatedUPT
parseChurch = do
  x <- getLineColumn
  (\upt -> x :< ChurchUPF upt) . fromInteger <$> (symbol "$" *> integer)

-- |Parse refinement check.
parseRefinementCheck :: TelomareParser (AnnotatedUPT -> AnnotatedUPT)
parseRefinementCheck = do
  x <- getLineColumn
  (\a b -> x :< CheckUPF a b) <$> (symbol ":" *> parseLongExpr)

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: TelomareParser (String, AnnotatedUPT)
parseAssignment = do
  var <- identifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  scn *> symbol "=" <?> "assignment ="
  expr <- scn *> parseLongExpr <* scn
  case annotation of
    Just annot -> pure (var, annot expr)
    _          -> pure (var, expr)

-- |Parse top level expressions.
parseTopLevel :: TelomareParser AnnotatedUPT
parseTopLevel = parseTopLevelWithPrelude []

-- |Parse top level expressions.
parseTopLevelWithPrelude :: [(String, AnnotatedUPT)]    -- ^Prelude
                         -> TelomareParser AnnotatedUPT
parseTopLevelWithPrelude lst = do
  x <- getLineColumn
  bindingList <- scn *> many parseAssignment <* eof
  pure $ x :< LetUPF (lst <> bindingList) (fromJust $ lookup "main" bindingList)

parseDefinitions :: TelomareParser (AnnotatedUPT -> AnnotatedUPT)
parseDefinitions = do
  x <- getLineColumn
  bindingList <- scn *> many parseAssignment <* eof
  pure $ \y -> x :< LetUPF bindingList y

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

parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePrelude str = let result = runParser (scn *> many parseAssignment <* eof) "" str
                    in first errorBundlePretty result

-- |Parse with specified prelude
parseWithPrelude :: [(String, AnnotatedUPT)]   -- ^Prelude
                 -> String                              -- ^Raw string to be parsed
                 -> Either String AnnotatedUPT -- ^Error on Left
parseWithPrelude prelude str = first errorBundlePretty $ runParser (parseTopLevelWithPrelude prelude) "" str
