{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SIL.Parser where

import Control.Monad.State
import Data.Char
import Data.List (elemIndex)
import Data.Map (Map, fromList)
import Debug.Trace
import qualified Data.Map as Map
import SIL (zero, pair, app, check, pleft, pright, varN, ite, lam, completeLam, IExpr(Trace), PrettyPartialType(..))
import SIL.TypeChecker
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Pos
import Data.Void

type VarList = [String]
type Term1 = ParserTerm (Either Int String)
type Bindings = Map String Term1

-- |SILParser :: * -> *
type SILParser = StateT ParserState (Parsec Void String)

newtype ErrorString = MkES { getErrorString :: String }

data ParserState = ParserState
  { bound :: Bindings
  } deriving Show

addBound :: String -> Term1 -> ParserState -> Maybe ParserState
addBound name expr (ParserState bound) = if Map.member name bound
  then Nothing
  else pure $ ParserState (Map.insert name expr bound)

{- |
 On the difference between TLam and TCompleteLam:
 The former should only be used when the inner grammar explicitly references external variables.
 Eventually these two forms should be merged in the parser's grammar and the determination of which form to use
 should be automatic.
-}
data ParserTerm v
  = TZero
  | TPair (ParserTerm v) (ParserTerm v)
  | TVar v
  | TApp (ParserTerm v) (ParserTerm v)
  | TCheck (ParserTerm v) (ParserTerm v)
  | TITE (ParserTerm v) (ParserTerm v) (ParserTerm v)
  | TLeft (ParserTerm v)
  | TRight (ParserTerm v)
  | TTrace (ParserTerm v)
  | TLam (ParserTerm v)
  | TCompleteLam (ParserTerm v)
  | TNamedLam String (ParserTerm v)
  | TNamedCompleteLam String (ParserTerm v)
  deriving (Eq, Show, Ord, Functor)

i2t :: Int -> ParserTerm v
i2t 0 = TZero
i2t n = TPair (i2t (n - 1)) TZero

ints2t :: [Int] -> ParserTerm v
ints2t = foldr (\i t -> TPair (i2t i) t) TZero

s2t :: String -> ParserTerm v
s2t = ints2t . map ord

i2c :: Int -> Term1
i2c x =
  let inner 0 = TVar $ Left 0
      inner x = TApp (TVar $ Left 1) (inner $ x - 1)
  in TCompleteLam (TLam (inner x))

debruijinize :: Monad m => VarList -> Term1 -> m (ParserTerm Int)
debruijinize _ TZero = pure TZero
debruijinize vl (TPair a b) = TPair <$> debruijinize vl a <*> debruijinize vl b
debruijinize _ (TVar (Left i)) = pure $ TVar i
debruijinize vl (TVar (Right n)) = case elemIndex n vl of
  Just i -> pure $ TVar i
  Nothing -> fail $ "undefined identifier " ++ n
debruijinize vl (TApp i c) = TApp <$> debruijinize vl i <*> debruijinize vl c
debruijinize vl (TCheck c tc) = TCheck <$> debruijinize vl c <*> debruijinize vl tc
debruijinize vl (TITE i t e) = TITE <$> debruijinize vl i <*> debruijinize vl t
  <*> debruijinize vl e
debruijinize vl (TLeft x) = TLeft <$> debruijinize vl x
debruijinize vl (TRight x) = TRight <$> debruijinize vl x
debruijinize vl (TTrace x) = TTrace <$> debruijinize vl x
debruijinize vl (TLam x) = TLam <$> debruijinize ("-- dummy" : vl) x
debruijinize vl (TCompleteLam x) = TCompleteLam <$> debruijinize ("-- dummyC" : vl) x
debruijinize vl (TNamedLam n l) = TLam <$> debruijinize (n : vl) l
debruijinize vl (TNamedCompleteLam n l) = TCompleteLam <$> debruijinize (n : vl) l

convertPT :: ParserTerm Int -> IExpr
convertPT TZero = zero
convertPT (TPair a b) = pair (convertPT a) (convertPT b)
convertPT (TVar n) = varN n
convertPT (TApp i c) = app (convertPT i) (convertPT c)
-- note preft hack to discard environment from normal lambda format
convertPT (TCheck c tc) = check (convertPT c) (convertPT tc)
convertPT (TITE i t e) = ite (convertPT i) (convertPT t) (convertPT e)
convertPT (TLeft i) = pleft (convertPT i)
convertPT (TRight i) = pright (convertPT i)
convertPT (TTrace i) = Trace (convertPT i)
convertPT (TLam c) = lam (convertPT c)
convertPT (TCompleteLam x) = completeLam (convertPT x)
convertPT (TNamedLam n _) = error $ "should be no named lambdas at this stage, name " ++ n
convertPT (TNamedCompleteLam n _) = error $ "should be no named complete lambdas in convertPT, name " ++ n

resolve :: String -> ParserState -> Maybe Term1
resolve name (ParserState bound) = if Map.member name bound
                                   then Map.lookup name bound
                                   else Just . TVar . Right $ name

-- |Line comments start with "--".
lineComment :: SILParser ()
lineComment = L.skipLineComment "--"

-- |A block comment starts with "{-" and ends at "-}".
-- Nested block comments are also supported.
blockComment = L.skipBlockCommentNested "{-" "-}"

-- |Space Consumer: Whitespace and comment parser that does not consume new-lines.
sc :: SILParser ()
sc = L.space
  (void $ some (char ' ' <|> char '\t'))
  lineComment
  blockComment

-- |Space Consumer: Whitespace and comment parser that does consume new-lines.
scn :: SILParser ()
scn = L.space space1 lineComment blockComment

-- |This is a wrapper for lexemes that picks up all trailing white space
-- using sc
lexeme :: SILParser a -> SILParser a
lexeme = L.lexeme sc

-- |A parser that matches given text using string internally and then similarly
-- picks up all trailing white space.
symbol :: String -> SILParser String
symbol = L.symbol sc

-- |This is to parse reserved words. 
reserved :: String -> SILParser ()
reserved w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

-- |List of reserved words
rws :: [String]
rws = ["let", "in", "right", "left", "trace", "if", "then", "else"]

-- |Variable identifiers can consist of alphanumeric characters, underscore,
-- and must start with an English alphabet letter
identifier :: SILParser String
identifier = (lexeme . try) $ p >>= check
    where
      p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_' <?> "variable")
      check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

-- |Parser for parenthesis.
parens :: SILParser a -> SILParser a
parens = between (symbol "(") (symbol ")")

-- |Parser for brackets.
brackets :: SILParser a -> SILParser a
brackets = between (symbol "[") (symbol "]")

-- |Parser for braces.
braces :: SILParser a -> SILParser a
braces = between (symbol "{") (symbol "}")

-- |Comma sepparated SILParser that will be useful for lists
commaSep :: SILParser a -> SILParser [a]
commaSep p = p `sepBy` (symbol ",")

-- |Integer SILParser used by `parseNumber` and `parseChurch`
integer :: SILParser Integer
integer = toInteger <$> lexeme L.decimal

-- |Parse string literal.
parseString :: SILParser (ParserTerm v)
parseString = fmap s2t $ char '\"' *> manyTill L.charLiteral (char '\"')

-- |Parse a variable.
parseVariable :: SILParser Term1
parseVariable = do
  varName <- identifier
  parseState <- get
  case resolve varName parseState of
    Nothing -> fail $ concat  ["identifier ", varName, " undeclared"]
    Just i -> pure i

-- |Prarse number (Integer).
parseNumber :: SILParser (ParserTerm v)
parseNumber = (i2t . fromInteger) <$> integer

-- |Parse a pair.
parsePair :: SILParser Term1
parsePair = braces $ do
  scn
  a <- parseLongExpr
  scn
  symbol ","
  scn
  b <- parseLongExpr
  scn
  return $ TPair a b

-- |Parse a list.
parseList :: SILParser Term1
parseList = do
  exprs <- brackets (commaSep parseLongExpr)
  return $ foldr TPair TZero exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: SILParser Term1
parseITE = do
  -- posIf <- L.indentLevel
  reserved "if"
  scn
  cond <- parseLongExpr
  scn
  -- posThen <- L.indentLevel
  reserved "then"
  scn
  thenExpr <- parseLongExpr
  scn
  -- posElse <- L.indentLevel
  reserved "else"
  scn
  elseExpr <- parseLongExpr
  scn
  return $ TITE cond thenExpr elseExpr
  -- case posIf > posThen of
  --   True -> L.incorrectIndent GT posIf posThen -- This should be GT or EQ
  --   False -> case posIf > posElse of
  --     True -> L.incorrectIndent GT posIf posElse -- This should be GT or EQ
  --     False -> return $ TITE cond thenExpr elseExpr

-- |Parse left.
parsePLeft :: SILParser Term1
parsePLeft = TLeft <$> (reserved "left" *> parseSingleExpr)

-- |Parse right.
parsePRight :: SILParser Term1
parsePRight = TRight <$> (reserved "right" *> parseSingleExpr)

-- |Parse trace.
parseTrace :: SILParser Term1
parseTrace = TTrace <$> (reserved "trace" *> parseSingleExpr)

-- |Parse a single expression.
parseSingleExpr :: SILParser Term1
parseSingleExpr = choice $ try <$> [ parseString
                                   , parseNumber
                                   , parsePair
                                   , parseList
                                   , parsePLeft
                                   , parsePRight
                                   , parseTrace
                                   , parseChurch
                                   , parseVariable
                                   , parens parseLongExpr
                                   ]

-- |Parse application of functions.
parseApplied :: SILParser Term1
parseApplied = do
  (f:args) <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc' <* scn
  pure $ foldl TApp f args

-- |Parse lambda expression.
parseLambda :: SILParser Term1
parseLambda = do
  symbol "\\"
  scn
  variables <- some identifier
  scn
  symbol "->"
  scn
  -- TODO make sure lambda names don't collide with bound names
  iexpr <- parseLongExpr
  return $ foldr TNamedLam iexpr variables

-- |Parse complete lambda expression.
parseCompleteLambda :: SILParser Term1
parseCompleteLambda = do
  symbol "#"
  variables <- some identifier
  scn
  symbol "->"
  scn
  iexpr <- parseLongExpr
  scn
  return . TNamedCompleteLam (head variables) $ foldr TNamedLam iexpr (tail variables)

-- |Parse let expression.
parseLet :: SILParser Term1
parseLet = do
  reserved "let"
  initialState <- get
  scn
  manyTill parseAssignment (reserved "in")
  scn
  expr <- parseLongExpr
  scn
  put initialState
  pure expr

-- |Parse long expression.
parseLongExpr :: SILParser Term1
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseCompleteLambda
                                 , parseApplied
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace sparation).
parseChurch :: SILParser Term1
parseChurch = (i2c . fromInteger) <$> (symbol "$" *> integer)

-- |Parse refinement check.
parseRefinementCheck :: SILParser (Term1 -> Term1)
parseRefinementCheck = flip TCheck <$> (symbol ":" *> parseLongExpr)

-- |Parse assignment.
parseAssignment :: SILParser ()
parseAssignment = do
  var <- identifier
  scn
  annotation <- optional parseRefinementCheck
  reserved "=" <?> "assignment ="
  expr <- parseLongExpr
  scn
  let annoExp = case annotation of
        Just f -> f expr
        _ -> expr
      assign ps = case addBound var annoExp ps of
        Just nps -> nps
        _ -> error $ "shadowing of binding not allowed " ++ var
  modify assign

-- |Parse top level expressions.
parseTopLevel :: SILParser Bindings
parseTopLevel = do
  many parseAssignment <* eof
  (ParserState bound) <- get
  pure bound

-- |Debug helper.
debugIndent i = show $ runState i (initialPos "debug")

-- |Helper function to test parsers without a result.
runSILParser_ :: Show a => SILParser a -> String -> IO ()
runSILParser_ parser str = do
  let p            = runStateT parser $ ParserState (Map.empty)
  case runParser p "" str of
    Right (a, s) -> do
      putStrLn ("Result:      " ++ show a)
      putStrLn ("Final state: " ++ show s)
    Left e -> putStr (errorBundlePretty e)

-- |Helper function to debug parsers without a result.
runSILParserWDebug_ :: Show a => SILParser a -> String -> IO ()
runSILParserWDebug_ parser str = do
  let p            = runStateT parser $ ParserState (Map.empty)
  case runParser (dbg "debug" p) "" str of
    Right (a, s) -> do
      putStrLn ("Result:      " ++ show a)
      putStrLn ("Final state: " ++ show s)
    Left e -> putStr (errorBundlePretty e)

-- |Helper function to test parsers with parsing result.
runSILParser :: Show a => SILParser a -> String -> IO String
runSILParser parser str = do
  let p            = runStateT parser $ ParserState (Map.empty)
  case runParser p "" str of
    Right (a, s) -> return $ show a
    Left e -> return $ errorBundlePretty e

-- |Parse with specified prelude.
parseWithPrelude :: Bindings -> String -> Either ErrorString Bindings
parseWithPrelude prelude str = let startState = ParserState prelude
                                   p          = runStateT parseTopLevel startState
                                   eitherEB str = case runParser p "" str of
                                     Right (a, s) -> Right a
                                     Left x       -> Left $ MkES $ errorBundlePretty x
                               in eitherEB str

-- |Parse prelude.
parsePrelude = parseWithPrelude Map.empty

-- |Resolve bindings (useful for Prelude).
resolveBinding :: String -> Bindings -> Maybe IExpr
resolveBinding name bindings = Map.lookup name bindings >>=
  \b -> convertPT <$> debruijinize [] b

-- |Helper to print binding types.
printBindingTypes :: Bindings -> IO ()
printBindingTypes bindings =
  let showType (s, iexpr) = putStrLn $ case inferType iexpr of
        Left pa -> concat [s, ": bad type -- ", show pa]
        Right ft ->concat [s, ": ", show . PrettyPartialType $ ft]
      resolvedBindings = mapM (\(s, b) -> debruijinize [] b >>=
                                (\b -> pure (s, convertPT b))) $ Map.toList bindings
  in resolvedBindings >>= mapM_ showType

-- |Parses main as a top level binding.
parseMain :: Bindings -> String -> Either ErrorString IExpr
parseMain prelude s = parseWithPrelude prelude s >>= getMain where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> fail "no main method found"
    Just main -> convertPT <$> debruijinize [] main

