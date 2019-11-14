{-# LANGUAGE DeriveFunctor #-}
module SIL.Parser where

import Control.Monad.State
import Data.Char
import Data.List (elemIndex)
import Data.Map (Map)
import Debug.Trace
import qualified Data.Map as Map
import SIL (zero, pair, app, check, pleft, pright, varN, ite, lam, completeLam, silTrace, IExpr
           , PrettyPartialType(..))
import SIL.TypeChecker
import Text.Parsec
import Text.Parsec.Indent
import Text.Parsec.Pos
import qualified Text.Parsec.Token as Token

type VarList = [String]
type Term1 = ParserTerm (Either Int String)
type Bindings = Map String Term1

data ParserState = ParserState
  { bound :: Bindings
  }

addBound :: String -> Term1 -> ParserState -> Maybe ParserState
addBound name expr (ParserState bound) = if Map.member name bound
  then Nothing
  else pure $ ParserState (Map.insert name expr bound)

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
  --TODO change to TCompleteLam and test
  in TLam (TLam (inner x))

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
convertPT (TTrace i) = silTrace (convertPT i)
convertPT (TLam c) = lam (convertPT c)
convertPT (TCompleteLam x) = completeLam (convertPT x)
convertPT (TNamedLam n _) = error $ "should be no named lambdas at this stage, name " ++ n
convertPT (TNamedCompleteLam n _) = error $ "should be no named complete lambdas in convertPT, name " ++ n

resolve :: String -> ParserState -> Maybe Term1
resolve name (ParserState bound) = if Map.member name bound
  then Map.lookup name bound
  else Just . TVar . Right $ name

type SILParser a = IndentParser String ParserState a
languageDef = Token.LanguageDef
  { Token.commentStart   = "{-"
  , Token.commentEnd     = "-}"
  , Token.commentLine    = "--"
  , Token.nestedComments = True
  , Token.identStart     = letter
  , Token.identLetter    = alphaNum <|> oneOf "_'"
  , Token.opStart        = Token.opLetter languageDef
  , Token.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedOpNames = ["\\","->", ":", "=", "$", "#"]
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

parseString :: SILParser (ParserTerm v)
parseString = s2t <$> Token.stringLiteral lexer

parseVariable :: SILParser Term1
parseVariable = do
              varName <- identifier
              parserState <- getState
              case resolve varName parserState of
                Nothing -> fail $ concat ["identifier ", varName, " undeclared"]
                Just i -> pure i

parseNumber :: SILParser (ParserTerm v)
parseNumber = (i2t . fromInteger) <$> integer

parsePair :: SILParser Term1
parsePair = withPos $ do
  char '{' <* spaces
  a <- parseLongExpr
  sameOrIndented <* char ',' <* spaces <?> "pair: ,"
  b <- parseLongExpr
  sameOrIndented <* char '}' <* spaces <?> "pair: }"
  return $ TPair a b

parseList :: SILParser Term1
parseList = do
  exprs <- brackets (commaSep parseLongExpr)
  return $ foldr TPair TZero exprs

parseITE :: SILParser Term1
parseITE = withPos $ do
  reserved "if"
  cond <- parseLongExpr
  sameOrIndented <* reserved "then" <?> "ITE: then"
  thenExpr <- parseLongExpr
  sameOrIndented <* reserved "else" <?> "ITE: else"
  elseExpr <- parseLongExpr
  return $ TITE cond thenExpr elseExpr

parsePLeft :: SILParser Term1
parsePLeft = TLeft <$> (reserved "left" *> parseSingleExpr)

parsePRight :: SILParser Term1
parsePRight = TRight <$> (reserved "right" *> parseSingleExpr)

parseTrace :: SILParser Term1
parseTrace = TTrace <$> (reserved "trace" *> parseSingleExpr)

parseSingleExpr :: SILParser Term1
parseSingleExpr = choice [ parseString
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

parseApplied :: SILParser Term1
parseApplied = withPos $ do
  (f:args) <- many1 (sameOrIndented *> parseSingleExpr)
  pure $ foldl TApp f args

parseLongExpr :: SILParser Term1
parseLongExpr = choice [ parseLet
                       , parseITE
                       , parseLambda
                       , parseCompleteLambda
                       , parseApplied
                       ]

parseLambda :: SILParser Term1
parseLambda = do
  reservedOp "\\"
  variables <- many1 identifier
  sameOrIndented <* reservedOp "->" <?> "lambda ->"
  -- TODO make sure lambda names don't collide with bound names
  iexpr <- parseLongExpr
  return $ foldr TNamedLam iexpr variables

parseCompleteLambda :: SILParser Term1
parseCompleteLambda = do
  reservedOp "#"
  variables <- many1 identifier
  sameOrIndented <* reservedOp "->" <?> "lambda ->"
  iexpr <- parseLongExpr
  return . TNamedCompleteLam (head variables) $ foldr TNamedLam iexpr (tail variables)

parseChurch :: SILParser Term1
parseChurch = (i2c . fromInteger) <$> (reservedOp "$" *> integer)

parseRefinementCheck :: SILParser (Term1 -> Term1)
parseRefinementCheck = flip TCheck <$> (reservedOp ":" *> parseLongExpr)

parseAssignment :: SILParser ()
parseAssignment = do
  var <- identifier
  annotation <- optionMaybe parseRefinementCheck
  reservedOp "=" <?> "assignment ="
  expr <- parseLongExpr
  let annoExp = case annotation of
        Just f -> f expr
        _ -> expr
      assign ps = case addBound var annoExp ps of
        Just nps -> nps
        _ -> error $ "shadowing of binding not allowed " ++ var
  modifyState assign

parseLet :: SILParser Term1
parseLet = withPos $ do
  reserved "let"
  initialState <- getState
  manyTill parseAssignment (reserved "in")
  expr <- parseLongExpr
  setState initialState
  pure expr

parseTopLevel :: SILParser Bindings
parseTopLevel = do
  many parseAssignment <* eof
  (ParserState bound) <- getState
  pure bound

debugIndent i = show $ runState i (initialPos "debug")

parsePrelude = parseWithPrelude Map.empty

parseWithPrelude :: Bindings -> String -> Either ParseError Bindings
parseWithPrelude prelude = let startState = ParserState prelude
                           in runIndentParser parseTopLevel startState "sil"

resolveBinding :: String -> Bindings -> Maybe IExpr
resolveBinding name bindings = Map.lookup name bindings >>=
  \b -> convertPT <$> debruijinize [] b

printBindingTypes :: Bindings -> IO ()
printBindingTypes bindings =
  let showType (s, iexpr) = putStrLn $ case inferType iexpr of
        Left pa -> concat [s, ": bad type -- ", show pa]
        Right ft ->concat [s, ": ", show . PrettyPartialType $ ft]
      resolvedBindings = mapM (\(s, b) -> debruijinize [] b >>=
                                (\b -> pure (s, convertPT b))) $ Map.toList bindings
  in resolvedBindings >>= mapM_ showType

parseMain :: Bindings -> String -> Either ParseError IExpr
parseMain prelude s = parseWithPrelude prelude s >>= getMain where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> fail "no main method found"
    Just main -> convertPT <$> debruijinize [] main
