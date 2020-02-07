{-# LANGUAGE DeriveFunctor #-}
module SIL.ParserMegaparsec where

import Control.Monad.State
import Data.Char
import Data.List (elemIndex)
import Data.Map (Map)
import Debug.Trace
import qualified Data.Map as Map
import SIL (zero, pair, app, check, pleft, pright, varN, ite, lam, completeLam, IExpr(Trace), PrettyPartialType(..))
import SIL.TypeChecker

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void


-- import qualified Text.Parsec as RM
-- import qualified Text.Parsec.Indent as RM
-- import qualified Text.Parsec.Pos as RM
-- import qualified Text.Parsec.Token as Token

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

{-
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

-- TODO: Comment is useful to explicitly see what is being refactored
--       When the refactor is completed, remove comment.
-- type SILParser a = RM.IndentParser String ParserState a

-- |SILParser :: * -> *
type SILParser = Parsec Void String

-- TODO: Comment is useful to explicitly see what is being refactored
--       When the refactor is completed, remove comment.
-- languageDef = Token.LanguageDef
--   { Token.commentStart   = "{-"
--   , Token.commentEnd     = "-}"
--   , Token.commentLine    = "--"
--   , Token.nestedComments = True
--   , Token.identStart     = RM.letter                                                         TODO: Still missing
--   , Token.identLetter    = RM.alphaNum RM.<|> RM.oneOf "_'"                                  TODO: Still missing
--   , Token.opStart        = Token.opLetter languageDef                                        TODO: Still missing
--   , Token.opLetter       = RM.oneOf ":!#$%&*+./<=>?@\\^|-~"                                  TODO: Still missing
--   , Token.reservedOpNames = ["\\","->", ":", "=", "$", "#"]                                  TODO: Still missing
--   , Token.reservedNames = ["let", "in", "right", "left", "trace", "if", "then", "else"]      TODO: Still missing
--   , Token.caseSensitive  = True                                                              TODO: Still missing
--   }

-- |Line comments start with "--".
lineComment :: SILParser ()
lineComment = L.skipLineComment "--"

-- |A block comment starts with "{-" and ends at "-}".
blockComment = L.skipBlockCommentNested "{-" "-}"

-- |Space parser that does not consume new-lines.
sc :: SILParser ()
sc = L.space
  space1
  lineComment
  blockComment

-- TODO: This is surely wrong. FIX.
-- |Variable identifiers can start with a letter and end with
-- an alphanumeric character or underscore (i.e. '_').
pVariable :: SILParser ParserTerm
pVariable = TVar <$> lexeme
  ((:) <$> letterChar <*> many alphaNumChar <?> "variable")

-- pInteger :: Parser Expr
-- pInteger = Int <$> lexeme L.decimal

-- parens :: Parser a -> Parser a
-- parens = between (symbol "(") (symbol ")")

-- pTerm :: Parser Expr
-- pTerm = choice
--   [ parens pExpr
--   , pVariable
--   , pInteger
--   ]

-- pExpr :: Parser Expr
-- pExpr = makeExprParser pTerm operatorTable


------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
-- TODO: Pass everything from bellow to above with Parsec refactored to MegaParsec
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

-- lexer = Token.makeTokenParser languageDef
-- identifier = Token.identifier lexer -- parses an identifier
-- reserved   = Token.reserved   lexer -- parses a reserved name
-- reservedOp = Token.reservedOp lexer -- parses an operator
-- parens     = Token.parens     lexer -- parses surrounding parenthesis:
-- brackets   = Token.brackets   lexer
-- braces     = Token.braces     lexer
-- commaSep   = Token.commaSep   lexer
-- commaSep1  = Token.commaSep1  lexer
-- integer    = Token.integer    lexer

-- parseString :: SILParser (ParserTerm v)
-- parseString = s2t <$> Token.stringLiteral lexer

-- parseVariable :: SILParser Term1
-- parseVariable = do
--               varName <- identifier
--               parserState <- RM.getState
--               case resolve varName parserState of
--                 Nothing -> fail $ concat ["identifier ", varName, " undeclared"]
--                 Just i -> pure i

-- parseNumber :: SILParser (ParserTerm v)
-- parseNumber = (i2t . fromInteger) <$> integer

-- parsePair :: SILParser Term1
-- parsePair = RM.withPos $ do
--   RM.char '{' <* RM.spaces
--   a <- parseLongExpr
--   RM.sameOrIndented <* RM.char ',' <* RM.spaces RM.<?> "pair: ,"
--   b <- parseLongExpr
--   RM.sameOrIndented <* RM.char '}' <* RM.spaces RM.<?> "pair: }"
--   return $ TPair a b

-- parseList :: SILParser Term1
-- parseList = do
--   exprs <- brackets (commaSep parseLongExpr)
--   return $ foldr TPair TZero exprs

-- parseITE :: SILParser Term1
-- parseITE = RM.withPos $ do
--   reserved "if"
--   cond <- parseLongExpr
--   RM.sameOrIndented <* reserved "then" RM.<?> "ITE: then"
--   thenExpr <- parseLongExpr
--   RM.sameOrIndented <* reserved "else" RM.<?> "ITE: else"
--   elseExpr <- parseLongExpr
--   return $ TITE cond thenExpr elseExpr

-- parsePLeft :: SILParser Term1
-- parsePLeft = TLeft <$> (reserved "left" *> parseSingleExpr)

-- parsePRight :: SILParser Term1
-- parsePRight = TRight <$> (reserved "right" *> parseSingleExpr)

-- parseTrace :: SILParser Term1
-- parseTrace = TTrace <$> (reserved "trace" *> parseSingleExpr)

-- parseSingleExpr :: SILParser Term1
-- parseSingleExpr = RM.choice [ parseString
--                          , parseNumber
--                          , parsePair
--                          , parseList
--                          , parsePLeft
--                          , parsePRight
--                          , parseTrace
--                          , parseChurch
--                          , parseVariable
--                          , parens parseLongExpr
--                          ]

-- parseApplied :: SILParser Term1
-- parseApplied = RM.withPos $ do
--   (f:args) <- RM.many1 (RM.sameOrIndented *> parseSingleExpr)
--   pure $ foldl TApp f args

-- parseLongExpr :: SILParser Term1
-- parseLongExpr = RM.choice [ parseLet
--                        , parseITE
--                        , parseLambda
--                        , parseCompleteLambda
--                        , parseApplied
--                        ]

-- parseLambda :: SILParser Term1
-- parseLambda = do
--   reservedOp "\\"
--   variables <- RM.many1 identifier
--   RM.sameOrIndented <* reservedOp "->" RM.<?> "lambda ->"
--   -- TODO make sure lambda names don't collide with bound names
--   iexpr <- parseLongExpr
--   return $ foldr TNamedLam iexpr variables

-- parseCompleteLambda :: SILParser Term1
-- parseCompleteLambda = do
--   reservedOp "#"
--   variables <- RM.many1 identifier
--   RM.sameOrIndented <* reservedOp "->" RM.<?> "lambda ->"
--   iexpr <- parseLongExpr
--   return . TNamedCompleteLam (head variables) $ foldr TNamedLam iexpr (tail variables)

-- parseChurch :: SILParser Term1
-- parseChurch = (i2c . fromInteger) <$> (reservedOp "$" *> integer)

-- parseRefinementCheck :: SILParser (Term1 -> Term1)
-- parseRefinementCheck = flip TCheck <$> (reservedOp ":" *> parseLongExpr)

-- parseAssignment :: SILParser ()
-- parseAssignment = do
--   var <- identifier
--   annotation <- RM.optionMaybe parseRefinementCheck
--   reservedOp "=" RM.<?> "assignment ="
--   expr <- parseLongExpr
--   let annoExp = case annotation of
--         Just f -> f expr
--         _ -> expr
--       assign ps = case addBound var annoExp ps of
--         Just nps -> nps
--         _ -> error $ "shadowing of binding not allowed " ++ var
--   RM.modifyState assign

-- parseLet :: SILParser Term1
-- parseLet = RM.withPos $ do
--   reserved "let"
--   initialState <- RM.getState
--   RM.manyTill parseAssignment (reserved "in")
--   expr <- parseLongExpr
--   RM.setState initialState
--   pure expr

-- parseTopLevel :: SILParser Bindings
-- parseTopLevel = do
--   RM.many parseAssignment <* RM.eof
--   (ParserState bound) <- RM.getState
--   pure bound

-- debugIndent i = show $ runState i (RM.initialPos "debug")

-- parsePrelude = parseWithPrelude Map.empty

-- parseWithPrelude :: Bindings -> String -> Either RM.ParseError Bindings
-- parseWithPrelude prelude = let startState = ParserState prelude
--                            in RM.runIndentParser parseTopLevel startState "sil"

-- resolveBinding :: String -> Bindings -> Maybe IExpr
-- resolveBinding name bindings = Map.lookup name bindings >>=
--   \b -> convertPT <$> debruijinize [] b

-- printBindingTypes :: Bindings -> IO ()
-- printBindingTypes bindings =
--   let showType (s, iexpr) = putStrLn $ case inferType iexpr of
--         Left pa -> concat [s, ": bad type -- ", show pa]
--         Right ft ->concat [s, ": ", show . PrettyPartialType $ ft]
--       resolvedBindings = mapM (\(s, b) -> debruijinize [] b >>=
--                                 (\b -> pure (s, convertPT b))) $ Map.toList bindings
--   in resolvedBindings >>= mapM_ showType

-- parseMain :: Bindings -> String -> Either RM.ParseError IExpr
-- parseMain prelude s = parseWithPrelude prelude s >>= getMain where
--   getMain bound = case Map.lookup "main" bound of
--     Nothing -> fail "no main method found"
--     Just main -> convertPT <$> debruijinize [] main
