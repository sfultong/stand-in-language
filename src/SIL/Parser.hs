{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module SIL.Parser where

import Control.Monad
import Data.Char
import Data.List (elemIndex)
import Data.Map (Map, fromList)
import Debug.Trace
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Pos
import Data.Void
import qualified Control.Monad.State as State
import qualified Data.Map as Map

import Data.Functor.Foldable

import SIL
import SIL.TypeChecker

type VarList = [String]
type Bindings = Map String Term1

-- |SILParser :: * -> *
type SILParser = State.StateT ParserState (Parsec Void String)

newtype ErrorString = MkES { getErrorString :: String } deriving Show

data ParserState = ParserState
  { bound :: Bindings
  } deriving Show

addBound :: String -> Term1 -> ParserState -> Maybe ParserState
addBound name expr (ParserState bound) = if Map.member name bound
  then Nothing
  else pure $ ParserState (Map.insert name expr bound)

i2t :: Int -> ParserTerm l x v
i2t 0 = tzero
i2t n = tpair (i2t (n - 1)) tzero

ints2t :: [Int] -> ParserTerm l x v
ints2t = foldr (\i t -> tpair (i2t i) t) tzero

s2t :: String -> ParserTerm l x v
s2t = ints2t . map ord

i2c :: Int -> Term1
i2c x =
  let inner 0 = tvar $ Left 0
      inner x = tapp (tvar $ Left 1) (inner $ x - 1)
  in tlam (Closed (Left ())) (tlam (Open (Left ())) (inner x))

debruijinize :: Monad m => VarList -> Term1 -> m Term2
debruijinize _ (Fix (TZero)) = pure $ Fix TZero
debruijinize vl (Fix (TPair a b)) = tpair <$> debruijinize vl a <*> debruijinize vl b
debruijinize _ (Fix (TVar (Left i))) = pure $ tvar i
debruijinize vl (Fix (TVar (Right n))) = case elemIndex n vl of
  Just i -> pure $ tvar i
  Nothing -> fail $ "undefined identifier " ++ n
debruijinize vl (Fix (TApp i c)) = tapp <$> debruijinize vl i <*> debruijinize vl c
debruijinize vl (Fix (TCheck c tc)) = tcheck <$> debruijinize vl c <*> debruijinize vl tc
debruijinize vl (Fix (TITE i t e)) = tite <$> debruijinize vl i <*> debruijinize vl t
  <*> debruijinize vl e
debruijinize vl (Fix (TLeft x)) = tleft <$> debruijinize vl x
debruijinize vl (Fix (TRight x)) = tright <$> debruijinize vl x
debruijinize vl (Fix (TTrace x)) = ttrace <$> debruijinize vl x
debruijinize vl (Fix (TLam (Open (Left _)) x)) = tlam (Open ()) <$> debruijinize ("-- dummy" : vl) x
debruijinize vl (Fix (TLam (Closed (Left _)) x)) = tlam (Closed ()) <$> debruijinize ("-- dummyC" : vl) x
debruijinize vl (Fix (TLam (Open (Right n)) x)) = tlam (Open ()) <$> debruijinize (n : vl) x
debruijinize vl (Fix (TLam (Closed (Right n)) x)) = tlam (Closed ()) <$> debruijinize (n : vl) x
debruijinize _ (Fix (TLimitedRecursion)) = pure tlimitedrecursion

-- splitExpr' :: Term2 -> BreakState' BreakExtras
-- splitExpr' = \case
--   tzero -> pure ZeroF
--   tpair a b -> PairF <$> splitExpr' a <*> splitExpr' b
--   tvar n -> pure $ varNF n
--   tapp c i -> appF (splitExpr' c) (splitExpr' i)
--   tcheck c tc ->
--     let performTC = deferF ((\ia -> (SetEnvF (PairF (SetEnvF (PairF AbortF ia)) (RightF EnvF)))) <$> appF (pure $ LeftF EnvF) (pure $ RightF EnvF))
--     in (\ptc nc ntc -> SetEnvF (PairF ptc (PairF ntc nc))) <$> performTC <*> splitExpr' c <*> splitExpr' tc
--   tite i t e -> (\ni nt ne -> SetEnvF (PairF (GateF ne nt) ni)) <$> splitExpr' i <*> splitExpr' t <*> splitExpr' e
--   tleft x -> LeftF <$> splitExpr' x
--   tright x -> RightF <$> splitExpr' x
--   ttrace x -> (\tf nx -> SetEnvF (PairF tf nx)) <$> deferF (pure TraceF) <*> splitExpr' x
--   tlam (Open ()) x -> (\f -> PairF f EnvF) <$> deferF (splitExpr' x)
--   tlam (Closed ()) x -> (\f -> PairF f ZeroF) <$> deferF (splitExpr' x)
--   tlimitedrecursion -> pure $ AuxF UnsizedRecursion

splitExpr' :: Term2 -> BreakState' BreakExtras
splitExpr' = \case
  (Fix TZero) -> pure ZeroF
  Fix (TPair a b) -> PairF <$> splitExpr' a <*> splitExpr' b
  Fix (TVar n) -> pure $ varNF n
  Fix (TApp c i) -> appF (splitExpr' c) (splitExpr' i)
  Fix (TCheck c tc) ->
    let performTC = deferF ((\ia -> (SetEnvF (PairF (SetEnvF (PairF AbortF ia)) (RightF EnvF)))) <$> appF (pure $ LeftF EnvF) (pure $ RightF EnvF))
    in (\ptc nc ntc -> SetEnvF (PairF ptc (PairF ntc nc))) <$> performTC <*> splitExpr' c <*> splitExpr' tc
  Fix (TITE i t e) -> (\ni nt ne -> SetEnvF (PairF (GateF ne nt) ni)) <$> splitExpr' i <*> splitExpr' t <*> splitExpr' e
  Fix (TLeft x) -> LeftF <$> splitExpr' x
  Fix (TRight x) -> RightF <$> splitExpr' x
  Fix (TTrace x) -> (\tf nx -> SetEnvF (PairF tf nx)) <$> deferF (pure TraceF) <*> splitExpr' x
  Fix (TLam (Open ()) x) -> (\f -> PairF f EnvF) <$> deferF (splitExpr' x)
  Fix (TLam (Closed ()) x) -> (\f -> PairF f ZeroF) <$> deferF (splitExpr' x)
  Fix TLimitedRecursion -> pure $ AuxF UnsizedRecursion

splitExpr :: Term2 -> Term3
splitExpr t = let (bf, (_,m)) = State.runState (splitExpr' t) (FragIndex 1, Map.empty)
              in Term3 $ Map.insert (FragIndex 0) bf m

convertPT :: Int -> Term3 -> Term4
convertPT n (Term3 termMap) =
  let changeTerm = \case
        AuxF UnsizedRecursion -> partialFixF n
        ZeroF -> pure ZeroF
        PairF a b -> PairF <$> changeTerm a <*> changeTerm b
        EnvF -> pure EnvF
        SetEnvF x -> SetEnvF <$> changeTerm x
        DeferF fi -> pure $ DeferF fi
        AbortF -> pure AbortF
        GateF l r -> GateF <$> changeTerm l <*> changeTerm r
        LeftF x -> LeftF <$> changeTerm x
        RightF x -> RightF <$> changeTerm x
        TraceF -> pure TraceF
      mmap = traverse changeTerm termMap
      startKey = succ . fst $ Map.findMax termMap
      newMapBuilder = do
        changedTermMap <- mmap
        State.modify (\(i,m) -> (i, Map.union changedTermMap m))
      (_,newMap) = State.execState newMapBuilder (startKey, Map.empty)
  in Term4 newMap

resolve :: String -> ParserState -> Maybe Term1
resolve name (ParserState bound) = if Map.member name bound
                                   then Map.lookup name bound
                                   else Just . tvar . Right $ name

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
parseString :: SILParser (ParserTerm l x v)
parseString = fmap s2t $ char '\"' *> manyTill L.charLiteral (char '\"')

-- |Parse a variable.
parseVariable :: SILParser Term1
parseVariable = do
  varName <- identifier
  parseState <- State.get
  case resolve varName parseState of
    Nothing -> fail $ concat  ["identifier ", varName, " undeclared"]
    Just i -> pure i

-- |Prarse number (Integer).
parseNumber :: SILParser (ParserTerm l x v)
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
  return $ tpair a b

-- |Parse a list.
parseList :: SILParser Term1
parseList = do
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  return $ foldr tpair tzero exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: SILParser Term1
parseITE = do
  reserved "if"
  scn
  cond <- parseLongExpr <|> parseSingleExpr
  scn
  reserved "then"
  scn
  thenExpr <- parseLongExpr <|> parseSingleExpr
  scn
  reserved "else"
  scn
  elseExpr <- parseLongExpr
  scn
  return $ tite cond thenExpr elseExpr

-- |Parse left.
parsePLeft :: SILParser Term1
parsePLeft = tleft <$> (reserved "left" *> parseSingleExpr)

-- |Parse right.
parsePRight :: SILParser Term1
parsePRight = tright <$> (reserved "right" *> parseSingleExpr)

-- |Parse trace.
parseTrace :: SILParser Term1
parseTrace = ttrace <$> (reserved "trace" *> parseSingleExpr)

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
                                   , parsePartialFix
                                   , parens (scn *> parseLongExpr <* scn)
                                   ]

-- |Parse application of functions.
parseApplied :: SILParser Term1
parseApplied = do
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) -> pure $ foldl tapp f args
    _ -> fail "expected expression"

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
  return $ foldr (\n -> tlam (Open (Right n))) iexpr variables

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
  return . tlam (Closed (Right $ head variables)) $ foldr (\n -> tlam (Open (Right n))) iexpr (tail variables)

-- |Parse let expression.
parseLet :: SILParser Term1
parseLet = do
  reserved "let"
  initialState <- State.get
  scn
  manyTill parseAssignment (reserved "in")
  scn
  expr <- parseLongExpr
  scn
  State.put initialState
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
parsePartialFix :: SILParser Term1
parsePartialFix = symbol "?" *> pure tlimitedrecursion

parseRefinementCheck :: SILParser (Term1 -> Term1)
parseRefinementCheck = flip tcheck <$> (symbol ":" *> parseLongExpr)

-- |Parse assignment.
parseAssignment :: SILParser ()
parseAssignment = do
  var <- identifier
  scn
  annotation <- optional . try $ parseRefinementCheck
  reserved "=" <?> "assignment ="
  expr <- parseLongExpr
  scn
  let annoExp = case annotation of
        Just f -> f expr
        _ -> expr
      assign ps = case addBound var annoExp ps of
        Just nps -> nps
        _ -> error $ "shadowing of binding not allowed " ++ var
  State.modify assign

 -- |Parse top level expressions.
parseTopLevel :: SILParser Bindings
parseTopLevel = do
  many parseAssignment <* eof
  (ParserState bound) <- State.get
  pure bound

debugIndent i = show $ State.runState i (initialPos "debug")

-- |Helper function to test parsers without a result.
runSILParser_ :: Show a => SILParser a -> String -> IO ()
runSILParser_ parser str = do
  let p            = State.runStateT parser $ ParserState (Map.empty)
  case runParser p "" str of
    Right (a, s) -> do
      putStrLn ("Result:      " ++ show a)
      putStrLn ("Final state: " ++ show s)
    Left e -> putStr (errorBundlePretty e)

-- |Helper function to debug parsers without a result.
runSILParserWDebug :: Show a => SILParser a -> String -> IO ()
runSILParserWDebug parser str = do
  let p = State.runStateT parser $ ParserState (Map.empty)
  case runParser (dbg "debug" p) "" str of
    Right (a, s) -> do
      putStrLn ("Result:      " ++ show a)
      putStrLn ("Final state: " ++ show s)
    Left e -> putStr (errorBundlePretty e)

-- |Helper function to test parsers with parsing result.
runSILParser :: Show a => SILParser a -> String -> IO String
runSILParser parser str = do
  let p = State.runStateT parser $ ParserState (Map.empty)
  case runParser p "" str of
    Right (a, s) -> return $ show a
    Left e -> return $ errorBundlePretty e

-- |Helper function to test if parser was successful.
parseSuccessful :: Show a => SILParser a -> String -> IO Bool
parseSuccessful parser str = do
  let p = State.runStateT parser $ ParserState (Map.empty)
  case runParser p "" str of
    Right _ -> return True
    Left _ -> return False

-- |Parse with specified prelude.
parseWithPrelude :: Bindings -> String -> Either ErrorString Bindings
parseWithPrelude prelude str = let startState = ParserState prelude
                                   p          = State.runStateT parseTopLevel startState
                                   eitherEB str = case runParser p "" str of
                                     Right (a, s) -> Right a
                                     Left x       -> Left $ MkES $ errorBundlePretty x
                               in eitherEB str

-- |Parse prelude.
parsePrelude :: String -> Either ErrorString Bindings
parsePrelude = parseWithPrelude Map.empty

-- |Parse main.
parseMain :: Bindings -> String -> Either ErrorString Term3
parseMain prelude s = parseWithPrelude prelude s >>= getMain where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> fail "no main method found"
    Just main -> splitExpr <$> debruijinize [] main
