{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

module SIL.Parser where

import           Control.Lens.Combinators
import           Control.Lens.Operators
import           Control.Monad
import           Control.Monad.State        (State)
import qualified Control.Monad.State        as State
import           Data.Bifunctor
import           Data.Char
import qualified Data.Foldable              as F
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.List                  (delete, elem, elemIndex)
import           Data.Map                   (Map)
import           Data.Map                   (Map, fromList, toList)
import qualified Data.Map                   as Map
import           Data.Maybe                 (fromJust)
import           Data.Set                   (Set, (\\))
import qualified Data.Set                   as Set
import           Data.Void
import           Debug.Trace
import           SIL
import           SIL.TypeChecker
import qualified System.IO.Strict           as Strict
import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Debug
import           Text.Megaparsec.Pos
import           Text.Read                  (readMaybe)

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
  | UnsizedRecursionUP
  | LeftUP UnprocessedParsedTerm
  | RightUP UnprocessedParsedTerm
  | TraceUP UnprocessedParsedTerm
  -- TODO check
  deriving (Eq, Ord, Show)
makeBaseFunctor ''UnprocessedParsedTerm -- * Functorial version UnprocessedParsedTerm

instance EndoMapper UnprocessedParsedTerm where
  endoMap f = \case
    VarUP str -> f $ VarUP str
    ITEUP i t e -> f $ ITEUP (recur i) (recur t) (recur e)
    LetUP listmap expr -> f $ LetUP ((second recur) <$> listmap) $ recur expr
    ListUP l -> f $ ListUP (recur <$> l)
    IntUP i -> f $ IntUP i
    StringUP str -> f $ StringUP str
    PairUP a b -> f $ PairUP (recur a) (recur b)
    AppUP x y -> f $ AppUP (recur x) (recur y)
    LamUP str x -> f $ LamUP str (recur x)
    ChurchUP i -> f $ ChurchUP i
    UnsizedRecursionUP -> f UnsizedRecursionUP
    LeftUP l -> f $ LeftUP (recur l)
    RightUP r -> f $ RightUP (recur r)
    TraceUP t -> f $ TraceUP (recur t)
    where recur = endoMap f

type VarList = [String]

-- |SILParser :: * -> *
--type SILParser = State.StateT ParserState (Parsec Void String)
type SILParser = Parsec Void String

newtype ErrorString = MkES { getErrorString :: String } deriving Show

-- |Int to ParserTerm
i2t :: Int -> ParserTerm l v
i2t = ana coalg where
  coalg :: Int -> Base (ParserTerm l v) Int
  coalg 0 = TZeroF
  coalg n = TPairF (n-1) 0

-- |List of Int's to ParserTerm
ints2t :: [Int] -> ParserTerm l v
ints2t = foldr (\i t -> TPair (i2t i) t) TZero

-- |String to ParserTerm
s2t :: String -> ParserTerm l v
s2t = ints2t . map ord

-- |Int to Church encoding
i2c :: Int -> Term1
i2c x = TLam (Closed "f") (TLam (Open "x") (inner x))
  where inner :: Int -> Term1
        inner = apo coalg
        coalg :: Int -> Base Term1 (Either Term1 Int)
        coalg 0 = TVarF "x"
        coalg n = TAppF (Left . TVar $ "f") (Right $ n - 1)

debruijinize :: Monad m => VarList -> Term1 -> m Term2
debruijinize _ (TZero) = pure $ TZero
debruijinize vl (TPair a b) = TPair <$> debruijinize vl a <*> debruijinize vl b
debruijinize vl (TVar n) = case elemIndex n vl of
                             Just i  -> pure $ TVar i
                             Nothing -> fail $ "undefined identifier " ++ n
debruijinize vl (TApp i c) = TApp <$> debruijinize vl i <*> debruijinize vl c
debruijinize vl (TCheck c tc) = TCheck <$> debruijinize vl c <*> debruijinize vl tc
debruijinize vl (TITE i t e) = TITE <$> debruijinize vl i
                                    <*> debruijinize vl t
                                    <*> debruijinize vl e
debruijinize vl (TLeft x) = TLeft <$> debruijinize vl x
debruijinize vl (TRight x) = TRight <$> debruijinize vl x
debruijinize vl (TTrace x) = TTrace <$> debruijinize vl x
debruijinize vl (TLam (Open n) x) = TLam (Open ()) <$> debruijinize (n : vl) x
debruijinize vl (TLam (Closed n) x) = TLam (Closed ()) <$> debruijinize (n : vl) x
debruijinize _ (TLimitedRecursion) = pure TLimitedRecursion

splitExpr' :: Term2 -> BreakState' BreakExtras
splitExpr' = \case
  TZero -> pure ZeroF
  TPair a b -> PairF <$> splitExpr' a <*> splitExpr' b
  TVar n -> pure $ varNF n
  TApp c i -> appF (splitExpr' c) (splitExpr' i)
  TCheck c tc ->
    let performTC = deferF ((\ia -> (SetEnvF (PairF (SetEnvF (PairF AbortF ia)) (RightF EnvF)))) <$> appF (pure $ LeftF EnvF) (pure $ RightF EnvF))
    in (\ptc nc ntc -> SetEnvF (PairF ptc (PairF ntc nc))) <$> performTC <*> splitExpr' c <*> splitExpr' tc
  TITE i t e -> (\ni nt ne -> SetEnvF (PairF (GateF ne nt) ni)) <$> splitExpr' i <*> splitExpr' t <*> splitExpr' e
  TLeft x -> LeftF <$> splitExpr' x
  TRight x -> RightF <$> splitExpr' x
  TTrace x -> (\tf nx -> SetEnvF (PairF tf nx)) <$> deferF (pure TraceF) <*> splitExpr' x
  TLam (Open ()) x -> (\f -> PairF f EnvF) <$> deferF (splitExpr' x)
  TLam (Closed ()) x -> (\f -> PairF f ZeroF) <$> deferF (splitExpr' x)
  TLimitedRecursion -> pure $ AuxF UnsizedRecursion

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

-- |Parse a variable.
parseVariable :: SILParser UnprocessedParsedTerm
parseVariable = do
  varName <- identifier
  pure $ VarUP varName

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
rws = ["let", "in", "if", "then", "else"]

-- |Variable identifiers can consist of alphanumeric characters, underscore,
-- and must start with an English alphabet letter
identifier :: SILParser String
identifier = (lexeme . try) $ p >>= check
    where
      p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_' <?> "variable")
      check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else pure x

-- |Parser for parenthesis.
parens :: SILParser a -> SILParser a
parens = between (symbol "(") (symbol ")")

-- |Parser for brackets.
brackets :: SILParser a -> SILParser a
brackets = between (symbol "[") (symbol "]")

-- |Comma sepparated SILParser that will be useful for lists
commaSep :: SILParser a -> SILParser [a]
commaSep p = p `sepBy` (symbol ",")

-- |Integer SILParser used by `parseNumber` and `parseChurch`
integer :: SILParser Integer
integer = toInteger <$> lexeme L.decimal

-- |Parse string literal.
parseString :: SILParser UnprocessedParsedTerm
parseString = StringUP <$> (char '\"' *> manyTill L.charLiteral (char '\"'))

-- |Parse number (Integer).
parseNumber :: SILParser UnprocessedParsedTerm
parseNumber = (IntUP . fromInteger) <$> integer

-- |Parse a pair.
parsePair :: SILParser UnprocessedParsedTerm
parsePair = parens $ do
  a <- scn *> parseLongExpr <* scn
  symbol "," <* scn
  b <- parseLongExpr <* scn
  pure $ PairUP a b

-- |Parse a list.
parseList :: SILParser UnprocessedParsedTerm
parseList = do
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  pure $ ListUP exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: SILParser UnprocessedParsedTerm
parseITE = do
  reserved "if" <* scn
  cond <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "then" <* scn
  thenExpr <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "else" <* scn
  elseExpr <- parseLongExpr <* scn
  pure $ ITEUP cond thenExpr elseExpr

-- |Parse a single expression.
parseSingleExpr :: SILParser UnprocessedParsedTerm
parseSingleExpr = choice $ try <$> [ parseString
                                   , parseNumber
                                   , parsePair
                                   , parseList
                                   , parseChurch
                                   , parseVariable
                                   , parsePartialFix
                                   , parens (scn *> parseLongExpr <* scn)
                                   ]

-- |Parse application of functions.
parseApplied :: SILParser UnprocessedParsedTerm
parseApplied = do
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) ->
      pure $ foldl AppUP f args
    _ -> fail "expected expression"

-- |Parse lambda expression.
parseLambda :: SILParser UnprocessedParsedTerm
parseLambda = do
  symbol "\\" <* scn
  variables <- some identifier <* scn
  symbol "->" <* scn
  -- TODO make sure lambda names don't collide with bound names
  term1expr <- parseLongExpr <* scn
  pure $ foldr LamUP term1expr variables

-- |Parser that fails if indent level is not `pos`.
parseSameLvl :: Pos -> SILParser a -> SILParser a
parseSameLvl pos parser = do
  lvl <- L.indentLevel
  case pos == lvl of
    True  -> parser
    False -> fail "Expected same indentation."

-- |`applyUntilNoChange f x` returns the fix point of `f` with `x` the starting point.
-- This function will loop if there is no fix point exists.
applyUntilNoChange :: Eq a => (a -> a) -> a -> a
applyUntilNoChange f x = case x == (f x) of
                           True  -> x
                           False -> applyUntilNoChange f $ f x

-- |Parse let expression.
parseLet :: SILParser UnprocessedParsedTerm
parseLet = do
  reserved "let" <* scn
  lvl <- L.indentLevel
  bindingsList <- manyTill (parseSameLvl lvl parseAssignment) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  pure $ LetUP bindingsList expr

-- |Extracting list (bindings) from the wrapping `LetUP` used to keep track of bindings.
extractBindingsList :: (UnprocessedParsedTerm -> UnprocessedParsedTerm)
                    -> [(String, UnprocessedParsedTerm)]
extractBindingsList bindings = case bindings $ IntUP 0 of
              LetUP b x -> b
              _ -> error $ unlines [ "`bindings` should be an unapplied LetUP UnprocessedParsedTerm."
                                   , "Called from `extractBindingsList'`"
                                   ]

-- |Parse long expression.
parseLongExpr :: SILParser UnprocessedParsedTerm
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseApplied
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: SILParser UnprocessedParsedTerm
parseChurch = (ChurchUP . fromInteger) <$> (symbol "$" *> integer)

parsePartialFix :: SILParser UnprocessedParsedTerm
parsePartialFix = symbol "?" *> pure UnsizedRecursionUP

-- |Parse refinement check.
parseRefinementCheck :: SILParser (UnprocessedParsedTerm -> UnprocessedParsedTerm)
parseRefinementCheck = pure id <* (symbol ":" *> parseLongExpr)

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: SILParser (String, UnprocessedParsedTerm)
parseAssignment = do
  var <- identifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  scn *> symbol "=" <?> "assignment ="
  expr <- scn *> parseLongExpr <* scn
  pure (var, expr)

 -- |Parse top level expressions.
parseTopLevel :: SILParser UnprocessedParsedTerm
parseTopLevel = do
  bindingList <- scn *> many parseAssignment <* eof
  pure $ LetUP bindingList (fromJust $ lookup "main" bindingList)

parseDefinitions :: SILParser (UnprocessedParsedTerm -> UnprocessedParsedTerm)
parseDefinitions = do
  bindingList <- scn *> many parseAssignment <* eof
  pure $ LetUP bindingList

-- |Helper function to test parsers without a result.
runSILParser_ :: Show a => SILParser a -> String -> IO ()
runSILParser_ parser str = show <$> runSILParser parser str >>= putStrLn

-- |Helper function to debug parsers without a result.
runSILParserWDebug :: Show a => SILParser a -> String -> IO ()
runSILParserWDebug parser str = show <$> runSILParser (dbg "debug" parser) str >>= putStrLn


-- |Helper function to test SIL parsers with any result.
runSILParser :: Monad m => SILParser a -> String -> m a
runSILParser parser str =
  case runParser parser "" str of
    Right x -> pure x
    Left e  -> error $ errorBundlePretty e

-- |Helper function to test if parser was successful.
parseSuccessful :: Monad m => SILParser a -> String -> m Bool
parseSuccessful parser str =
  case runParser parser "" str of
    Right _ -> pure True
    Left _  -> pure False

-- |Parse with specified prelude and g-> UnprocessedParsedTerm)
parseWithPrelude :: (UnprocessedParsedTerm -> UnprocessedParsedTerm)
                 -> String
                 -> Either String UnprocessedParsedTerm
parseWithPrelude prelude str = let result = prelude <$> runParser parseTopLevel "" str
                               in first errorBundlePretty result

addBuiltins :: UnprocessedParsedTerm -> UnprocessedParsedTerm
addBuiltins = LetUP
  [ ("zero", IntUP 0)
  , ("left", LamUP "x" (LeftUP (VarUP "x")))
  , ("right", LamUP "x" (RightUP (VarUP "x")))
  , ("trace", LamUP "x" (TraceUP (VarUP "x")))
  , ("pair", LamUP "x" (LamUP "y" (PairUP (VarUP "x") (VarUP "y"))))
  , ("app", LamUP "x" (LamUP "y" (AppUP (VarUP "x") (VarUP "y"))))
  ]

-- |Parse prelude.
parsePrelude :: String -> Either ErrorString (UnprocessedParsedTerm -> UnprocessedParsedTerm)
parsePrelude str = case runParser parseDefinitions "" str of
  Right pd -> Right (addBuiltins . pd)
  Left x   -> Left $ MkES $ errorBundlePretty x

-- |Collect all variable names in a `Term1` expresion excluding terms binded
--  to lambda args
vars :: Term1 -> Set String
vars = cata alg where
  alg :: Base Term1 (Set String) -> Set String
  alg (TVarF n)            = Set.singleton n
  alg (TLamF (Open n) x)   = del n x
  alg (TLamF (Closed n) x) = del n x
  alg e                    = F.fold e
  del :: String -> Set String -> Set String
  del n x = case Set.member n x of
              False -> x
              True  -> Set.delete n x

-- |`makeLambda ps vl t1` makes a `TLam` around `t1` with `vl` as arguments.
-- Automatic recognition of Close or Open type of `TLam`.
makeLambda :: (UnprocessedParsedTerm -> UnprocessedParsedTerm) -- ^Bindings
           -> String                                           -- ^Variable name
           -> Term1                                            -- ^Lambda body
           -> Term1
makeLambda bindings str term1 =
  case unbound == Set.empty of
    True -> TLam (Closed str) term1
    _    -> TLam (Open str) term1
  where bindings' = Set.fromList $ fst <$> extractBindingsList bindings
        v = vars term1
        unbound = ((v \\ bindings') \\ Set.singleton str)

validateVariables :: (UnprocessedParsedTerm -> UnprocessedParsedTerm) -> UnprocessedParsedTerm -> Either String Term1
validateVariables bindings term =
  let validateWithEnvironment :: UnprocessedParsedTerm
        -> State.StateT (Map String Term1) (Either String) Term1
      validateWithEnvironment = \case
        LamUP v x -> do
          oldState <- State.get
          State.modify (Map.insert v (TVar v))
          result <- validateWithEnvironment x
          State.put oldState
          pure $ makeLambda bindings v result
        VarUP n -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _      -> State.lift . Left  $ "No definition found for " <> n
        --TODO add in Daniel's code
        LetUP bindingsMap inner -> do
          oldBindings <- State.get
          let addBinding (k,v) = do
                term <- validateWithEnvironment v
                State.modify (Map.insert k term)
          mapM_ addBinding bindingsMap
          result <- validateWithEnvironment inner
          State.put oldBindings
          pure result
        ITEUP i t e -> TITE <$> validateWithEnvironment i
                            <*> validateWithEnvironment t
                            <*> validateWithEnvironment e
        IntUP x -> pure $ i2t x
        StringUP s -> pure $ s2t s
        PairUP a b -> TPair <$> validateWithEnvironment a
                            <*> validateWithEnvironment b
        ListUP l -> foldr TPair TZero <$> mapM validateWithEnvironment l
        AppUP f x -> TApp <$> validateWithEnvironment f
                          <*> validateWithEnvironment x
        UnsizedRecursionUP -> pure TLimitedRecursion
        ChurchUP n -> pure $ i2c n
        LeftUP x -> TLeft <$> validateWithEnvironment x
        RightUP x -> TRight <$> validateWithEnvironment x
        TraceUP x -> TTrace <$> validateWithEnvironment x
  in State.evalStateT (validateWithEnvironment term) Map.empty

optimizeBuiltinFunctions :: UnprocessedParsedTerm -> UnprocessedParsedTerm
optimizeBuiltinFunctions = endoMap optimize where
  optimize = \case
    twoApp@(AppUP (AppUP f x) y) ->
      case f of
        VarUP "pair" -> PairUP x y
        VarUP "app"  -> AppUP x y
        _            -> twoApp
    oneApp@(AppUP f x) ->
      case f of
        VarUP "left"  -> LeftUP x
        VarUP "right" -> RightUP x
        VarUP "trace" -> TraceUP x
        VarUP "pair"  -> LamUP "y" (PairUP x . VarUP $ "y")
        VarUP "app"   -> LamUP "y" (AppUP x . VarUP $ "y")
        _             -> oneApp
        -- VarUP "check" TODO
    x -> x

-- |Process an `UnprocessedParesedTerm` to a `Term3` with failing capability.
process :: (UnprocessedParsedTerm -> UnprocessedParsedTerm) -> UnprocessedParsedTerm -> Either String Term3
process bindings = fmap splitExpr . (>>= debruijinize []) . validateVariables bindings . optimizeBuiltinFunctions

-- |Parse main.
parseMain :: (UnprocessedParsedTerm -> UnprocessedParsedTerm) -> String -> Either String Term3
parseMain prelude s = parseWithPrelude prelude s >>= process prelude
