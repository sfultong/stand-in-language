{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parser where

import           Codec.Binary.UTF8.String   (encode)
import           Control.Lens.Combinators
import           Control.Lens.Operators
import           Control.Lens.Plated
import           Control.Monad
import           Control.Monad.State        (State)
import qualified Control.Monad.State        as State
import           Crypto.Hash                (Digest, SHA256, hash)
import           Data.Bifunctor
import qualified Data.ByteArray             as BA
import           Data.ByteString            (ByteString)
import qualified Data.ByteString            as BS
import           Data.Char
import qualified Data.Foldable              as F
import           Data.Functor               (($>))
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.List                  (delete, elem, elemIndex)
import           Data.Map                   (Map, fromList, toList)
import qualified Data.Map                   as Map
import           Data.Maybe                 (fromJust)
import           Data.Set                   (Set, (\\))
import qualified Data.Set                   as Set
import           Data.Void
import           Data.Word                  (Word8)
import           Debug.Trace
import qualified System.IO.Strict           as Strict
import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Debug
import           Text.Megaparsec.Pos
import           Text.Read                  (readMaybe)


import           Telomare                   (BreakExtras, BreakState',
                                             FragExpr (..), FragIndex (..),
                                             IExpr (..), LamType (..),
                                             ParserTerm (..), ParserTermF (..),
                                             Term1 (..), Term2 (..), Term3 (..),
                                             appF, clamF, deferF, lamF,
                                             nextBreakToken,
                                             unsizedRecursionWrapper, varNF)
import           Telomare.TypeChecker       (typeCheck)

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
  | CheckUP UnprocessedParsedTerm UnprocessedParsedTerm
  | HashUP UnprocessedParsedTerm -- ^ On ad hoc user defined types, this term will be substitued to a unique Int.
  -- TODO check
  deriving (Eq, Ord, Show)
makeBaseFunctor ''UnprocessedParsedTerm -- Functorial version UnprocessedParsedTerm
makePrisms ''UnprocessedParsedTerm

instance Plated UnprocessedParsedTerm where
  plate f = \case
    ITEUP i t e -> ITEUP <$> f i <*> f t <*> f e
    LetUP l x   -> LetUP <$> traverse sequenceA (second f <$> l) <*> f x
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

type VarList = [String]
-- |TelomareParser :: * -> *
--type TelomareParser = State.StateT ParserState (Parsec Void String)
type TelomareParser = Parsec Void String

newtype ErrorString = MkES { getErrorString :: String } deriving Show

-- |Int to ParserTerm
i2t :: Int -> ParserTerm l v
i2t = ana coalg where
  coalg :: Int -> Base (ParserTerm l v) Int
  coalg 0 = TZeroF
  coalg n = TPairF (n-1) 0

-- |List of Int's to ParserTerm
ints2t :: [Int] -> ParserTerm l v
ints2t = foldr (TPair . i2t) TZero

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

instance MonadFail (Either String) where
  fail = Left

debruijinize :: MonadFail m => VarList -> Term1 -> m Term2
debruijinize _ TZero = pure TZero
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
debruijinize vl (THash x) = THash <$> debruijinize vl x
debruijinize vl (TLam (Open n) x) = TLam (Open ()) <$> debruijinize (n : vl) x
debruijinize vl (TLam (Closed n) x) = TLam (Closed ()) <$> debruijinize (n : vl) x
debruijinize _ TLimitedRecursion = pure TLimitedRecursion

splitExpr' :: Term2 -> BreakState' BreakExtras BreakExtras
splitExpr' = \case
  TZero -> pure ZeroFrag
  TPair a b -> PairFrag <$> splitExpr' a <*> splitExpr' b
  TVar n -> pure $ varNF n
  TApp c i -> appF (splitExpr' c) (splitExpr' i)
  TCheck tc c ->
    let performTC = deferF ((\ia -> SetEnvFrag (PairFrag (SetEnvFrag (PairFrag AbortFrag ia)) (RightFrag EnvFrag))) <$> appF (pure $ LeftFrag EnvFrag) (pure $ RightFrag EnvFrag))
    in (\ptc nc ntc -> SetEnvFrag (PairFrag ptc (PairFrag ntc nc))) <$> performTC <*> splitExpr' c <*> splitExpr' tc
  TITE i t e -> (\ni nt ne -> SetEnvFrag (PairFrag (GateFrag ne nt) ni)) <$> splitExpr' i <*> splitExpr' t <*> splitExpr' e
  TLeft x -> LeftFrag <$> splitExpr' x
  TRight x -> RightFrag <$> splitExpr' x
  TTrace x -> (\tf nx -> SetEnvFrag (PairFrag tf nx)) <$> deferF (pure TraceFrag) <*> splitExpr' x
  TLam (Open ()) x -> lamF $ splitExpr' x
  TLam (Closed ()) x -> clamF $ splitExpr' x
  TLimitedRecursion -> nextBreakToken >>= unsizedRecursionWrapper

splitExpr :: Term2 -> Term3
splitExpr t = let (bf, (_,_,m)) = State.runState (splitExpr' t) (toEnum 0, FragIndex 1, Map.empty)
              in Term3 $ Map.insert (FragIndex 0) bf m

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
rws = ["let", "in", "if", "then", "else"]

-- |Variable identifiers can consist of alphanumeric characters, underscore,
-- and must start with an English alphabet letter
identifier :: TelomareParser String
identifier = lexeme . try $ p >>= check
  where
    p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_' <?> "variable")
    check x = if x `elem` rws
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else pure x

-- |Parser for parenthesis.
parens :: TelomareParser a -> TelomareParser a
parens = between (symbol "(") (symbol ")")

-- |Parser for brackets.
brackets :: TelomareParser a -> TelomareParser a
brackets = between (symbol "[") (symbol "]")

-- |Comma sepparated TelomareParser that will be useful for lists
commaSep :: TelomareParser a -> TelomareParser [a]
commaSep p = p `sepBy` symbol ","

-- |Integer TelomareParser used by `parseNumber` and `parseChurch`
integer :: TelomareParser Integer
integer = toInteger <$> lexeme L.decimal

-- |Parse string literal.
parseString :: TelomareParser UnprocessedParsedTerm
parseString = StringUP <$> (symbol "\"" *> manyTill L.charLiteral (symbol "\""))

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

-- |Parse a single expression.
parseSingleExpr :: TelomareParser UnprocessedParsedTerm
parseSingleExpr = choice $ try <$> [ parseHash
                                   , parseString
                                   , parseNumber
                                   , parsePair
                                   , parseList
                                   , parseChurch
                                   , parseVariable
                                   , parsePartialFix
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
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: TelomareParser UnprocessedParsedTerm
parseChurch = ChurchUP . fromInteger <$> (symbol "$" *> integer)

parsePartialFix :: TelomareParser UnprocessedParsedTerm
parsePartialFix = symbol "?" $> UnsizedRecursionUP

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

-- |Helper function to compile to Term2
runTelomareParser2Term2 :: TelomareParser UnprocessedParsedTerm -- ^Parser to run
                        -> [(String, UnprocessedParsedTerm)]    -- ^Prelude
                        -> String                               -- ^Raw string to be parsed
                        -> Either String Term2                  -- ^Error on Left
runTelomareParser2Term2 parser prelude str =
  first errorBundlePretty (runParser parser "" str) >>= process2Term2 prelude

-- |Helper function to test if parser was successful.
parseSuccessful :: Monad m => TelomareParser a -> String -> m Bool
parseSuccessful parser str =
  case runParser parser "" str of
    Right _ -> pure True
    Left _  -> pure False

addBuiltins :: UnprocessedParsedTerm -> UnprocessedParsedTerm
addBuiltins = LetUP
  [ ("zero", IntUP 0)
  , ("left", LamUP "x" (LeftUP (VarUP "x")))
  , ("right", LamUP "x" (RightUP (VarUP "x")))
  , ("trace", LamUP "x" (TraceUP (VarUP "x")))
  , ("pair", LamUP "x" (LamUP "y" (PairUP (VarUP "x") (VarUP "y"))))
  , ("app", LamUP "x" (LamUP "y" (AppUP (VarUP "x") (VarUP "y"))))
  ]

parsePrelude :: String -> Either String [(String, UnprocessedParsedTerm)]
parsePrelude str = let result = runParser (scn *> many parseAssignment <* eof) "" str
                    in first errorBundlePretty result

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
  del n x = if Set.member n x then Set.delete n x else x

-- |`makeLambda ps vl t1` makes a `TLam` around `t1` with `vl` as arguments.
-- Automatic recognition of Close or Open type of `TLam`.
makeLambda :: [(String, UnprocessedParsedTerm)] -- ^Bindings
           -> String                            -- ^Variable name
           -> Term1                             -- ^Lambda body
           -> Term1
makeLambda bindings str term1 =
  if unbound == Set.empty then TLam (Closed str) term1 else TLam (Open str) term1
  where bindings' = Set.fromList $ fst <$> bindings
        v = vars term1
        unbound = (v \\ bindings') \\ Set.singleton str

-- |Transformation from `UnprocessedParsedTerm` to `Term1` validating and inlining `VarUP`s
validateVariables :: [(String, UnprocessedParsedTerm)] -- ^ Prelude
                  -> UnprocessedParsedTerm
                  -> Either String Term1
validateVariables prelude term =
  let validateWithEnvironment :: UnprocessedParsedTerm
                              -> State.StateT (Map String Term1) (Either String) Term1
      validateWithEnvironment = \case
        LamUP v x -> do
          oldState <- State.get
          State.modify (Map.insert v (TVar v))
          result <- validateWithEnvironment x
          State.put oldState
          pure $ makeLambda prelude v result
        VarUP n -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _      -> State.lift . Left  $ "No definition found for " <> n
        LetUP preludeMap inner -> do
          oldPrelude <- State.get
          let addBinding (k,v) = do
                newTerm <- validateWithEnvironment v
                State.modify (Map.insert k newTerm)
          mapM_ addBinding preludeMap
          result <- validateWithEnvironment inner
          State.put oldPrelude
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
        CheckUP cf x -> TCheck <$> validateWithEnvironment cf <*> validateWithEnvironment x
        HashUP x -> THash <$> validateWithEnvironment x
  in State.evalStateT (validateWithEnvironment term) Map.empty

optimizeBuiltinFunctions :: UnprocessedParsedTerm -> UnprocessedParsedTerm
optimizeBuiltinFunctions = transform optimize where
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

-- |Process an `Term2` to have all `HashUP` replaced by a unique number.
-- The unique number is constructed by doing a SHA1 hash of the Term2 and
-- adding one for all consecutive HashUP's.
generateAllHashes :: Term2 -> Term2
generateAllHashes = transform interm where
  hash' :: ByteString -> Digest SHA256
  hash' = hash
  term2Hash :: Term2 -> ByteString
  term2Hash = BS.pack . BA.unpack . hash' . BS.pack . encode . show
  bs2Term2 :: ByteString -> Term2
  bs2Term2 bs = ints2t . drop 24 $ fromInteger . toInteger <$> BS.unpack bs
  interm :: Term2 -> Term2
  interm = \case
    THash term1 -> bs2Term2 . term2Hash $ term1
    x           -> x

-- |Process an `UnprocessedParsedTerm` to a `Term3` with failing capability.
process :: [(String, UnprocessedParsedTerm)] -- ^Prelude
        -> UnprocessedParsedTerm
        -> Either String Term3
process prelude upt = splitExpr <$> process2Term2 prelude upt

process2Term2 :: [(String, UnprocessedParsedTerm)] -- ^Prelude
              -> UnprocessedParsedTerm
              -> Either String Term2
process2Term2 prelude = fmap generateAllHashes
                      . debruijinize [] <=< validateVariables prelude
                      . optimizeBuiltinFunctions

-- |Parse with specified prelude
parseWithPrelude :: [(String, UnprocessedParsedTerm)]   -- ^Prelude
                 -> String                              -- ^Raw string to be parsed
                 -> Either String UnprocessedParsedTerm -- ^Error on Left
-- parseWithPrelude prelude str = bimap errorBundlePretty (LetUP prelude) $ runParser parseTopLevel "" str
parseWithPrelude prelude str = first errorBundlePretty $ runParser (parseTopLevelWithPrelude prelude) "" str

parseMain :: [(String, UnprocessedParsedTerm)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either String Term3               -- ^Error on Left.
parseMain prelude s = parseWithPrelude prelude s >>= process prelude
