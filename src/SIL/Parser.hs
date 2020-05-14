{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

module SIL.Parser where

import Control.Lens.Combinators
import Control.Lens.Operators
import Control.Monad
import Data.Bifunctor
import Data.Char
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Foldable as F
import Data.List (elemIndex, delete, elem)
import Data.Map (Map, fromList, toList)
import qualified Data.Map as Map
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import Text.Read (readMaybe)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Pos
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import qualified System.IO.Strict as Strict


import SIL
import SIL.TypeChecker
-- import SIL.Prisms

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
i2c x = TLam (Closed (Left ())) (TLam (Open (Left ())) (inner x))
  where inner :: Int -> Term1
        inner = apo coalg
        coalg :: Int -> Base Term1 (Either Term1 Int)
        coalg 0 = TVarF (Left 0)
        coalg n = TAppF (Left . TVar $ Left 1) (Right $ n - 1)

debruijinize :: Monad m => VarList -> Term1 -> m Term2
debruijinize _ (TZero) = pure $ TZero
debruijinize vl (TPair a b) = TPair <$> debruijinize vl a <*> debruijinize vl b
debruijinize _ (TVar (Left i)) = pure $ TVar i
debruijinize vl (TVar (Right n)) = case elemIndex n vl of
                                     Just i -> pure $ TVar i
                                     Nothing -> fail $ "undefined identifier " ++ n
debruijinize vl (TApp i c) = TApp <$> debruijinize vl i <*> debruijinize vl c
debruijinize vl (TCheck c tc) = TCheck <$> debruijinize vl c <*> debruijinize vl tc
debruijinize vl (TITE i t e) = TITE <$> debruijinize vl i
                                    <*> debruijinize vl t
                                    <*> debruijinize vl e
debruijinize vl (TLeft x) = TLeft <$> debruijinize vl x
debruijinize vl (TRight x) = TRight <$> debruijinize vl x
debruijinize vl (TTrace x) = TTrace <$> debruijinize vl x
debruijinize vl (TLam (Open (Left _)) x) = TLam (Open ()) <$> debruijinize ("-- dummy" : vl) x
debruijinize vl (TLam (Closed (Left _)) x) = TLam (Closed ()) <$> debruijinize ("-- dummyC" : vl) x
debruijinize vl (TLam (Open (Right n)) x) = TLam (Open ()) <$> debruijinize (n : vl) x
debruijinize vl (TLam (Closed (Right n)) x) = TLam (Closed ()) <$> debruijinize (n : vl) x
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
  --pure . TVar . Right $ varName
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
                else return x

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
  return $ ListUP exprs

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
  return $ ITEUP cond thenExpr elseExpr

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
    (f:args) -> do
      {-
      case f of
        TVar (Right "left") -> case args of
          [t] -> pure . TLeft $ t
          [] -> fail "This should be imposible. I'm being called fro parseApplied."
          (x:xs) -> pure $ foldl TApp (TLeft x) xs
        TVar (Right "right") -> case args of
          [t] -> pure . TRight $ t
          [] -> fail "This should be imposible. I'm being called fro parseApplied."
          (x:xs) -> pure $ foldl TApp (TRight x) xs
        TVar (Right "trace") -> case args of
          [t] -> pure . TTrace $ t
          [] -> fail "This should be imposible. I'm being called fro parseApplied."
          (x:xs) -> pure $ foldl TApp (TTrace x) xs
        TVar (Right "pair") -> case args of
          [a, b] -> pure $ TPair a b
          [a] -> pure $ TLam (Open (Right "x")) . TPair a . TVar . Right $ "x"
          [] -> fail "This should be imposible. I'm being called fro parseApplied."
          _ -> fail "Failed to parse pair. Too many arguments applied to pair."
        TVar (Right "app") -> case args of
          [a, b] -> pure $ TApp a b
          [a] -> pure $ TLam (Open (Right "x")) . TApp a . TVar . Right $ "x"
          [] -> fail "This should be imposible. I'm being called fro parseApplied."
          (x0:x1:xs) -> pure $ foldl TApp (TApp x0 x1) xs
        TVar (Right "check") -> case args of
          [a, b] -> pure $ TCheck a b
          [a] -> pure $ TLam (Open (Right "x")) . TCheck a . TVar . Right $ "x"
          [] -> fail "This should be imposible. I'm being called fro parseApplied."
          _ -> fail "Failed to parse check. Too many arguments applied to check."

        _ -> pure $ foldl TApp f args
-}
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
    True -> parser
    False -> fail "Expected same indentation."

applyUntilNoChange :: Eq a => (a -> a) -> a -> a
applyUntilNoChange f x = case x == (f x) of
                           True -> x
                           False -> applyUntilNoChange f $ f x

-- |Parse let expression.
parseLet :: SILParser UnprocessedParsedTerm
parseLet = do
  reserved "let" <* scn
  lvl <- L.indentLevel
  bindingsList <- manyTill (parseSameLvl lvl parseAssignment) (reserved "in") <* scn
  --let bindingsMap = foldr (uncurry Map.insert) Map.empty bindingsList
  expr <- parseLongExpr <* scn
  --let oexpr = applyUntilNoChange (optimizeLetBindingsReference intermediateState) expr
  pure $ LetUP bindingsList expr

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

-- |True when char argument is not an Int.
notInt :: Char -> Bool
notInt s = case (readMaybe [s]) :: Maybe Int of
             Just _ -> False
             Nothing -> True

-- |Separates name and Int tag.
--  Case of no tag, assigned tag is `-1` which will become `0` in `tagVar`
getTag :: String -> (String, Int)
getTag str = case name == str of
                  True -> (name, -1)
                  False -> (name, read $ drop (length str') str)
  where
    str' = dropUntil notInt $ reverse str
    name = take (length str') str

-- |Tags a var with number `i` if it doesn't already contain a number tag, or `i`
-- plus the already present number tag, and corrects for name collisions.
-- Also returns `Int` tag.
{-
tagVar :: ParserState -> (ParserState -> Set String) -> String -> Int -> (String, Int)
tagVar ps bindingNames str i = case candidate `Set.member` bindingNames ps of
                                 True -> (fst $ tagVar ps bindingNames str (i + 1), n + i + 1)
                                 False -> (candidate, n + i)
  where
    (name,n) = getTag str
    candidate = name ++ (show $ n + i)
-}

-- |Sateful (Int count) string tagging and keeping track of new names and old names with name collision
-- avoidance.
{-
stag :: ParserState -> (ParserState -> Set String) -> String -> State (Int, VarList, VarList) String
stag ps bindingNames str = do
  (i0, new0, old0) <- State.get
  let (new1, tag1) = tagVar ps bindingNames str (i0 + 1)
  if i0 >= tag1
    then State.modify (\(_, new, old) -> (i0 + 1, new ++ [new1], old ++ [str]))
    else State.modify (\(_, new, old) -> (tag1 + 1, new ++ [new1], old ++ [str]))
  pure new1
-}

-- |Renames top level bindings references found on a `Term1` by tagging them with consecutive `Int`s
-- while keeping track of new names and substituted names.
-- i.e. Let `f` and `g2` be two top level bindings
-- then `\g -> [g,f,g2]` would be renamend to `\g -> [g,f1,g3]` in `Term1` representation.
-- ["f1","g3"] would be the second part of the triplet (new names), and ["f", "g2"] the third part of
-- the triplet (substituted names)
{-
rename :: ParserState -> (ParserState -> Set String) -> Term1 -> (Term1, VarList, VarList)
rename ps bindingNames term1 = (res, newf, oldf)
  where
    toReplace = (vars term1) `Set.intersection` bindingNames ps
    sres = traverseOf (traversed . _Right . filtered (`Set.member` toReplace)) (stag ps bindingNames) term1
    (res, (_, newf, oldf)) = State.runState sres (1,[],[])
-}

-- |Adds bound to `ParserState` if there's no shadowing conflict.
{-
addTopLevelBound :: String -> Term1 -> ParserState -> Maybe ParserState
addTopLevelBound name expr ps =
  if Map.member name $ bound ps
  then Nothing
  else Just $ ParserState (Map.insert name expr $ bound ps) (letBound ps)

addLetBound :: String -> Term1 -> ParserState -> Maybe ParserState
addLetBound name expr ps =
  if Map.member name $ letBound ps
  then Nothing
  else Just $ ParserState (bound ps) (Map.insert name expr $ letBound ps)
-}

-- |Top level bindings encapsulated in an extra outer lambda and applied by it's corresponding
-- original reference.
-- e.g. let `f = zero` be a top level binding in `ParserState` `ps` and let `t1` be the `Term1` representation of
-- `[f,f]`
-- Then `optimizeTopLevelBindingsReference ps t1` will output the `Term1` representation of:
-- (\f1 f2 -> [f1, f2]) f f`
{-
optimizeTopLevelBindingsReference :: ParserState -> Term1 -> Term1
optimizeTopLevelBindingsReference parserState annoExp =
  optimizeBindingsReference parserState topLevelBindingNames (\str -> (bound parserState) Map.! str) annoExp
  -- optimizeBindingsReference parserState topLevelBindingNames (TVar . Right) annoExp

optimizeLetBindingsReference :: ParserState -> Term1 -> Term1
optimizeLetBindingsReference parserState annoExp =
  optimizeBindingsReference parserState letBindingNames (\str -> (letBound parserState) Map.! str) annoExp

optimizeBindingsReference :: ParserState
                          -> (ParserState -> Set String)
                          -> (String -> Term1)
                          -> Term1
                          -> Term1
optimizeBindingsReference parserState bindingNames f annoExp =
  case new == [] of
    True -> annoExp
    False -> foldl TApp (makeLambda parserState new t1) (f <$> old)
  where
    (t1, new, old) = rename parserState bindingNames annoExp
-}

{-
parseTopLevelAssignment :: SILParser ()
parseTopLevelAssignment = parseAssignment addTopLevelBound

parseLetAssignment :: SILParser ()
parseLetAssignment = parseAssignment addLetBound
-}

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: SILParser (String, UnprocessedParsedTerm)
parseAssignment = do
  var <- identifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  reserved "=" <?> "assignment ="
  expr <- parseLongExpr <* scn
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
runSILParser :: SILParser a -> String -> IO a
runSILParser parser str =
  case runParser parser "" str of
    Right x -> pure x
    Left e -> error $ errorBundlePretty e

-- |Helper function to test if parser was successful.
parseSuccessful :: SILParser a -> String -> IO Bool
parseSuccessful parser str =
  case runParser parser "" str of
    Right _ -> return True
    Left _ -> return False

-- |Parse with specified prelude.

parseWithPrelude :: String -> (UnprocessedParsedTerm -> UnprocessedParsedTerm)
  -> Either String UnprocessedParsedTerm
parseWithPrelude str addDefinitions =
  let result = addDefinitions <$> runParser parseTopLevel "" str
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
  Left x -> Left $ MkES $ errorBundlePretty x

-- |Collect all variable names in a `Term1` expresion excluding terms binded
--  to lambda args
vars :: UnprocessedParsedTerm -> Set String
vars = cata alg where
  alg :: Base UnprocessedParsedTerm (Set String) -> Set String
  alg (VarUPF n) = Set.singleton n
  alg (LamUPF n x) = del n x
  alg e = F.fold e
  del :: String -> Set String -> Set String
  del n x = case Set.member n x of
              False -> x
              True -> Set.delete n x

-- |`makeLambda ps vl t1` makes a `TLam` around `t1` with `vl` as arguments.
-- Automatic recognition of Close or Open type of `TLam`.
makeLambda :: Map String Term1 -> String -> UnprocessedParsedTerm -> Term1 -> Term1
makeLambda state variable upTermExpr term1 = -- trace ("\nstate: " <> show state <> ) $
  case unbound == Set.empty of
    True -> TLam (Closed (Right variable)) term1
    _ -> TLam (Open (Right variable)) term1
  where v = vars upTermExpr
        unbound = ((v \\ Map.keysSet state) \\ Set.singleton variable)

validateVariables :: UnprocessedParsedTerm -> Either String Term1
validateVariables term =
  let validateWithEnvironment :: UnprocessedParsedTerm
        -> State.StateT (Map String Term1) (Either String) Term1
      validateWithEnvironment = \case
        VarUP n -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _ -> State.lift . Left  $ "No definition found for " <> n
        ITEUP i t e -> TITE <$> validateWithEnvironment i <*> validateWithEnvironment t <*> validateWithEnvironment e
        IntUP x -> pure $ i2t x
        StringUP s -> pure $ s2t s
        PairUP a b -> TPair <$> validateWithEnvironment a <*> validateWithEnvironment b
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
        ListUP l -> foldr TPair TZero <$> mapM validateWithEnvironment l
        AppUP f x -> TApp <$> validateWithEnvironment f <*> validateWithEnvironment x
        --LamUP v x -> TLam (Open (Right v)) <$> validateWithEnvironment x
        LamUP v x -> do
          oldState <- State.get
          State.modify (Map.insert v (TVar (Right v)))
          result <- validateWithEnvironment x
          State.put oldState
          -- pure $ TLam (Open (Right v)) result
          pure $ makeLambda oldState v x result
        UnsizedRecursionUP -> pure TLimitedRecursion
        ChurchUP n -> pure $ i2c n
        LeftUP x -> TLeft <$> validateWithEnvironment x
        RightUP x -> TRight <$> validateWithEnvironment x
        TraceUP x -> TTrace <$> validateWithEnvironment x
  in State.evalStateT (validateWithEnvironment term) Map.empty

-- |Parse main.
parseMain :: (UnprocessedParsedTerm -> UnprocessedParsedTerm) -> String -> Either String Term3
parseMain prelude s = parseWithPrelude s prelude >>= process where
  process :: UnprocessedParsedTerm -> Either String Term3
  process = fmap splitExpr . (>>= debruijinize []) . validateVariables -- . (\x -> trace (show x) x)
