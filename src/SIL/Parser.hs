{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module SIL.Parser where

import Control.Lens.Combinators
import Control.Lens.Operators
import Control.Monad
import Data.Char
import Data.Functor.Foldable
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

type VarList = [String]
type Bindings = Map String Term1

-- |SILParser :: * -> *
type SILParser = State.StateT ParserState (Parsec Void String)

newtype ErrorString = MkES { getErrorString :: String } deriving Show

data ParserState = ParserState
  { bound :: Bindings -- *Bindings collected by parseTopLevelAssignment
  , letBound :: Bindings -- *Bindings collected by parseLetAssignment
  } deriving Show

-- |Helper to retrieve all let names as a Set.
letBindingNames :: ParserState -> Set String
letBindingNames = Map.keysSet . letBound

-- |Helper to retrieve all top level function names as a Set.
topLevelBindingNames :: ParserState -> Set String
topLevelBindingNames = Map.keysSet . bound

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
        -- coalg :: Int -> Term1F (Either Term1 Int)
        coalg :: Int -> Base Term1 (Either Term1 Int)
        coalg 0 = TVarF (Left 0)
        coalg n = TAppF (Left . TVar $ Left 1) (Right $ n - 1)


-- TODO: Use a recursion scheme.
resolveAllTopLevel :: Bindings -> Set String -> Term1 -> Term1
resolveAllTopLevel tlv fv (TZero) = TZero
resolveAllTopLevel tlv fv (TPair a b) = TPair (resolveAllTopLevel tlv fv a) (resolveAllTopLevel tlv fv b)
resolveAllTopLevel tlv fv (TVar (Left i)) = TVar . Left $ i
resolveAllTopLevel tlv fv (TVar (Right n)) =   case n `Set.member` fv of
                                             True -> tlv Map.! n
                                             False -> TVar . Right $ n
resolveAllTopLevel tlv fv (TApp i c) = TApp (resolveAllTopLevel tlv fv i) (resolveAllTopLevel tlv fv c)
resolveAllTopLevel tlv fv (TCheck c tc) = TCheck (resolveAllTopLevel tlv fv c) (resolveAllTopLevel tlv fv tc)
resolveAllTopLevel tlv fv (TITE i t e) = TITE (resolveAllTopLevel tlv fv i)
                                          (resolveAllTopLevel tlv fv t)
                                          (resolveAllTopLevel tlv fv e)
resolveAllTopLevel tlv fv (TLeft x) = TLeft $ resolveAllTopLevel tlv fv x
resolveAllTopLevel tlv fv (TRight x) = TRight $ resolveAllTopLevel tlv fv x
resolveAllTopLevel tlv fv (TTrace x) = TTrace $ resolveAllTopLevel tlv fv x
resolveAllTopLevel tlv fv (TLam l x) = TLam l $ resolveAllTopLevel tlv fv x
resolveAllTopLevel tlv fv TLimitedRecursion = TLimitedRecursion

-- t1 = do
--   ps <- State.get
--   let vs = vars t1
--       tlv = bound ps
--       isTVarRight :: Term1 -> Bool
--       isTVarRight (TVar (Right _)) = True
--       isTVarRight _ = False
--       mod :: Term1 -> Term1
--       mod (TVar (Right s)) = tlv Map.! s
--       mod x = error "woooot"
--       myshow :: Term1 -> IO ()
--       myshow = putStrLn . show
--   -- t1 & (traversed . filtered (\x -> (isTVarRight x) && x `Set.member` (TVar . Right <$> vs))) %~ mod
--   traverseOf (traversed . filtered (\x -> (isTVarRight x))) (myshow) t1

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

-- |Helper function to get Term2
debruijinizedTerm :: SILParser Term1 -> String -> IO Term2
debruijinizedTerm parser str = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let prelude = case parsePrelude preludeFile of
                  Right p -> p
                  Left pe -> error . getErrorString $ pe
      startState = ParserState prelude Map.empty
      p = State.runStateT parser startState
      t1 = case runParser p "" str of
             Right (a, s) -> a
             Left e -> error . errorBundlePretty $ e
  debruijinize [] t1

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

-- resolve :: String -> ParserState -> Maybe Term1
-- resolve name (ParserState bound) = if Map.member name bound
--                                    then Map.lookup name bound
--                                    else Just . TVar . Right $ name

-- |Parse a variable.
parseVariable :: SILParser Term1
parseVariable = do
  varName <- identifier
  pure . TVar . Right $ varName
  -- parseState <- State.get
  -- case resolve varName parseState of
  --   Nothing -> fail $ concat  ["identifier ", varName, " undeclared"] -- unreachable
  --   Just i -> pure i

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
parseString :: SILParser (ParserTerm l v)
parseString = fmap s2t $ char '\"' *> manyTill L.charLiteral (char '\"')

-- |Prarse number (Integer).
parseNumber :: SILParser (ParserTerm l v)
parseNumber = (i2t . fromInteger) <$> integer

-- |Parse a pair.
parsePair :: SILParser Term1
parsePair = parens $ do
  a <- scn *> parseLongExpr <* scn
  symbol "," <* scn
  b <- parseLongExpr <* scn
  pure $ TPair a b

-- |Parse a list.
parseList :: SILParser Term1
parseList = do
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  return $ foldr TPair TZero exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: SILParser Term1
parseITE = do
  reserved "if" <* scn
  cond <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "then" <* scn
  thenExpr <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "else" <* scn
  elseExpr <- parseLongExpr <* scn
  return $ TITE cond thenExpr elseExpr

-- |Parse a single expression.
parseSingleExpr :: SILParser Term1
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
parseApplied :: SILParser Term1
parseApplied = do
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) -> do
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
    _ -> fail "expected expression"

-- |Collect all variable names in a `Term1` expresion excluding terms binded
--  to lambda args
vars :: Term1 -> Set String
vars = cata alg where
  alg :: Base Term1 (Set String) -> Set String
  alg (TVarF (Right n)) = Set.singleton n
  alg (TLamF (Open (Right n)) x) = del n x
  alg (TLamF (Closed (Right n)) x) = del n x
  alg e = F.fold e
  
  del :: String -> Set String -> Set String
  del n x = case Set.member n x of
              False -> x
              True -> Set.delete n x

-- |`makeLambda ps vl t1` makes a `TLam` around `t1` with `vl` as arguments.
-- Automatic recognition of Close or Open type of `TLam`.
makeLambda :: ParserState -> VarList -> Term1 -> Term1
makeLambda parserState variables term1expr =
  case unbound == Set.empty of
    True -> TLam (Closed (Right $ head variables)) $
              foldr (\n -> TLam (Open (Right n))) term1expr (tail variables)
    _ -> foldr (\n -> TLam (Open (Right n))) term1expr variables
  where v = vars term1expr
        variableSet = Set.fromList variables
        unbound = ((v \\ topLevelBindingNames parserState) \\ variableSet)

-- |Parse lambda expression.
parseLambda :: SILParser Term1
parseLambda = do
  parserState <- State.get
  symbol "\\" <* scn
  variables <- some identifier <* scn
  symbol "->" <* scn
  -- TODO make sure lambda names don't collide with bound names
  term1expr <- parseLongExpr <* scn
  pure $ makeLambda parserState variables term1expr

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
parseLet :: SILParser Term1
parseLet = do
  reserved "let" <* scn
  initialState <- State.get
  lvl <- L.indentLevel
  manyTill (parseSameLvl lvl parseLetAssignment) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  
  intermediateState <- State.get
  let oexpr = optimizeLetBindingsReference intermediateState expr
      oexpr' = applyUntilNoChange (optimizeLetBindingsReference intermediateState) oexpr
  
  State.put initialState
  pure oexpr'

-- |Parse long expression.
parseLongExpr :: SILParser Term1
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseApplied
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: SILParser Term1
parseChurch = (i2c . fromInteger) <$> (symbol "$" *> integer)

parsePartialFix :: SILParser Term1
parsePartialFix = symbol "?" *> pure TLimitedRecursion

-- |Parse refinement check.
parseRefinementCheck :: SILParser (Term1 -> Term1)
parseRefinementCheck = flip TCheck <$> (symbol ":" *> parseLongExpr)

-- |`dropUntil p xs` drops leading elements until `p $ head xs` is satisfied.
dropUntil :: (a -> Bool) -> [a] -> [a]
dropUntil _ [] = []
dropUntil p x@(x1:_) =
  case p x1 of
    False -> dropUntil p (drop 1 x)
    True -> x

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
tagVar :: ParserState -> (ParserState -> Set String) -> String -> Int -> (String, Int)
tagVar ps bindingNames str i = case candidate `Set.member` bindingNames ps of
                                 True -> (fst $ tagVar ps bindingNames str (i + 1), n + i + 1)
                                 False -> (candidate, n + i)
  where
    (name,n) = getTag str
    candidate = name ++ (show $ n + i)

-- |Sateful (Int count) string tagging and keeping track of new names and old names with name collision
-- avoidance.
stag :: ParserState -> (ParserState -> Set String) -> String -> State (Int, VarList, VarList) String
stag ps bindingNames str = do
  (i0, new0, old0) <- State.get
  let (new1, tag1) = tagVar ps bindingNames str (i0 + 1)
  if i0 >= tag1
    then State.modify (\(_, new, old) -> (i0 + 1, new ++ [new1], old ++ [str]))
    else State.modify (\(_, new, old) -> (tag1 + 1, new ++ [new1], old ++ [str]))
  pure new1

-- |Renames top level bindings references found on a `Term1` by tagging them with consecutive `Int`s
-- while keeping track of new names and substituted names.
-- i.e. Let `f` and `g2` be two top level bindings
-- then `\g -> [g,f,g2]` would be renamend to `\g -> [g,f1,g3]` in `Term1` representation.
-- ["f1","g3"] would be the second part of the triplet (new names), and ["f", "g2"] the third part of
-- the triplet (substituted names)
rename :: ParserState -> (ParserState -> Set String) -> Term1 -> (Term1, VarList, VarList)
rename ps bindingNames term1 = (res, newf, oldf)
  where
    toReplace = (vars term1) `Set.intersection` bindingNames ps
    sres = traverseOf (traversed . _Right . filtered (`Set.member` toReplace)) (stag ps bindingNames) term1
    (res, (_, newf, oldf)) = State.runState sres (1,[],[])

-- |Adds bound to `ParserState` if there's no shadowing conflict.
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

-- |Top level bindings encapsulated in an extra outer lambda and applied by it's corresponding
-- original reference.
-- e.g. let `f = zero` be a top level binding in `ParserState` `ps` and let `t1` be the `Term1` representation of
-- `[f,f]`
-- Then `optimizeTopLevelBindingsReference ps t1` will output the `Term1` representation of:
-- (\f1 f2 -> [f1, f2]) f f`
optimizeTopLevelBindingsReference :: ParserState -> Term1 -> Term1
optimizeTopLevelBindingsReference parserState annoExp =
  optimizeBindingsReference parserState topLevelBindingNames (TVar . Right) annoExp

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

parseTopLevelAssignment :: SILParser ()
parseTopLevelAssignment = parseAssignment addTopLevelBound

parseLetAssignment :: SILParser ()
parseLetAssignment = parseAssignment addLetBound

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: (String -> Term1 -> ParserState -> Maybe ParserState) -> SILParser ()
parseAssignment addBound = do
  parserState <- State.get
  var <- identifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  reserved "=" <?> "assignment ="
  expr <- parseLongExpr <* scn
  let annoExp = case annotation of
        Just f -> f expr
        _ -> expr
      appLambdaAnnoExp = optimizeTopLevelBindingsReference parserState annoExp
      assign ps = case addBound var appLambdaAnnoExp ps of
        Just nps -> nps
        _ -> error $ "shadowing of binding not allowed " ++ var
  State.modify assign

 -- |Parse top level expressions.
parseTopLevel :: SILParser Bindings
parseTopLevel = do
  scn *> many parseTopLevelAssignment <* eof
  s <- State.get
  pure . bound $ s

-- |Helper to debug indentation.
debugIndent i = show $ State.runState i (initialPos "debug")

-- |This allows parsing of AST instructions as functions (complete lambdas).
initialMap = fromList
  [ ("zero", TZero)
  , ("left", TLam (Closed (Right "x"))
               (TLeft (TVar (Right "x"))))
  , ("right", TLam (Closed (Right "x"))
                (TRight (TVar (Right "x"))))
  , ("trace", TLam (Closed (Right "x"))
                (TTrace (TVar (Right "x"))))
  , ("pair", TLam (Closed (Right "x"))
               (TLam (Open (Right "y"))
                 (TPair
                   (TVar (Right "x"))
                   (TVar (Right "y")))))
  , ("app", TLam (Closed (Right "x"))
              (TLam (Open (Right "y"))
                (TApp
                  (TVar (Right "x"))
                  (TVar (Right "y")))))
  , ("check", TLam (Closed (Right "x"))
                (TLam (Open (Right "y"))
                  (TCheck
                    (TVar (Right "x"))
                    (TVar (Right "y")))))
  ]

-- |Helper function to test parsers without a result.
runSILParser_ :: Show a => SILParser a -> String -> IO ()
runSILParser_ parser str = do
  let p = State.runStateT parser $ ParserState initialMap Map.empty
  case runParser p "" str of
    Right (a, s) -> do
      let printBindings :: Map String Term1 -> IO ()
          printBindings xs = forM_ (toList xs) $
            \b -> do
              putStr "  "
              putStr . show . fst $ b
              putStr " = "
              putStrLn $ show . snd $ b
      putStrLn ("Result:      " ++ show a)
      putStrLn "Final top level bindings state:"
      printBindings . bound $ s
      putStrLn "Final let bindings state:"
      printBindings . letBound $ s
    Left e -> putStr (errorBundlePretty e)

-- |Helper function to debug parsers without a result.
runSILParserWDebug :: Show a => SILParser a -> String -> IO ()
runSILParserWDebug parser str = do
  let p = State.runStateT parser $ ParserState initialMap Map.empty
  case runParser (dbg "debug" p) "" str of
    Right (a, s) -> do
      putStrLn ("Result:      " ++ show a)
      putStrLn ("Final state: " ++ show s)
    Left e -> putStr (errorBundlePretty e)

-- |Helper function to test parsers with result as String.
runSILParser :: Show a => SILParser a -> String -> IO String
runSILParser parser str = do
  let p = State.runStateT parser $ ParserState initialMap Map.empty
  case runParser p "" str of
    Right (a, s) -> return $ show a
    Left e -> return $ errorBundlePretty e

-- |Helper function to test parsers with `Term1` result.
runSILParserTerm1 :: SILParser Term1 -> String -> IO Term1
runSILParserTerm1 parser str = do
  let p = State.runStateT parser $ ParserState initialMap Map.empty
  case runParser p "" str of
    Right (a, s) -> return a
    Left e -> error $ errorBundlePretty e

-- |Helper function to test if parser was successful.
parseSuccessful :: Show a => SILParser a -> String -> IO Bool
parseSuccessful parser str = do
  let p = State.runStateT parser $ ParserState initialMap Map.empty
  case runParser p "" str of
    Right _ -> return True
    Left _ -> return False


-- resolveAllTopLevel :: Bindings -> Set String -> Term1 -> Term1

-- |Parse with specified prelude.
parseWithPrelude :: Bindings -> String -> Either ErrorString Bindings
parseWithPrelude prelude str = do
  -- TODO: check what happens with overlaping definitions with initialMap
  let startState = ParserState (prelude <> initialMap) (Map.empty)
      -- parseTopLevel' = do
      --   parseTopLevel
        
        
      p = State.runStateT parseTopLevel startState
  case runParser p "" str of
    Right (a, s) -> Right a
    Left x       -> Left $ MkES $ errorBundlePretty x

-- |Parse prelude.
parsePrelude :: String -> Either ErrorString Bindings
parsePrelude = parseWithPrelude initialMap

-- |Parse main.
parseMain :: Bindings -> String -> Either ErrorString Term3
parseMain prelude s = parseWithPrelude prelude s >>= getMain where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> fail "no main method found"
    Just main -> splitExpr <$> debruijinize [] main
      -- do
      -- ps <- State.get
      
      -- let tlv = topLevelBindingNames
      --     main' = resolveAllTopLevel tlv fv main

