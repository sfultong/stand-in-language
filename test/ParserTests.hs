{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor
import Data.Fix (Fix (..))
import qualified Data.List.NonEmpty as NE
import qualified System.IO.Strict as Strict
import Telomare.Expand
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.Parse
import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Parser Tests" [unitTests, expansionTests]

-- |The expansion pass ('Telomare.Expand') as a stage of its own: raw
-- parser output goes in, expanded trees or 'ExpansionError's come out.
expansionTests :: TestTree
expansionTests = testGroup "Expansion pass"
  [ testCase "multi-pattern lambda expands through buildMultiLambda" $ do
      raw <- runTelomareParser parseLongExpr "\\(x, y) z -> x"
      case raw of
        loc :< ParsedTermSugar (LamPatF pats body) ->
          case (,,) <$> traverse (traverse expandPattern) pats
                    <*> expandTerm body
                    <*> expandTerm raw of
            Left err -> assertFailure $ renderExpansionError err
            Right (pats', body', expanded) ->
              stripParserLocs expanded @?= stripParserLocs (buildMultiLambda loc pats' body')
        _ -> assertFailure $ "expected raw LamPatF, got: " <> show raw
  , testCase "annotated pattern lambda binds a CheckF of the argument" $ do
      raw <- runTelomareParser parseLongExpr "\\(v : Bool) -> v"
      case expandTerm raw of
        Right (_ :< UnprocessedParsedTermL (LamF binder
                (_ :< LetUPF
                  [(name, _ :< UnprocessedParsedTermH (CheckF RefinementAbort
                    (_ :< UnprocessedParsedTermL (VarF "Bool"))
                    (_ :< UnprocessedParsedTermL (VarF bound))))]
                  (_ :< UnprocessedParsedTermL (VarF "v")))))
          | locatedNameText name == "v" ->
          bound @?= locatedNameText binder
        other -> assertFailure $ "unexpected expansion: " <> show other
  , testCase "annotations are accepted anywhere in a pattern" $ do
      raw <- runTelomareParser parseLongExpr
        "\\((a : Bool), b) -> case b of\n  (x, (y : Bool)) -> y\n  _ -> a\n"
      case expandTerm raw of
        Right _ -> pure ()
        Left err -> assertFailure $ "unexpected expansion error: " <> renderExpansionError err
  , testCase "a pattern binding a name twice is an ExpansionError" $ do
      raw <- runTelomareParser parseLongExpr "case 0 of\n  (x, x) -> x\n"
      case expandTerm raw of
        Left (DuplicatePatternVariable _ "x") -> pure ()
        other -> assertFailure $ "expected DuplicatePatternVariable: " <> show other
  , testCase "a guard mentioning its own pattern's names is an ExpansionError" $ do
      raw <- runTelomareParser parseLongExpr "case 0 of\n  (x, (y : \\v -> x)) -> y\n"
      case expandTerm raw of
        Left (GuardUsesOwnBinder _ "x") -> pure ()
        other -> assertFailure $ "expected GuardUsesOwnBinder: " <> show other
  , testCase "a guard may bind and use its own names" $ do
      raw <- runTelomareParser parseLongExpr "case 0 of\n  (y : \\y -> let x = y in x) -> y\n"
      case expandTerm raw of
        Right _ -> pure ()
        Left err -> assertFailure $ "unexpected expansion error: " <> renderExpansionError err
  , testCase "refinement annotation folds into CheckF" $ do
      defs <- runTelomareParser parseDefinitions "main : T = 0\n"
      case expandDefs defs of
        Right [(name, _ :< UnprocessedParsedTermH (CheckF RefinementAbort
                 (_ :< UnprocessedParsedTermL (VarF "T"))
                 (_ :< IntUPF 0)))] ->
          locatedNameText name @?= "main"
        other -> assertFailure $ "unexpected expansion: " <> show other
  , testCase "list assignment arity mismatch is an ExpansionError" $ do
      defs <- runTelomareParser parseDefinitions "[a, b] = [1, 2, 3]\n"
      case expandDefs defs of
        Left (ListArityMismatch _ 2 3) -> pure ()
        other -> assertFailure $ "expected ListArityMismatch: " <> show other
  , testCase "repeated literal patterns get distinct lambda binders" $ do
      raw <- runTelomareParser parseExpression "\\0 0 -> 1"
      case expandTerm raw of
        Right (_ :< UnprocessedParsedTermL (LamF firstBinder
                 (_ :< UnprocessedParsedTermL (LamF secondBinder _)))) ->
          assertBool "generated binders must be distinct"
            (locatedNameText firstBinder /= locatedNameText secondBinder)
        other -> assertFailure $ "unexpected pattern lambda expansion: " <> show other
  , testCase "case expansion errors follow pattern-before-body source order" $ do
      raw <- runTelomareParser parseExpression
        "case 0 of (x : let [p] = [1, 2] in p) -> let [a, b] = [1] in x"
      case expandTerm raw of
        Left (ListArityMismatch _ 1 2) -> pure ()
        other -> assertFailure $ "expected pattern annotation error first: " <> show other
  , testCase "module expansion retains typed import and binding locations" $ do
      raw <- either assertFailure pure $
        runParseModule "Example" "import qualified Data.List as L\nmain = 0\n"
      case expandModule raw of
        Right [ ExpandedModuleImport importDecl
              , ExpandedModuleBinding mainName _
              ] -> do
          locatedNameText (parsedImportModule importDecl) @?= "Data.List"
          locatedNameText <$> parsedImportQualifier importDecl @?= Just "L"
          locatedNameText mainName @?= "main"
          assertBool "binding location should survive expansion"
            (locatedNameLoc mainName /= UnknownLoc)
        other -> assertFailure $ "unexpected expanded module: " <> show other
  , testCase "wrapMain without a main definition is MissingMain" $ do
      defs <- runTelomareParser parseDefinitions "foo = 0\n"
      (expandDefs defs >>= wrapMain []) @?= Left MissingMain
  ]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
    -- Keep structured Megaparsec errors available for LSP ranges while
    -- preserving pretty text for CLI-style diagnostics.
  [ testCase "runParseModuleDetailed exposes parse error offsets for diagnostics" $ do
      case runParseModuleDetailed "" "main = if 0 then 1" of
        Left bundle -> do
          errorOffset (NE.head $ bundleErrors bundle) >= 0 @?= True
          null (errorBundlePretty bundle) @?= False
        Right _     -> assertFailure "expected parse error"
    -- Source spans must cover only the token, not whitespace consumed by
    -- lexeme wrappers, otherwise editor diagnostics underline too much.
  , testCase "variable source spans exclude trailing whitespace" $ do
      case runParser parseVariable "" "foo   0" of
        Left err -> assertFailure $ errorBundlePretty err
        Right (SourceLoc srcSpan :< ParsedTermUP (UnprocessedParsedTermL (VarF "foo"))) -> do
          sourcePositionLine (sourceSpanStart srcSpan) @?= 1
          sourcePositionColumn (sourceSpanStart srcSpan) @?= 1
          sourcePositionLine (sourceSpanEnd srcSpan) @?= 1
          sourcePositionColumn (sourceSpanEnd srcSpan) @?= 4
        Right parsed -> assertFailure $ "unexpected parse result: " <> show parsed
  , testCase "let binding source spans exclude trailing whitespace" $ do
      case runParser parseLongExpr "" "let foo   = 0 in foo" of
        Left err -> assertFailure $ errorBundlePretty err
        Right (_ :< ParsedTermSugar (LetSugarF [SingleDefF name Nothing _] _)) | SourceLoc srcSpan <- locatedNameLoc name -> do
          locatedNameText name @?= "foo"
          sourcePositionLine (sourceSpanStart srcSpan) @?= 1
          sourcePositionColumn (sourceSpanStart srcSpan) @?= 5
          sourcePositionLine (sourceSpanEnd srcSpan) @?= 1
          sourcePositionColumn (sourceSpanEnd srcSpan) @?= 8
        Right parsed -> assertFailure $ "unexpected parse result: " <> show parsed
  , testCase "lambda binding source spans exclude trailing whitespace" $ do
      case runParser parseLongExpr "" "\\foo   -> foo" of
        Left err -> assertFailure $ errorBundlePretty err
        Right (_ :< ParsedTermSugar (LamPatF [(binderLoc, Fix (PatternVarF name))] _))
          | locatedNameText name == "foo" -> case binderLoc of
          SourceLoc srcSpan -> do
            sourcePositionLine (sourceSpanStart srcSpan) @?= 1
            sourcePositionColumn (sourceSpanStart srcSpan) @?= 2
            sourcePositionLine (sourceSpanEnd srcSpan) @?= 1
            sourcePositionColumn (sourceSpanEnd srcSpan) @?= 5
          loc -> assertFailure $ "unexpected lambda binder location: " <> show loc
        Right parsed -> assertFailure $ "unexpected parse result: " <> show parsed
  , testCase "complete expressions reject trailing input" $ do
      case runParseExpression "" "0 ???" of
        Left _  -> pure ()
        Right x -> assertFailure $ "accepted trailing input: " <> show x
  , testCase "complete expression-or-definitions rejects trailing input" $ do
      case runParser parseOneExprOrDefinitions "" "0 ???" of
        Left _  -> pure ()
        Right x -> assertFailure $ "accepted trailing input: " <> show x
  , testCase "keywords use the same boundary as identifiers" $ do
      case runParseExpression "" "let in_value = 0 in in_value" of
        Right _  -> pure ()
        Left err -> assertFailure err
  , testCase "oversized natural literals are rejected in every grammar position" $ do
      let tooLarge = show (toInteger (maxBound :: Int) + 1)
          inputs = [tooLarge, "$" <> tooLarge, "\\" <> tooLarge <> " -> 0"]
      forM_ inputs $ \input -> case runParseExpression "" input of
        Left _  -> pure ()
        Right x -> assertFailure $ "accepted oversized literal " <> input <> ": " <> show x
  , testCase "empty list expressions remain valid but empty list definitions do not" $ do
      case (runParseExpression "" "[]", runParseDefinitions "" "[] = []") of
        (Right _, Left _) -> pure ()
        results -> assertFailure $ "unexpected empty-list parse results: " <> show results
  , testCase "module parser returns direct import and definition items" $ do
      case runParseModule "Example" "import qualified Data.List as L\nmain = 0\n" of
        Right [ ModuleImportItem (ImportDecl _ moduleName (Just qualifier))
              , ModuleDefinitionItem (SingleDefF mainName Nothing _)
              ] -> do
          locatedNameText moduleName @?= "Data.List"
          locatedNameText qualifier @?= "L"
          locatedNameText mainName @?= "main"
        other -> assertFailure $ "unexpected raw module: " <> show other
  , testCase "application syntax is left associative" $ do
      case runParseExpression "" "f x y" of
        Right (_ :< ParsedTermUP (UnprocessedParsedTermL (AppF
          (_ :< ParsedTermUP (UnprocessedParsedTermL (AppF
            (_ :< ParsedTermUP (UnprocessedParsedTermL (VarF "f")))
            (_ :< ParsedTermUP (UnprocessedParsedTermL (VarF "x"))))))
          (_ :< ParsedTermUP (UnprocessedParsedTermL (VarF "y")))))) -> pure ()
        other -> assertFailure $ "unexpected application tree: " <> show other
  , testCase "case pattern variables retain source locations" $ do
      case runParseExpression "CaseSource" "case x of (a, b) -> a" of
        Right (_ :< ParsedTermUP (CaseUPF _
          [(Fix (PatternPairF (Fix (PatternVarF a)) (Fix (PatternVarF b))), _)])) -> do
            locatedNameText a @?= "a"
            locatedNameText b @?= "b"
            case (locatedNameLoc a, locatedNameLoc b) of
              (SourceLoc aSpan, SourceLoc bSpan) -> do
                sourceSpanFile aSpan @?= Just "CaseSource"
                sourceSpanFile bSpan @?= Just "CaseSource"
              locs -> assertFailure $ "expected source locations: " <> show locs
        other -> assertFailure $ "unexpected case tree: " <> show other
  , testCase "compound expressions carry complete source spans" $ do
      case runParseExpression "SpanSource" "\\x -> x" of
        Right (SourceLoc srcSpan :< ParsedTermSugar (LamPatF _ _)) -> do
          sourceSpanFile srcSpan @?= Just "SpanSource"
          sourcePositionColumn (sourceSpanStart srcSpan) @?= 1
          sourcePositionColumn (sourceSpanEnd srcSpan) @?= 8
        other -> assertFailure $ "unexpected lambda span: " <> show other
  , testCase "all shipped Telomare programs parse and expand" $ do
      let programs = [ "Prelude.tel"
                     , "test/programs/simpleplus.tel"
                     , "test/programs/ChurchArith.tel"
                     , "tictactoe.tel"
                     , "test/programs/testchar.tel"
                     , "tc_ultra_minimal.tel"
                     , "test/programs/limits/unbounded-input-recursion.tel"
                     , "test/programs/limits/over-budget-recursion.tel"
                     ]
      forM_ programs $ \path -> do
        content <- Strict.readFile path
        case runParseModule path content
               >>= first renderExpansionError . expandModule of
          Right _  -> pure ()
          Left err -> assertFailure $ path <> ": " <> err
  , testCase "surface Show is total for empty collections" $ do
      assertBool "empty list should render"
        ((not . null . show) ((UnknownLoc :< ListUPF []) :: ExpandedSurfaceTerm))
  , testCase "test function applied to a string that has whitespaces in both sides inside a structure" $ do
      res1 <- parseSuccessful parseLongExpr "(foo \"woops\" , 0)"
      res2 <- parseSuccessful parseLongExpr "(foo \"woops\" )"
      res3 <- parseSuccessful parseLongExpr "if 0 then foo \"woops\" else 0"
      res4 <- parseSuccessful parseLongExpr "[ foo \"woops\" ]"
      (res1 && res2 && res3 && res4) `compare` True @?= EQ
  , testCase "test Pair 0" $ do
      res <- parseSuccessful (parsePair >> eof) testPair0
      res @?= True
  , testCase "test ITE 1" $ do
      res <- parseSuccessful parseITE testITE1
      res @?= True
  , testCase "test ITE 2" $ do
      res <- parseSuccessful parseITE testITE2
      res @?= True
  , testCase "test ITE 3" $ do
      res <- parseSuccessful parseITE testITE3
      res @?= True
  , testCase "test ITE 4" $ do
      res <- parseSuccessful parseITE testITE4
      res @?= True
  , testCase "test ITE with Pair" $ do
      res <- parseSuccessful parseITE testITEwPair
      res @?= True
  , testCase "test if Complete Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testCompleteLambdawITEwPair
      res @?= True
  , testCase "test if Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testLambdawITEwPair
      res @?= True
  , testCase "test parse assignment with Complete Lambda with ITE with Pair" $ do
      res <- parseSuccessful (parseDefinitions <* eof) testParseAssignmentwCLwITEwPair1
      res @?= True
  , testCase "test if testParseTopLevelwCLwITEwPair parses successfuly" $ do
      res <- parseSuccessful (parseDefinitions <* eof) testParseTopLevelwCLwITEwPair
      res @?= True
  , testCase "test main2Term3 with CL with ITE with Pair parses" $ do
      res <- runTestMainwCLwITEwPair
      res @?= True
  , testCase "testList0" $ do
      res <- parseSuccessful parseList testList0
      res @?= True
  , testCase "testList1" $ do
      res <- parseSuccessful parseList testList1
      res @?= True
  , testCase "testList2" $ do
      res <- parseSuccessful parseList testList2
      res @?= True
  , testCase "testList3" $ do
      res <- parseSuccessful parseList testList3
      res @?= True
  , testCase "testList4" $ do
      res <- parseSuccessful parseList testList4
      res @?= True
  , testCase "testList5" $ do
      res <- parseSuccessful parseList testList5
      res @?= True
  , testCase "test parse Prelude.tel" $ do
      res <- runTestParsePrelude
      res @?= True
  , testCase "test parse tictactoe.tel" $ do
      res <- testWtictactoe
      res @?= True
  , testCase "test Main with Type" $ do
      res <- runTestMainWType
      res @?= True
  , testCase "testShowBoard0" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard0
      res @?= True
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard1
      res @?= True
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard2
      res @?= True
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard3
      res @?= True
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard4
      res @?= True
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard5
      res @?= True
  , testCase "testShowBoard6" $ do
      res <- parseSuccessful parseApplied testShowBoard6
      res @?= True
  , testCase "testLetShowBoard0" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard0
      res @?= True
  , testCase "testLetShowBoard1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard1
      res @?= True
  , testCase "testLetShowBoard2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard2
      res @?= True
  , testCase "testLetShowBoard3" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard3
      res @?= True
  , testCase "testLetShowBoard4" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testLetShowBoard4
      res @?= True
  , testCase "testLetShowBoard5" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard5
      res @?= True
  , testCase "testLetShowBoard8" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard8
      res @?= True
  , testCase "testLetShowBoard9" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard9
      res @?= True
  , testCase "AST terms as functions" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app left (pair zero zero)"
      res @?= True
  , testCase "left with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "left (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res @?= True
  , testCase "right with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "right (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res @?= True
  , testCase "trace with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "trace (\\x -> (\\y -> (x,y))) 0 0"
      res @?= True
  , testCase "app with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app (\\x y z -> x) 0 1 2"
      res @?= True
  , testCase "testLetIndentation" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIndentation
      res @?= True
  , testCase "testLetIncorrectIndentation1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation1
      res `compare` False @?= EQ
  , testCase "testLetIncorrectIndentation2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation2
      res `compare` False @?= EQ
  , testCase "Case within top level definitions" $ do
      defs <- runTelomareParser parseDefinitions caseExpr0
      case expandDefs defs >>= wrapMain [] of
        Left err  -> assertFailure $ renderExpansionError err
        Right res -> stripParserLocs res @?= caseExpr0UPT
  ]

stripParserLocs :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
stripParserLocs (_loc :< term) = UnknownLoc :< case term of
  LetUPF bindings body -> LetUPF ((\(name, value) -> (locatedName UnknownLoc $ locatedNameText name, stripParserLocs value)) <$> bindings) (stripParserLocs body)
  UnprocessedParsedTermL (LamF name body) -> UnprocessedParsedTermL (LamF (locatedName UnknownLoc $ locatedNameText name) (stripParserLocs body))
  CaseUPF scrutinee cases -> CaseUPF (stripParserLocs scrutinee) (bimap stripPatternLocs stripParserLocs <$> cases)
  other -> stripParserLocs <$> other

stripPatternLocs :: PatternA -> PatternA
stripPatternLocs (Fix patternF) = Fix $ case patternF of
  PatternVarF name -> PatternVarF (locatedName UnknownLoc $ locatedNameText name)
  PatternAnnotatedF pat term -> PatternAnnotatedF (stripPatternLocs pat) (AnnotatedEST . stripParserLocs $ unAnnotatedEST term)
  other -> stripPatternLocs <$> other

caseExpr0UPT :: ExpandedSurfaceTerm
caseExpr0UPT =
  UnknownLoc :< LetUPF
    [ ( locatedName UnknownLoc "foo"
      , UnknownLoc :< UnprocessedParsedTermL (LamF (locatedName UnknownLoc "a")
          (UnknownLoc :< CaseUPF (UnknownLoc :< UnprocessedParsedTermL (VarF "a"))
            [ (Fix $ PatternIntF 0, UnknownLoc :< UnprocessedParsedTermL (VarF "a"))
            , (Fix $ PatternVarF (locatedName UnknownLoc "x"), UnknownLoc :< UnprocessedParsedTermL (AppF (UnknownLoc :< UnprocessedParsedTermL (VarF "succ")) (UnknownLoc :< UnprocessedParsedTermL (VarF "a"))))
            ]))
      )
    , ( locatedName UnknownLoc "main"
      , UnknownLoc :< UnprocessedParsedTermL (LamF (locatedName UnknownLoc "i")
          (UnknownLoc :< UnprocessedParsedTermB (PairSF (UnknownLoc :< StringUPF "Success") (UnknownLoc :< IntUPF 0))))
      )
    ]
    (UnknownLoc :< UnprocessedParsedTermL (LamF (locatedName UnknownLoc "i")
      (UnknownLoc :< UnprocessedParsedTermB (PairSF (UnknownLoc :< StringUPF "Success") (UnknownLoc :< IntUPF 0)))))
caseExpr0 :: String
caseExpr0 = unlines
  [ "foo = \\a -> case a of"
  , "              0 -> a"
  , "              x -> succ a"
  , ""
  , "main = \\i -> (\"Success\", 0)"
  ]

test2UPT :: Monad m => String -> m Bool
test2UPT str =
  case runParseModule "" str
         >>= first renderExpansionError . expandModule of
    Right _ -> return True
    Left _  -> return False

testWtictactoe :: IO Bool
testWtictactoe = Strict.readFile "tictactoe.tel" >>= test2UPT

runTestMainwCLwITEwPair :: IO Bool
runTestMainwCLwITEwPair = test2UPT testMainwCLwITEwPair

runTestMainWType :: IO Bool
runTestMainWType = test2UPT "main : (\\x -> if x then \"fail\" else 0) = 0"

testLetIndentation :: String
testLetIndentation = unlines
  [ "let x = 0"
  , "    y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation1 :: String
testLetIncorrectIndentation1 = unlines
  [ "let x = 0"
  , "  y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation2 :: String
testLetIncorrectIndentation2 = unlines
  [ "let x = 0"
  , "      y = 1"
  , "in (x,y)"
  ]

testPair0 :: String
testPair0 = "(\"Hello World!\", \"0\")"

testITE1 :: String
testITE1 = unlines
  [ "if"
  , "  1"
  , "then 1"
  , "else"
  , "  2"
  ]
testITE2 :: String
testITE2 = unlines
  [ "if 1"
  , "  then"
  , "                1"
  , "              else 2"
  ]
testITE3 :: String
testITE3 = unlines
  [ "if 1"
  , "   then"
  , "                1"
  , "              else 2"
  ]
testITE4 :: String
testITE4 = unlines
  [ "if 1"
  , "    then"
  , "                1"
  , "              else 2"
  ]

testITEwPair :: String
testITEwPair = unlines
  [ "if"
  , "    1"
  , "  then (\"Hello, world!\", 0)"
  , "  else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testCompleteLambdawITEwPair :: String
testCompleteLambdawITEwPair = unlines
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testLambdawITEwPair :: String
testLambdawITEwPair = unlines
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

runTestParsePrelude :: IO Bool
runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.tel"
  case runParseDefinitions "" preludeFile
         >>= first renderExpansionError . expandDefs of
    Right _ -> return True
    Left _  -> return False

testParseAssignmentwCLwITEwPair1 :: String
testParseAssignmentwCLwITEwPair1 = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "       (\"Hello, world!\", 0)"
  , "     else (\"Goodbye, world!\", 0)"
  ]

testParseTopLevelwCLwITEwPair :: String
testParseTopLevelwCLwITEwPair = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMainwCLwITEwPair :: String
testMainwCLwITEwPair = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testList0 :: String
testList0 = unlines [ "[ 0"
  , ", 1"
  , ", 2"
  , "]"
  ]

testList1 :: String
testList1 = "[0,1,2]"

testList2 :: String
testList2 = "[ 0 , 1 , 2 ]"

testList3 :: String
testList3 = unlines
  [ "[ 0 , 1"
  , ", 2 ]"
  ]

testList4 :: String
testList4 = unlines
  [ "[ 0 , 1"
  , ",2 ]"
  ]

testList5 :: String
testList5 = unlines
  [ "[ 0,"
  , "  1,"
  , "  2 ]"
  ]

testShowBoard0 :: String
testShowBoard0 = unlines
  [ "main = or (and validPlace"
  , "                    (and (not winner)"
  , "                         (not filledBoard)))"
  , "          (1)"
  ]

testShowBoard1 :: String
testShowBoard1 = unlines
  [ "main = or (0)"
  , "               (1)"
  ]

testShowBoard2 :: String
testShowBoard2 = unlines
  [ "main = or (and 1"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard3 :: String
testShowBoard3 = unlines
  [ "main = or (and x"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard4 :: String
testShowBoard4 = unlines
  [ "main = or (and x"
  , "                    (or 0"
  , "                        (1)))"
  , "               (1)"
  ]

testShowBoard5 :: String
testShowBoard5 = unlines
  [ "main = or (or x"
  , "                   (or 0"
  , "                       1))"
  , "               (1)"
  ]

testLetShowBoard0 :: String
testLetShowBoard0 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        (and (not winner)"
  , "                             (not filledBoard)"
  , "                        )"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard1 :: String
testLetShowBoard1 = unlines
  [ "let showBoard = or (0)"
  , "                   (1)"
  , "in 0"
  ]

testLetShowBoard2 :: String
testLetShowBoard2 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard3 :: String
testLetShowBoard3 = unlines
  [ "or (and 1"
  , "        1"
  , "   )"
  , "   (not boardIn)"
  ]

testLetShowBoard4 :: String
testLetShowBoard4 = unlines
  [ "main = or (and 0"
  , "                    1)"
  , "               (not boardIn)"
  ]

testLetShowBoard5 :: String
testLetShowBoard5 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1)"
  , "                   (not boardIn)"
  , "in 0"
  ]

testShowBoard6 :: String
testShowBoard6 = unlines
  [ "or (or x"
  , "       (or 0"
  , "           1))"
  , "   (1)"
  ]

testLetShowBoard8 :: String
testLetShowBoard8 = unlines
  [ "or (0"
  , "   )"
  , "   1"
  ]
testLetShowBoard9 :: String
testLetShowBoard9 = unlines
  [ "or 0"
  , "   1"
  ]
