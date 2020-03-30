module Main where

import SIL
import SIL.Parser
import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec.Error
import Text.Megaparsec
import Text.Megaparsec.Debug
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Functor.Foldable
import qualified SIL.Parser as Parsec
import qualified System.IO.Strict as Strict
import qualified Control.Monad.State as State

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests = testGroup "Unit tests"
  [ testCase "test Pair 0" $ do
      res <- parseSuccessful (parsePair >> eof) testPair0
      res `compare` True @?= EQ
  ,testCase "test ITE 1" $ do
      res <- parseSuccessful parseITE testITE1
      res `compare` True @?= EQ
  , testCase "test ITE 2" $ do
      res <- parseSuccessful parseITE testITE2
      res `compare` True @?= EQ
  , testCase "test ITE 3" $ do
      res <- parseSuccessful parseITE testITE3
      res `compare` True @?= EQ
  , testCase "test ITE 4" $ do
      res <- parseSuccessful parseITE testITE4
      res `compare` True @?= EQ
  , testCase "test ITE with Pair" $ do
      res <- parseSuccessful parseITE testITEwPair
      res `compare` True @?= EQ
  , testCase "test if Complete Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testCompleteLambdawITEwPair
      res `compare` True @?= EQ
  , testCase "test if Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testLambdawITEwPair
      res `compare` True @?= EQ
  , testCase "test parse assignment with Complete Lambda with ITE with Pair" $ do
      res <- parseSuccessful (parseAssignment <* eof) testParseAssignmentwCLwITEwPair1
      res `compare` True @?= EQ
  , testCase "test if testParseTopLevelwCLwITEwPair parses successfuly" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseTopLevelwCLwITEwPair
      res `compare` True @?= EQ
  , testCase "test parseMain with CL with ITE with Pair parses" $ do
      res <- runTestMainwCLwITEwPair
      res `compare` True @?= EQ
  , testCase "testList0" $ do
      res <- parseSuccessful parseList testList0
      res `compare` True @?= EQ
  , testCase "testList1" $ do
      res <- parseSuccessful parseList testList1
      res `compare` True @?= EQ
  , testCase "testList2" $ do
      res <- parseSuccessful parseList testList2
      res `compare` True @?= EQ
  , testCase "testList3" $ do
      res <- parseSuccessful parseList testList3
      res `compare` True @?= EQ
  , testCase "testList4" $ do
      res <- parseSuccessful parseList testList4
      res `compare` True @?= EQ
  , testCase "testList5" $ do
      res <- parseSuccessful parseList testList5
      res `compare` True @?= EQ
  , testCase "test parse Prelude.sil" $ do
      res <- runTestParsePrelude
      res `compare` True @?= EQ
  , testCase "test parse tictactoe.sil" $ do
      res <- testWtictactoe
      res `compare` True @?= EQ
  , testCase "test Main with Type" $ do
      res <- runTestMainWType
      res `compare` True @?= EQ
  , testCase "testShowBoard0" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testShowBoard0
      res `compare` True @?= EQ
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testShowBoard1
      res `compare` True @?= EQ
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testShowBoard2
      res `compare` True @?= EQ
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testShowBoard3
      res `compare` True @?= EQ
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testShowBoard4
      res `compare` True @?= EQ
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testShowBoard5
      res `compare` True @?= EQ
  , testCase "testShowBoard6" $ do
      res <- parseSuccessful (parseApplied) testShowBoard6
      res `compare` True @?= EQ
  , testCase "testLetShowBoard0" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard0
      res `compare` True @?= EQ
  , testCase "testLetShowBoard1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard1
      res `compare` True @?= EQ
  , testCase "testLetShowBoard2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard2
      res `compare` True @?= EQ
  , testCase "testLetShowBoard3" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard3
      res `compare` True @?= EQ
  , testCase "testLetShowBoard4" $ do
      res <- parseSuccessful (parseAssignment <* scn <* eof) testLetShowBoard4
      res `compare` True @?= EQ
  , testCase "testLetShowBoard5" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard5
      res `compare` True @?= EQ
  , testCase "testLetShowBoard7" $ do
      res <- parseSuccessful (parseAssignment <* scn <* parseNumber <* scn <* eof) testLetShowBoard7
      res `compare` True @?= EQ
  , testCase "testLetShowBoard8" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard8
      res `compare` True @?= EQ
  , testCase "testLetShowBoard9" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard9
      res `compare` True @?= EQ
  , testCase "AST terms as functions" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app left (pair zero zero)"
      res `compare` True @?= EQ
  , testCase "left with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "left (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res `compare` True @?= EQ
  , testCase "right with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "right (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res `compare` True @?= EQ
  , testCase "trace with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "trace (\\x -> (\\y -> (x,y))) 0 0"
      res `compare` True @?= EQ
  , testCase "app with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app (\\x y z -> x) 0 1 2"
      res `compare` True @?= EQ
  , testCase "testLetIndentation" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIndentation
      res `compare` True @?= EQ
  , testCase "testLetIncorrectIndentation1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation1
      res `compare` False @?= EQ
  , testCase "testLetIncorrectIndentation2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation2
      res `compare` False @?= EQ
  , testCase "collect vars" $ do
      let fv = vars expr
      fv `compare` (Set.empty) @?= EQ
  , testCase "collect vars many x's" $ do
      let fv = vars expr1
      fv `compare` (Set.empty) @?= EQ
  , testCase "test automatic open close lambda" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x -> \\y -> (x, y)"
      res `compare` closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 2" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x y -> (x, y)"
      res `compare` closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 3" $ do
      res <- runSILParserTerm1 (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> z"
      res `compare` expr6 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runSILParserTerm1 (parseLambda <* scn <* eof) "\\x -> (x, x)"
      res `compare` expr5 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runSILParserTerm1 (parseLambda <* scn <* eof) "\\x -> \\x -> \\x -> x"
      res `compare` expr4 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runSILParserTerm1 (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> [x,y,z]"
      res `compare` expr3 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runSILParserTerm1 (parseLambda <* scn <* eof) "\\a -> (a, (\\a -> (a,0)))"
      res `compare` expr2 @?= EQ
  ]

-- | SIL Parser AST representation of: \x -> \y -> \z -> z
expr6 = Fix (TLam (Closed (Right "x"))
              (Fix (TLam (Closed (Right "y"))
                     (Fix (TLam (Closed (Right "z"))
                            (Fix (TVar (Right "z"))))))))

-- | SIL Parser AST representation of: \x -> (x, x)
expr5 = Fix (TLam (Closed (Right "x"))
              (Fix (TPair
                     (Fix (TVar (Right "x")))
                     (Fix (TVar (Right "x"))))))

-- | SIL Parser AST representation of: \x -> \x -> \x -> x
expr4 = Fix (TLam (Closed (Right "x"))
              (Fix (TLam (Closed (Right "x"))
                     (Fix (TLam (Closed (Right "x"))
                            (Fix (TVar (Right "x"))))))))

-- | SIL Parser AST representation of: \x -> \y -> \z -> [x,y,z]
expr3 = Fix (TLam (Closed (Right "x"))
              (Fix (TLam (Open (Right "y"))
                     (Fix (TLam (Open (Right "z"))
                            (Fix (TPair
                                   (Fix (TVar (Right "x")))
                                   (Fix (TPair
                                          (Fix (TVar (Right "y")))
                                          (Fix (TPair
                                                 (Fix (TVar (Right "z")))
                                                 (Fix TZero))))))))))))

-- | SIL Parser AST representation of: \a -> (a, (\a -> (a,0)))
expr2 = Fix (TLam (Closed (Right "a"))
              (Fix (TPair
                     (Fix (TVar (Right "a")))
                     (Fix (TLam (Closed (Right "a"))
                            (Fix (TPair
                                   (Fix (TVar (Right "a")))
                                   (Fix TZero))))))))


-- | SIL Parser AST representation of: \x -> [x, x, x]
expr1 = Fix (TLam (Closed (Right "x"))
             (Fix (TPair
                    (Fix (TVar (Right "x")))
                    (Fix (TPair
                           (Fix (TVar (Right "x")))
                           (Fix (TPair
                                  (Fix (TVar (Right "x")))
                                  (Fix TZero))))))))

expr = Fix (TLam (Closed (Right "x"))
                   (Fix (TLam (Open (Right "y"))
                          (Fix (TPair
                                 (Fix (TVar (Right "x")))
                                 (Fix (TVar (Right "y"))))))))

range = unlines
  [ "range = \\a b -> let layer = \\recur i -> if dMinus b i"
  , "                                           then (i, recur (i,0))"
  , "                                           else 0"
  , "                in ? layer (\\i -> 0) a"
  , "r = range 2 5"
  ]

closedLambdaPair = "Fix (TLam (Closed (Right \"x\")) (Fix (TLam (Open (Right \"y\")) (Fix (TPair (Fix (TVar (Right \"x\"))) (Fix (TVar (Right \"y\"))))))))"

testLetIndentation = unlines
  [ "let x = 0"
  , "    y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation1 = unlines
  [ "let x = 0"
  , "  y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation2 = unlines
  [ "let x = 0"
  , "      y = 1"
  , "in (x,y)"
  ]


runTestPair :: String -> IO String
runTestPair = runSILParser parsePair

testPair0 = "(\"Hello World!\", \"0\")"

testPair1 = unlines
  [ "("
  , " \"Hello World!\""
  , ", \"0\""
  , ")"
  ]

testITE1 = unlines $
  [ "if"
  , "  1"
  , "then 1"
  , "else"
  , "  2"
  ]
testITE2 = unlines $
  [ "if 1"
  , "  then"
  , "                1"
  , "              else 2"
  ]
testITE3 = unlines $
  [ "if 1"
  , "   then"
  , "                1"
  , "              else 2"
  ]
testITE4 = unlines $
  [ "if 1"
  , "    then"
  , "                1"
  , "              else 2"
  ]

testITEwPair = unlines $
  [ "if"
  , "    1"
  , "  then (\"Hello, world!\", 0)"
  , "  else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testCompleteLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.sil"
  case parsePrelude preludeFile of
    Right _ -> return True
    Left _ -> return False

testParseAssignmentwCLwITEwPair2 = unlines $
  [ "main = \\input -> if 1"
  , "                  then"
  , "                   (\"Hello, world!\", 0)"
  , "                  else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair3 = unlines $
  [ "main = \\input ->"
  , "  if 1"
  , "   then"
  , "     (\"Hello, world!\", 0)"
  , "   else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair4 = unlines $
  [ "main = \\input"
  , "-> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair5 = unlines $
  [ "main"
  , "  = \\input"
  , "-> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair6 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair7 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "       then"
  , "             (\"Hello, world!\", 0)"
  , "           else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair1 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "       (\"Hello, world!\", 0)"
  , "     else (\"Goodbye, world!\", 0)"
  ]

testParseTopLevelwCLwITEwPair = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMainwCLwITEwPair = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMain3 = "main = 0"

test4 = "(\\x -> if x then \"f\" else 0)"
test5 = "\\x -> if x then \"f\" else 0"
test6 = "if x then \"1\" else 0"
test7 = unlines $
  [ "if x then \"1\""
  , "else 0"
  ]
test8 = "if x then 1 else 0"

runTestMainwCLwITEwPair = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  case parseMain prelude testMainwCLwITEwPair of
    Right x -> return True
    Left err -> return False

testMain2 = "main : (\\x -> if x then \"fail\" else 0) = 0"

runTestMainWType = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  case parseMain prelude $ testMain2 of
    Right x -> return True
    Left err -> return False

testList0 = unlines $
  [ "[ 0"
  , ", 1"
  , ", 2"
  , "]"
  ]

testList1 = "[0,1,2]"

testList2 = "[ 0 , 1 , 2 ]"

testList3 = unlines $
  [ "[ 0 , 1"
  , ", 2 ]"
  ]

testList4 = unlines $
  [ "[ 0 , 1"
  , ",2 ]"
  ]

testList5 = unlines $
  [ "[ 0,"
  , "  1,"
  , "  2 ]"
  ]

-- |Usefull to see if tictactoe.sil was correctly parsed
-- and was usefull to compare with the deprecated SIL.Parser
-- Parsec implementation
testWtictactoe = do
  preludeFile <- Strict.readFile "Prelude.sil"
  tictactoe <- Strict.readFile "tictactoe.sil"
  let
    prelude = case parsePrelude preludeFile of
                Right p -> p
                Left pe -> error . getErrorString $ pe
  case parseMain prelude tictactoe of
    Right _ -> return True
    Left _ -> return False

-- -- |Helper function to debug tictactoe.sil
-- debugTictactoe :: IO ()
-- debugTictactoe  = do
--   preludeFile <- Strict.readFile "Prelude.sil"
--   tictactoe <- Strict.readFile "tictactoe.sil"
--   let prelude =
--         case parsePrelude preludeFile of
--           Right pf -> pf
--           Left pe -> error . getErrorString $ pe
--       p str = State.runStateT $ parseMain prelude str
--   case runParser (dbg "debug" p) "" tictactoe of
--     Right (a, s) -> do
--       putStrLn ("Result:      " ++ show a)
--       putStrLn ("Final state: " ++ show s)
--     Left err -> putStr (errorBundlePretty err)

runTictactoe = do
  preludeFile <- Strict.readFile "Prelude.sil"
  tictactoe <- Strict.readFile "tictactoe.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  case parseMain prelude $ tictactoe of
    Right x -> putStrLn $ show x
    Left err -> putStrLn . getErrorString $ err

testITEParsecResult = "TITE (TPair TZero TZero) (TPair TZero TZero) (TPair (TPair TZero TZero) TZero)"

testShowBoard0 = unlines
  [ "showBoard = or (and validPlace"
  , "                    (and (not winner)"
  , "                         (not filledBoard)"
  , "                    )"
  , "               )"
  , "               (1)"
  ]

testShowBoard1 = unlines
  [ "showBoard = or (0)"
  , "               (1)"
  ]

testShowBoard2 = unlines
  [ "showBoard = or (and 1"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard3 = unlines
  [ "showBoard = or (and x"
  , "                    0)"
  , "               (1)"
  ]

testLetShowBoard0 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        (and (not winner)"
  , "                             (not filledBoard)"
  , "                        )"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard1 = unlines
  [ "let showBoard = or (0)"
  , "                   (1)"
  , "in 0"
  ]

testLetShowBoard3 = unlines
  [ "or (and 1"
  , "        1"
  , "   )"
  , "   (not boardIn)"
  ]

testLetShowBoard5 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1)"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard2 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard7 = unlines
  [ "showBoard = or (and validPlace"
  , "                    1"
  , "               )"
  , "               (not boardIn)"
  , "0"
  ]

testLetShowBoard4 = unlines
  [ "showBoard = or (and 0"
  , "                    1"
  , "               )"
  , "               (not boardIn)"
  ]

testLetShowBoard8 = unlines
  [ "or (0"
  , "   )"
  , "   1"
  ]
testLetShowBoard9 = unlines
  [ "or 0"
  , "   1"
  ]

testShowBoard6 = unlines
  [ "or (or x"
  , "       (or 0"
  , "           1))"
  , "   (1)"
  ]

testShowBoard4 = unlines
  [ "showBoard = or (and x"
  , "                    (or 0"
  , "                        (1)))"
  , "               (1)"
  ]

testShowBoard5 = unlines
  [ "showBoard = or (or x"
  , "                   (or 0"
  , "                       1))"
  , "               (1)"
  ]
