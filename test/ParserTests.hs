{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Common
import Control.Lens.Fold
import Control.Lens.Plated
import Control.Monad

import Control.Monad.Fix (fix)
import Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.State as State
import Data.Bifunctor
import Data.Either (fromRight)
import Data.Functor.Foldable
import Data.List
import Data.Map (Map, fromList, toList)
import qualified Data.Map as Map
import Data.Ord
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
import Debug.Trace (trace, traceShowId)
import qualified System.IO.Strict as Strict
import System.Process hiding (createPipe)
import Telomare
import Telomare.Eval
import Telomare.Parser
import Telomare.Resolver
import Telomare.RunTime
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Megaparsec
import Text.Megaparsec.Debug
import Text.Megaparsec.Error

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Parser Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "parse uniqueUP" $ do
      res <- parseSuccessful parseHash "# (\\x -> x)"
      res `compare` True @?= EQ
  , testCase "test function applied to a string that has whitespaces in both sides inside a structure" $ do
      res1 <- parseSuccessful parseLongExpr "(foo \"woops\" , 0)"
      res2 <- parseSuccessful parseLongExpr "(foo \"woops\" )"
      res3 <- parseSuccessful parseLongExpr "if 0 then foo \"woops\" else 0"
      res4 <- parseSuccessful parseLongExpr "[ foo \"woops\" ]"
      (res1 && res2 && res3 && res4) `compare` True @?= EQ
  , testCase "test Pair 0" $ do
      res <- parseSuccessful (parsePair >> eof) testPair0
      res `compare` True @?= EQ
  , testCase "test ITE 1" $ do
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
      res <- parseSuccessful (parseTopLevel <* eof) testParseAssignmentwCLwITEwPair1
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
  , testCase "test parse Prelude.tel" $ do
      res <- runTestParsePrelude
      res `compare` True @?= EQ
  , testCase "test parse tictactoe.tel" $ do
      res <- testWtictactoe
      res `compare` True @?= EQ
  , testCase "test Main with Type" $ do
      res <- runTestMainWType
      res `compare` True @?= EQ
  , testCase "testShowBoard0" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard0
      res `compare` True @?= EQ
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard1
      res `compare` True @?= EQ
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard2
      res `compare` True @?= EQ
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard3
      res `compare` True @?= EQ
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard4
      res `compare` True @?= EQ
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard5
      res `compare` True @?= EQ
  , testCase "testShowBoard6" $ do
      res <- parseSuccessful parseApplied testShowBoard6
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
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testLetShowBoard4
      res `compare` True @?= EQ
  , testCase "testLetShowBoard5" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard5
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
  ]

-- |Usefull to see if tictactoe.tel was correctly parsed
-- and was usefull to compare with the deprecated Telomare.Parser
-- Parsec implementation
testWtictactoe = do
  preludeFile <- Strict.readFile "Prelude.tel"
  tictactoe <- Strict.readFile "tictactoe.tel"
  let
    prelude = case parsePrelude preludeFile of
                Right p -> p
                Left pe -> error pe
  case parseMain prelude tictactoe of
    Right _ -> return True
    Left _  -> return False

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

testPair0 = "(\"Hello World!\", \"0\")"

testITE1 = unlines
  [ "if"
  , "  1"
  , "then 1"
  , "else"
  , "  2"
  ]
testITE2 = unlines
  [ "if 1"
  , "  then"
  , "                1"
  , "              else 2"
  ]
testITE3 = unlines
  [ "if 1"
  , "   then"
  , "                1"
  , "              else 2"
  ]
testITE4 = unlines
  [ "if 1"
  , "    then"
  , "                1"
  , "              else 2"
  ]

testITEwPair = unlines
  [ "if"
  , "    1"
  , "  then (\"Hello, world!\", 0)"
  , "  else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testCompleteLambdawITEwPair = unlines
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testLambdawITEwPair = unlines
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.tel"
  case parsePrelude preludeFile of
    Right _ -> return True
    Left _  -> return False

testParseAssignmentwCLwITEwPair1 = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "       (\"Hello, world!\", 0)"
  , "     else (\"Goodbye, world!\", 0)"
  ]

testParseTopLevelwCLwITEwPair = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMainwCLwITEwPair = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

runTestMainwCLwITEwPair = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error pe
  case parseMain prelude testMainwCLwITEwPair of
    Right x  -> return True
    Left err -> return False

runTestMainWType = do
  let testMain2 = "main : (\\x -> if x then \"fail\" else 0) = 0"
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error pe
  case parseMain prelude testMain2 of
    Right x  -> return True
    Left err -> return False

testList0 = unlines [ "[ 0"
  , ", 1"
  , ", 2"
  , "]"
  ]

testList1 = "[0,1,2]"

testList2 = "[ 0 , 1 , 2 ]"

testList3 = unlines
  [ "[ 0 , 1"
  , ", 2 ]"
  ]

testList4 = unlines
  [ "[ 0 , 1"
  , ",2 ]"
  ]

testList5 = unlines
  [ "[ 0,"
  , "  1,"
  , "  2 ]"
  ]

-- TODO: does it matter that one parses succesfuly and the other doesnt?
parseApplied0 = unlines
  [ "foo (bar baz"
  , "     )"
  ]
parseApplied1 = unlines
  [ "foo (bar baz"
  , "         )"
  ]


testShowBoard0 = unlines
  [ "main = or (and validPlace"
  , "                    (and (not winner)"
  , "                         (not filledBoard)))"
  , "          (1)"
  ]

testShowBoard1 = unlines
  [ "main = or (0)"
  , "               (1)"
  ]

testShowBoard2 = unlines
  [ "main = or (and 1"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard3 = unlines
  [ "main = or (and x"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard4 = unlines
  [ "main = or (and x"
  , "                    (or 0"
  , "                        (1)))"
  , "               (1)"
  ]

testShowBoard5 = unlines
  [ "main = or (or x"
  , "                   (or 0"
  , "                       1))"
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

testLetShowBoard2 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard3 = unlines
  [ "or (and 1"
  , "        1"
  , "   )"
  , "   (not boardIn)"
  ]

testLetShowBoard4 = unlines
  [ "main = or (and 0"
  , "                    1)"
  , "               (not boardIn)"
  ]

testLetShowBoard5 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1)"
  , "                   (not boardIn)"
  , "in 0"
  ]

testShowBoard6 = unlines
  [ "or (or x"
  , "       (or 0"
  , "           1))"
  , "   (1)"
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
