module ParserTests where

import SIL.ParserMegaparsec
import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as Map
import qualified SIL.Parser as Parsec
import qualified System.IO.Strict as Strict

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests = testGroup "Unit tests"
  [ testCase "test Pair 0" $ do
      res <- runTestPair testPair0
      let Right resParsec' = Parsec.runParsecParser Parsec.parsePair testPair0
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  ,testCase "test ITE 1" $ do
      res <- runTestITE testITE1
      let Right resParsec' = Parsec.runParsecParser Parsec.parseITE testITE2
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test ITE 2" $ do
      res <- runTestITE testITE2
      let Right resParsec' = Parsec.runParsecParser Parsec.parseITE testITE2
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test ITE 3" $ do
      res <- runTestITE testITE3
      let Right resParsec' = Parsec.runParsecParser Parsec.parseITE testITE3
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
    -- Maybe TODO: Maybe Fix
    -- Probably thinks "then" is part of an assignment
  , testCase "test ITE 4" $ do
      res <- runTestITE testITE4
      let Right resParsec' = Parsec.runParsecParser Parsec.parseITE testITE4
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test ITE with Pair" $ do
      res <- runSILParser parseITE testITEwPair
      let Right resParsec' = Parsec.runParsecParser Parsec.parseITE testITEwPair
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test Complete Lambda with ITE Pair" $ do
      res <- runSILParser parseCompleteLambda testCompleteLambdawITEwPair
      let Right resParsec' = Parsec.runParsecParser Parsec.parseCompleteLambda testCompleteLambdawITEwPair
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test Lambda with ITE Pair" $ do
      res <- runSILParser parseLambda testLambdawITEwPair
      let Right resParsec' = Parsec.runParsecParser Parsec.parseLambda testLambdawITEwPair
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test parse Prelude.sil" $ do
      res <- runTestParsePrelude
      preludeFile <- Strict.readFile "Prelude.sil"
      let Right resParsec' = Parsec.parsePrelude preludeFile
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test parse assignment with Complete Lambda with ITE with Pair" $ do
      res <- runSILParser parseAssignment testParseAssignmentwCLwITEwPair1
      let Right resParsec' =
            Parsec.runParsecParser Parsec.parseAssignment testParseAssignmentwCLwITEwPair1
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test parseTopLevel with Complete Lambda with ITE with Pair" $ do
      res <- runSILParser parseTopLevel testParseTopLevelwCLwITEwPair
      let Right resParsec' =
            Parsec.runParsecParser Parsec.parseTopLevel testParseTopLevelwCLwITEwPair
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test parseMain with CL with ITE with Pair" $ do
      res <- runTestMainwCLwITEwPair
      preludeFile <- Strict.readFile "Prelude.sil"
      let Right resParsec' = Parsec.parseMain Map.empty testMainwCLwITEwPair
          resParsec = show resParsec'
      res `compare` resParsec @?= EQ
  , testCase "test Megaparsec vs Parsec implementation with tictactoe.sil" $ do
      preludeFile <- Strict.readFile "Prelude.sil"
      tictactoe <- Strict.readFile "tictactoe.sil"
      let megaPrelude = case parsePrelude preludeFile of
                          Right p -> p
                          Left pe -> error . getErrorString $ pe
          parsecPrelude = case Parsec.parsePrelude preludeFile of
                            Right p -> p
                            Left pe -> error . show $ pe
          megaparsecRes = case parseMain megaPrelude $ tictactoe of
                            Right x -> show x
                            Left err -> getErrorString err
          parsecRes = case Parsec.parseMain parsecPrelude $ tictactoe of
                        Right x -> show x
                        Left err -> show err
      megaparsecRes `compare` parsecRes @?= EQ
  ]

runTestPair :: String -> IO String
runTestPair = runSILParser parsePair

testPair0 = "{\"Hello World!\", \"0\"}"

testPair1 = unlines
  [ "{"
  , " \"Hello World!\""
  , ", \"0\""
  , "}"
  ]

runTestITE :: String -> IO String
runTestITE = runSILParser parseITE

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
  , "  then {\"Hello, world!\", 0}"
  , "  else"
  , "    {\"Goodbye, world!\", 1}"
  ]

testCompleteLambdawITEwPair = unlines $
  [ "#input ->"
  , "  if"
  , "    1"
  , "   then {\"Hello, world!\", 0}"
  , "   else"
  , "    {\"Goodbye, world!\", 1}"
  ]

testLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then {\"Hello, world!\", 0}"
  , "   else"
  , "    {\"Goodbye, world!\", 1}"
  ]

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ getErrorString pe
  return $ show prelude

testParseAssignmentwCLwITEwPair2 = unlines $
  [ "main = #input -> if 1"
  , "                  then"
  , "                   {\"Hello, world!\", 0}"
  , "                  else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair3 = unlines $
  [ "main = #input ->"
  , "  if 1"
  , "   then"
  , "     {\"Hello, world!\", 0}"
  , "   else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair4 = unlines $
  [ "main = #input"
  , "-> if 1"
  , "    then"
  , "       {\"Hello, world!\", 0}"
  , "      else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair5 = unlines $
  [ "main"
  , "  = #input"
  , "-> if 1"
  , "    then"
  , "       {\"Hello, world!\", 0}"
  , "      else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair6 = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "    then"
  , "       {\"Hello, world!\", 0}"
  , "      else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair7 = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "       then"
  , "             {\"Hello, world!\", 0}"
  , "           else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair1 = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "     then"
  , "       {\"Hello, world!\", 0}"
  , "     else {\"Goodbye, world!\", 0}"
  ]

testParseTopLevelwCLwITEwPair = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "     then"
  ,"        {\"Hello, world!\", 0}"
  ,"      else {\"Goodbye, world!\", 0}"
  ]

testMainwCLwITEwPair = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "     then"
  ,"        {\"Hello, world!\", 0}"
  ,"      else {\"Goodbye, world!\", 0}"
  ]

runTestMainwCLwITEwPair = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
    res = case parseMain prelude $ testMainwCLwITEwPair of
      Right x -> show x
      Left err -> getErrorString err
  return res

testWtictactoe = do
  preludeFile <- Strict.readFile "Prelude.sil"
  tictactoe <- Strict.readFile "tictactoe.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
    res = case parseMain prelude $ tictactoe of
      Right x -> show x
      Left err -> getErrorString err
  return res


-- unitTest2' parse s r = it s $ case parse s of
--   Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
--   Right g -> fmap (show . PrettyIExpr) (testEval g) >>= \r2 -> if r2 == r
--     then pure ()
--     else expectationFailure $ concat [s, " result ", r2]

-- unitTests parse = do
--   let unitTestType = unitTestType' parse
--       unitTest2 = unitTest2' parse
--   describe "type checker" $ do
--     undefined
--   describe undefined undefined

-- main = do
--   preludeFile <- Strict.readFile "Prelude.sil"
--   let prelude = case parsePrelude preludeFile of
--         Right p -> p
--         Left pe -> error $ show pe
--       parse = parseMain prelude
--   hspec $ do
--     unitTests parse
--     --nexprTests
