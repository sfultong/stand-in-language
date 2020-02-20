module ParserTests where

import           SIL.ParserMegaparsec
import qualified System.IO.Strict as Strict

-- - 1
--   - a

-- - 1
--   - a
--   - b
--   - c

testPair = unlines
  [ "{"
  , " \"Hello World!\""
  , ", \"0\""
  , "}"
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

runTestITE = runSILParser parseITE testITE4

testITEwPair = unlines $
  [ "  if"
  , "    1"
  , "  then {\"Hello, world!\", 0}"
  , "  else"
  , "    {\"Goodbye, world!\", 1}"
  ]

runTestITEwPair = runSILParser (sc *> parseITE) testITEwPair

testCompleteLambdawITEwPair = unlines $
  [ "#input ->"
  , "  if"
  , "    1"
  , "  then {\"Hello, world!\", 0}"
  , "  else"
  , "    {\"Goodbye, world!\", 1}"
  ]

runTestCompleteLambdawITEwPair = runSILParser parseCompleteLambda testCompleteLambdawITEwPair

testLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "  then {\"Hello, world!\", 0}"
  , "  else"
  , "    {\"Goodbye, world!\", 1}"
  ]

runTestLambdawITEwPair = runSILParser parseCompleteLambda testCompleteLambdawITEwPair

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
  putStrLn "Prelude parse successful!"

testParseAssignmentwCLwITEwPair2 = unlines $
  [ "main = #input -> if 1"
  , "                 then"
  , "                   {\"Hello, world!\", 0}"
  , "                 else {\"Goodbye, world!\", 0}"
  ]
testParseAssignmentwCLwITEwPair3 = unlines $
  [ "main = #input ->"
  , "  if 1"
  , "  then"
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
-- fails
testParseAssignmentwCLwITEwPair = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "        then"
  , "                {\"Hello, world!\", 0}"
  , "              else {\"Goodbye, world!\", 0}"
  ]

runTestParseAssignmentwCLwITEwPair = runSILParser parseAssignment testParseAssignmentwCLwITEwPair

--fails
testParseTopLevelwCLwITEwPair = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "              then"
  ,"                 {\"Hello, world!\", 0}"
  ,"                else {\"Goodbye, world!\", 0}"
  ]

--fails
runTestParseTopLevelwCLwITEwPair = runSILParser parseTopLevel testParseTopLevelwCLwITEwPair

--fails
testMainwCLwITEwPair = unlines $
  [ "main"
  , "  = #input"
  , " -> if 1"
  , "              then"
  ,"                 {\"Hello, world!\", 0}"
  ,"                else {\"Goodbye, world!\", 0}"
  ]

--fails
runTestMainwCLwITEwPair = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    res = show $ parseMain prelude $ testMainwCLwITEwPair
  putStrLn res

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
