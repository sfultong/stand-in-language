{-# LANGUAGE LambdaCase #-}

module CaseTests (unitTestsCase, qcPropsCase) where

import Common
import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Monad.State as State
import Data.Functor.Foldable (Base, Recursive (cata))
import Telomare (forget)
import Telomare.Parser
import Telomare.Resolver (pattern2UPT)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

caseTests :: IO ()
caseTests = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTestsCase, qcPropsCase]

---------------------
------ Property Tests
---------------------

caseExprStrWithPattern :: Pattern -> String
caseExprStrWithPattern p = unlines
  [ "main ="
  , "  let toCase = " <> (show . PrettyUPT . forget . pattern2UPT (0,0) $ p)
  , "      caseTest ="
  , "        case toCase of"
  , "          " <> (show . PrettyPattern $ p) <> " -> \"True\""
  , "          _ -> \"False\""
  , "  in \\input -> (caseTest, 0)"
  ]

caseExprStrWithPatternIgnore :: Pattern -> String
caseExprStrWithPatternIgnore p = unlines
  [ "main ="
  , "  let toCase = " <> (show . PrettyUPT . forget . pattern2UPT (0,0) $ p)
  , "      caseTest ="
  , "        case toCase of"
  , "          _ -> \"True\""
  , "          " <> (show . PrettyPattern $ p) <> " -> \"False\""
  , "  in \\input -> (caseTest, 0)"
  ]

runCaseExpWithPattern :: (Pattern -> String) -> Pattern -> IO String
runCaseExpWithPattern p2s p = runTelomareStr $ p2s p

qcPropsCase = testGroup "Property tests on case expressions (QuickCheck)" []
  -- [ QC.testProperty "All case patterns are reachable" $
  --     \x -> withMaxSuccess 16 . QC.idempotentIOProperty $ (do
  --       res <- runCaseExpWithPattern caseExprStrWithPattern x
  --       case res of
  --         "True\ndone\n" -> pure True
  --         _              -> pure False)
  -- , QC.testProperty "Ignore pattern accpets any pattern" $
  --     \x -> withMaxSuccess 16 . QC.idempotentIOProperty $ (do
  --       res <- runCaseExpWithPattern caseExprStrWithPatternIgnore x
  --       case res of
  --         "True\ndone\n" -> pure True
  --         _              -> pure False)
  -- ]

unitTestsCase :: TestTree
unitTestsCase = testGroup "Unit tests on case expressions" []
  -- [ testCase "test case with int leaves" $ do
  --     res <- runTelomareStr caseExprIntLeavesStr
  --     "True\ndone\n" `compare` res  @?= EQ
  -- , testCase "test case with string leaves" $ do
  --     res <- runTelomareStr caseExprStringLeavesStr
  --     "True\ndone\n" `compare` res  @?= EQ
  -- , testCase "test case with all leaves" $ do
  --     res <- runTelomareStr caseExprAllLeavesStr
  --     "Hi, sam!\ndone\n" `compare` res  @?= EQ
  -- ]

runTelomareStr :: String -> IO String
runTelomareStr str = runTelomare str $ \(_,_,_,_) -> pure ()

caseExprIntLeavesStr :: String
caseExprIntLeavesStr = unlines
  [ "main ="
  , "  let toCase = (0,(8,2))"
  , "      caseTest ="
  , "        case toCase of"
  , "          (0, (1,2)) -> \"False\""
  , "          (1, (8,2)) -> \"False\""
  , "          (0,(8,2)) -> \"True\""
  , "  in \\input -> (caseTest, 0)"
  ]

caseExprStringLeavesStr :: String
caseExprStringLeavesStr = unlines
  [ "main ="
  , "  let toCase = (\"a string\",(\"hi, sam\",\"str\"))"
  , "      caseTest ="
  , "        case toCase of"
  , "          (\"a string\", (\"hi, sam\",2)) -> \"False\""
  , "          (1, (8,2)) -> \"False\""
  , "          (\"a string\",(\"hi, sam\",\"str\")) -> \"True\""
  , "  in \\input -> (caseTest, 0)"
  ]

caseExprAllLeavesStr :: String
caseExprAllLeavesStr = unlines
  [ "main ="
  , "  let toCase = (\"a string\",(\"Hi, sam!\",\"str\"))"
  , "      caseTest ="
  , "        case toCase of"
  , "          (\"a string\", (\"Hi, sam!\",2)) -> \"False\""
  , "          (1, (8,2)) -> \"False\""
  , "          (\"a string\",(x,\"str\")) -> x"
  , "  in \\input -> (caseTest, 0)"
  ]

instance Arbitrary Pattern where
  arbitrary = sanitizePatternVars <$> sized genTree where
    sanitizePatternVars :: Pattern -> Pattern
    sanitizePatternVars p = State.evalState (go p) 0 where
      go :: Pattern -> State.State Int Pattern
      go = \case
        PatternVar _ -> do
          s <- State.get
          State.modify (+ 1)
          pure . PatternVar $ "var" <> show s
        PatternPair x y -> PatternPair <$> go x <*> go y
        x -> pure x
    leaves :: Gen Pattern
    leaves = oneof
      [ PatternString <$> elements (fmap (("s" <>) . show) [1..9])
      , PatternInt <$> elements [0..9]
      , pure $ PatternVar ""
      ]
    genTree :: Int -> Gen Pattern
    genTree = \case
      0 -> leaves
      x -> oneof
        [ leaves
        , PatternPair <$> genTree (div x 2) <*> genTree (div x 2)
        ]

  shrink = \case
    PatternString s -> case s of
      [] -> []
      _  -> pure . PatternString $ tail s
    PatternInt i -> case i of
      0 -> []
      x -> pure . PatternInt $ x - 1
    PatternPair a b -> a : b : [PatternPair na nb | (na, nb) <- shrink (a,b)]
