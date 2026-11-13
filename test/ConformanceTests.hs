-- |The compiler has three ways to run a program: the sized interpreter, the
-- step-counting meter, and the unsized fast runtime. Each extra runtime is
-- only worth having if it is still the same interpreter — it is easy to get
-- a plausible cost or transcript out of an evaluator that quietly computes
-- the wrong answer. So this asserts, over every fixture program that sizes,
-- that all three agree.
module ConformanceTests where

import SizingTests (loadWith)
import Test.Hspec

import Telomare.Driver (CompiledProgram (..), compileModules, runMainWithInput)
import Telomare.Eval.Meter (Meter (..), evalMeter)
import Telomare.Fast (compileFast, runFastWithInput)
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.Machine (appB)

-- |Every fixture that compiles under sizing, with the input its main expects.
corpus :: [(FilePath, String, [String])]
corpus =
  [ ("test/programs/simpleplus.tel", "simpleplus", ["3 4"])
  , ("tc_ultra_minimal.tel", "tc_ultra_minimal", [])
  , ("test/programs/state-invariant-halt.tel", "state-invariant-halt", ["", "x"])
  ]

conformanceSpec :: Spec
conformanceSpec = describe "the three evaluators agree" $ mapM_ agreeOn corpus

agreeOn :: (FilePath, String, [String]) -> Spec
agreeOn (path, name, input) = describe name $ do
  it "the fast transcript matches the sized transcript" $ do
    modules <- loadWith path name
    expected <- runMainWithInput input modules name
    case compileFast modules name of
      Left err -> expectationFailure $ "failed to compile without sizing:\n" <> err
      Right prog -> case snd (runFastWithInput Nothing input prog) of
        Left e       -> expectationFailure $ "fast run failed: " <> show e
        Right actual -> actual `shouldBe` expected

  it "the meter computes the sized evaluator's value" $ do
    modules <- loadWith path name
    case compileModules modules name of
      Left err -> expectationFailure $ "failed to compile:\n" <> err
      Right cp -> do
        let applied = appB (cpExpr cp) ZeroB
            (measured, metered) = evalMeter applied
        fmap show metered `shouldBe` fmap show (eval applied)
        meterSteps measured `shouldSatisfy` (> 0)
        -- A run of any length constructs at least one node.
        meterBuilt measured `shouldSatisfy` (> 0)
