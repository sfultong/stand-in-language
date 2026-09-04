{-# LANGUAGE PatternSynonyms #-}
module Main where

import Data.Bifunctor (first)
import qualified Data.Map as Map
import qualified System.IO.Strict as Strict
import Telomare.Driver (compileUnitTest)
import Telomare.EAL (EALLiftedResult (..), inferEALWithLifting)
import Telomare.Eval.Reference ()
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.IC
import Telomare.IR.Base (BasicExpr, pattern AbortB, pattern EnvB,
                         pattern GateB, pattern GateSwitchEE, pattern LeftB,
                         pattern PairB, pattern RightB, pattern SetEnvB,
                         pattern ZeroB, varB)
import Telomare.IR.Core (AbstractRunTime (..), CompiledExpr,
                         RunTimeError (..), Term3)
import Telomare.Machine (abortInd, appB, deferB, iteB)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (main2Term3)
import Test.Tasty
import Test.Tasty.HUnit

-- * Term construction helpers

z :: CompiledExpr
z = ZeroB

p :: CompiledExpr -> CompiledExpr -> CompiledExpr
p = PairB

se :: CompiledExpr -> CompiledExpr
se = SetEnvB

d :: Int -> CompiledExpr -> CompiledExpr
d = deferB

-- | Apply a closure pair (code, env) to an argument, through twiddle,
-- exactly as compiled applications do.
app :: CompiledExpr -> CompiledExpr -> CompiledExpr
app = appB

-- | @\\f x -> f (f x)@ as a closed closure: the church numeral two.
churchTwo :: CompiledExpr
churchTwo = p (d 20 (p (d 21 body) EnvB)) z where
  body = app (varB 1) (app (varB 1) (varB 0))

-- | A successor-shaped closure: @\\x -> (Zero, x)@.
succC :: CompiledExpr
succC = p (d 22 (p z (varB 0))) z

-- | Telomare-style numerals: n = (Zero, (Zero, ... Zero)).
num :: Int -> CompiledExpr
num 0 = z
num n = p z (num (n - 1))

-- | The abort message @(Zero, Zero)@ at the message type.
msgPair :: BasicExpr
msgPair = PairB ZeroB ZeroB

-- | Unapplied self-application is a value; applied to itself its level
-- equations demand an unbounded tower — EAL rejects it, and this runtime
-- runs out of fuel on it.
omegaApplied :: CompiledExpr
omegaApplied = se (p omega (p omega z)) where
  omega = d 1 (se (p (LeftB EnvB) EnvB))

-- * Assertion helpers

-- | The IC runtime and the reference evaluator must both produce exactly
-- this outcome.
expectTest :: String -> CompiledExpr -> Either RunTimeError CompiledExpr
           -> TestTree
expectTest name t v = testCase name $ do
  icEval t @?= v
  eval t @?= v

-- | The IC runtime must agree with the reference evaluator, whatever the
-- outcome.
diffTest :: String -> CompiledExpr -> TestTree
diffTest name t = icDiff name t (const (pure ()))

-- | 'diffTest' plus an extra check on the term.
icDiff :: String -> CompiledExpr -> (CompiledExpr -> Assertion) -> TestTree
icDiff name t extra = testCase name $ do
  icEval t @?= eval t
  extra t

main :: IO ()
main = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    parseAndExpand (name, content) = (,) name <$>
      (runParseModule name content >>= first renderExpansionError . expandModule)
    parse :: String -> Either String Term3
    parse str = do
      ms <- traverse parseAndExpand
        [("Prelude", preludeFile), ("AuxModule", "import Prelude\n" <> str)]
      first show $ main2Term3 ms "AuxModule"
    -- compile a source program and evaluate it the way the unit-test
    -- corpus does: the compiled expression applied to a Zero env
    compiled :: String -> Either String CompiledExpr
    compiled src = do
      t3 <- parse src
      c <- first show (compileUnitTest t3)
      pure $ se (p (d 0 c) z)
    -- both evaluators must agree on the compiled program
    corpus :: String -> TestTree
    corpus src = testCase src $ case compiled src of
      Left e  -> assertFailure $ "compilation failed: " <> e
      Right t -> icEval t @?= eval t
  defaultMain $ testGroup "IC runtime"
    [ testGroup "application"
        [ expectTest "identity defer" (se (p (d 100 EnvB) z)) (Right z)
        , expectTest "constant body erases its env"
            (se (p (d 107 z) (p z z))) (Right z)
        , expectTest "application through twiddle"
            (app (p (d 106 (LeftB EnvB)) z) (p z z)) (Right (p z z))
        , expectTest "closure returning a closure"
            (se (p (d 108 (p (d 109 (LeftB EnvB)) EnvB)) z))
            (Right (p (d 109 (LeftB EnvB)) z))
        ]
    , testGroup "projection"
        [ expectTest "left of pair" (LeftB (p (p z z) z)) (Right (p z z))
        , expectTest "right of pair" (RightB (p (p z z) z)) (Right z)
        , expectTest "left of zero" (LeftB z) (Right z)
        , expectTest "projection of computed pair"
            (LeftB (se (p (d 112 EnvB) (p z (p z z))))) (Right z)
        ]
    , testGroup "duplication"
        [ expectTest "env used twice duplicates data"
            (se (p (d 101 (p EnvB EnvB)) (p z z)))
            (Right (p (p z z) (p z z)))
        , expectTest "env used twice duplicates a defer by reference"
            (se (p (d 102 (p EnvB EnvB)) (d 103 EnvB)))
            (Right (p (d 103 EnvB) (d 103 EnvB)))
        , expectTest "shared defer applied to two different arguments"
            (se (p (d 110 (p (se (p EnvB z)) (se (p EnvB (p z z)))))
                   (d 111 EnvB)))
            (Right (p z (p z z)))
        ]
    , testGroup "gates"
        [ expectTest "zero selects the left branch"
            (GateSwitchEE (p z z) z z) (Right (p z z))
        , expectTest "pair selects the right branch"
            (GateSwitchEE (p z z) z (p z z)) (Right z)
        , expectTest "discarded branch may be a closure"
            (GateSwitchEE (d 105 EnvB) z (p z z)) (Right z)
        , diffTest "scrutinee is computed"
            (GateSwitchEE z (p z z) (se (p (d 113 EnvB) (p z z))))
        ]
    , testGroup "abort"
        [ expectTest "abort of zero is the identity continuation"
            (se (p AbortB z)) (Right (d abortInd EnvB))
        , expectTest "the abort continuation passes its env through"
            (se (p (se (p AbortB z)) (p z z))) (Right (p z z))
        , expectTest "abort of a pair aborts with that message"
            (se (p AbortB (p z z))) (Left (AbortRunTime msgPair))
        , expectTest "aborted values poison projections"
            (LeftB (se (p AbortB (p z z)))) (Left (AbortRunTime msgPair))
        , expectTest "a discarded aborted value is no abort"
            (GateSwitchEE z (LeftB (se (p AbortB (p z z)))) z) (Right z)
        ]
    , testGroup "church numerals"
        [ expectTest "two applications of successor"
            (app (app churchTwo succC) z) (Right (num 2))
        , expectTest "iterated composition: two of (two of successor)"
            (app (app churchTwo (app churchTwo succC)) z) (Right (num 4))
        , diffTest "three levels of composition"
            (app (app churchTwo (app churchTwo (app churchTwo succC))) z)
        ]
    , testGroup "runtime machinery"
        [ testCase "interaction counts are reported" $ do
            let (r, stats) =
                  icEvalDetailed defaultFuel (app (app churchTwo succC) z)
            either (assertFailure . show) (const (pure ())) r
            assertBool "apply-ref fired"
              (maybe False (> 0) (Map.lookup "apply-ref" stats))
        , testCase "fuel exhaustion is reported" $
            case fst (icEvalDetailed 3 (app (app churchTwo succC) z)) of
              Left (ICFuelExhausted _) -> pure ()
              r -> assertFailure $ "expected fuel exhaustion, got " <> show r
        ]
    , testGroup "compiled program corpus (IC vs reference evaluator)"
        [ corpus "main = 0"
        , corpus "main = succ 0"
        , corpus "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"
        , corpus "main = plus $3 $2 succ 0"
        , corpus "main = times $3 $2 succ 0"
        , corpus "main = dEqual 2 1"
        , corpus "main = dEqual 2 2"
        , corpus "main = listLength [1,2,3]"
        , corpus "main = listPlus [1,2] [3,4]"
        , corpus "main = map left [1,2]"
        , corpus "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]"
        , corpus "main = take $5 [1,2,3]"
        , corpus "main = c2d (minus $4 $3)"
        , corpus ("main = let f = \\a b -> (a,b)\n"
               <> "           g = if 1 then f 1 else left\n"
               <> "       in g 1")
        , corpus ("main = let layer = \\recur x -> recur (x, 0)\n"
               <> "       in $3 layer (\\x -> x) 0")
        ]
    , testGroup "branch laziness (iteB vs iteB_)"
        [ expectTest "lazy ite never instantiates a diverging dead branch"
            -- iteB defers each branch, so the unselected else-branch (which
            -- would diverge) is an erased ref the net never fires
            (se (p (d 200 (iteB (p z z) (LeftB EnvB) omegaApplied))
                   (p z z)))
            (Right z)
        , testCase "strict ite speculates: a diverging dead branch is fuel death" $ do
            -- iteB_-style raw branches are fired eagerly by the net (the
            -- price of speculation); the lazy reference evaluator skips
            -- them, so this is a deliberate, documented divergence
            let strict = se (p (d 201 (se (p (se (p GateB (p z z)))
                                            (p omegaApplied (LeftB EnvB)))))
                             (p z z))
            eval strict @?= Right z
            case fst (icEvalDetailed 50000 strict) of
              Left (ICFuelExhausted _) -> pure ()
              r -> assertFailure $ "expected fuel exhaustion, got " <> show r
        , expectTest "strict ite with a stuck dead branch still agrees"
            -- bounded dead code is fine under speculation: the stuck value
            -- is erased with the unselected branch
            (se (p (d 202 (se (p (se (p GateB (p z z)))
                                (p (se (p (p z z) z)) (LeftB EnvB)))))
                  (p z z)))
            (Right z)
        ]
    , testGroup "EAL boundary experiments"
        [ testCase "EAL-rejected but terminating: runtime still agrees" $
            -- numeral-of-numeral composition ($3 applied to $2) needs
            -- level polymorphism the analyzer lacks (conservative
            -- rejection); the abstract algorithm still computes it
            -- correctly, so rejection here measures the certificate's
            -- precision, not soundness
            case parse "main = $3 $2 succ 0" of
              Left e -> assertFailure $ "parse failed: " <> e
              Right t3 -> do
                -- rejected either way; the error class depends on the
                -- resolver encoding (level cap vs. flow imprecision)
                case ealLiftedMain (inferEALWithLifting t3) of
                  Left _ -> pure ()
                  Right r -> assertFailure $
                    "expected EAL rejection, got " <> show r
                case compiled "main = $3 $2 succ 0" of
                  Left e  -> assertFailure $ "compilation failed: " <> e
                  Right t -> icEval t @?= eval t
        , testCase "EAL-rejected and diverging: runtime runs out of fuel" $
            -- omega omega: the reference evaluator would hang, EAL rejects
            -- at the level cap, and the net reduction never quiesces
            case fst (icEvalDetailed 100000 omegaApplied) of
              Left (ICFuelExhausted _) -> pure ()
              r -> assertFailure $ "expected divergence, got " <> show r
        ]
    ]
