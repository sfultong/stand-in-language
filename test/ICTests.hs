{-# LANGUAGE PatternSynonyms #-}
module Main where

import Data.Bifunctor (bimap, first, second)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Telomare.Driver (CompiledProgram (..), SizingOption (..),
                        compileMainReporting, compileUnitTest, erasedChecks,
                        evalLoopCore, keepAccum, plainEval, programIteration,
                        programPlan)
import Telomare.EAL (CodeGuidance (..), EALLiftedResult (..),
                     deriveSizedGuidance, ealCaptureLayouts, inferEALCompiled,
                     inferEALFaithful, inferEALWithLifting)
import Telomare.Eval.IC (ICMeter (..), ICPlan (..), admitIC, evalIC)
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.IC
import Telomare.IR.Base (AbortKind (..), AbortOrigin (..), BasicExpr,
                         pattern AbortB, pattern EnvB, pattern GateB,
                         pattern GateSwitchEE, pattern LeftB, pattern PairB,
                         pattern RightB, pattern SetEnvB, pattern ZeroB, varB)
import Telomare.IR.Core (AbstractRunTime (..), CompiledExpr, RunTimeError (..),
                         Term3, compiled2Term3)
import Telomare.IR.Loc (LocTag (UnknownLoc))
import Telomare.Machine (appB, chainLinks, deferB, iteB, refinementCheckB)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferKeys (..), DeferMap (..), deferLift, keyDefers,
                         main2Term3)
import Telomare.Size (SizingReport (..))
import Test.Tasty
import Test.Tasty.HUnit
import TestModules (auxImports, libraryModules)

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

-- | Two distinguishable abort origins.
userO, caseO :: AbortOrigin
userO = AbortOrigin UserAbort UnknownLoc
caseO = AbortOrigin CaseAbort UnknownLoc

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
  library <- libraryModules
  let
    expandNamed name content =
      case runParseModule name content
             >>= first renderExpansionError . expandModule of
        Right m -> m
        Left e  -> error e
    prelude = [(name, expandNamed name src) | (name, src) <- library]
    parseAuxModule str =
      ("AuxModule", expandNamed "AuxModule" (auxImports <> str))
    parse :: String -> Either String Term3
    parse str =
      first show $ main2Term3 (parseAuxModule str : prelude) "AuxModule"
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
    -- what `telomare --ic` does: compile through the driver (whose gate
    -- certifies the program before sizing), read IC admission off the
    -- compiled program (a second certification, after sizing), run the
    -- net; both certifications must pass, and the net must print what the
    -- reference evaluator prints
    driverAdmits :: String -> TestTree
    driverAdmits src = testCase src $
      case compileMainReporting MainSizing (parseAuxModule src : prelude)
             "AuxModule" of
        Left e   -> assertFailure $ "compilation failed: " <> show e
        Right cp -> case programPlan cp of
          Left refusal -> assertFailure $ "refused: " <> refusal
          Right plan   -> do
            (_, viaIC) <- evalLoopCore (evalIC plan) (programIteration cp)
                            keepAccum "" []
            (_, viaRef) <- evalLoopCore plainEval (programIteration cp)
                             keepAccum "" []
            viaIC @?= viaRef
    -- the driver's post-sizing guidance is derived from the unsized
    -- program's size-independent certificate, and it is the guidance
    -- inferring the sized program again gives: the same bodies, the same
    -- capture layouts
    derivedAgrees :: String -> TestTree
    derivedAgrees src = testCase src $
      case (parse src, compileMainReporting MainSizing (parseAuxModule src : prelude)
                         "AuxModule") of
        (Left e, _) -> assertFailure $ "parse failed: " <> e
        (_, Left e) -> assertFailure $ "compilation failed: " <> show e
        (Right t3, Right cp) -> do
          let links = chainLinks (sizingReportCounts (cpSizing cp))
              full = inferEALCompiled (cpExpr cp)
          derived <- either (assertFailure . ("not derived: " <>)) pure $
            deriveSizedGuidance links (erasedChecks (cpExpr cp)) t3
              (inferEALFaithful t3) (cpExpr cp)
          either (assertFailure . show) (const (pure ())) (ealLiftedMain full)
          Map.keysSet (ealGuidance derived) @?= Map.keysSet (ealGuidance full)
          ealCaptureLayouts derived @?= ealCaptureLayouts full
          -- the program's guidance is main's and its input prologue's
          Map.keysSet (cpGuidance cp) @?= Map.keysSet (ealGuidance full)
            <> foldMap (Map.keysSet . ealGuidance . inferEALCompiled) (cpPrologue cp)
  defaultMain $ testGroup "IC runtime"
    [ testGroup "template namespace"
        [ testCase "deferHash agrees with the DeferMap key" $ do
            let dv = d 2 (p (LeftB EnvB) z)
                (DeferMap dm, _) = deferLift (compiled2Term3 dv)
            case (deferHash dv, Map.keys dm) of
              (Right h, [h']) -> h @?= h'
              other -> assertFailure $ "expected one shared hash, got "
                <> show other
        , testCase "keyDefers names every nested body by its DeferMap key" $ do
            -- guidance is looked up by these keys, so the one-pass keying
            -- must agree with deferLift at every depth, not just the top
            let dv = d 2 (p (d 3 (se (p (d 4 (LeftB EnvB)) EnvB)))
                            (d 5 (p EnvB z)))
                (DeferMap dm, _) = deferLift (compiled2Term3 dv)
                keys = catMaybes . toList $ keyDefers dv
            Map.keysSet dm @?= Set.fromList (dkHash <$> keys)
            length keys @?= 4
        , testCase "equal bodies share one template (selectors included)" $ do
            -- both bodies equal doLeft's, so all three refs reuse the
            -- selector template and only the two reserved templates are
            -- ever compiled
            let term = p (se (p (d 2 (LeftB EnvB)) (p z z)))
                         (se (p (d 3 (LeftB EnvB)) (p z z)))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p z z)
            Map.lookup "template-compiled" stats @?= Just 2
            Map.lookup "template-reused" stats @?= Just 2
        , testCase "deduped defers read back with their own index" $ do
            -- the result contains both defer values; sharing a template
            -- must not collapse their indexes (defer equality is by index)
            let body = p EnvB z
                term = p (d 2 body) (d 3 body)
            icEval term @?= eval term
            icEval term @?= Right term
        , testCase "bodies equal only modulo nested indexes stay separate" $ do
            -- outer bodies hash alike (the hash names nested defers by
            -- content) but their exact keys differ, so each keeps its own
            -- template and readback stays exact
            let outer i j = d i (se (p (d j (LeftB EnvB)) EnvB))
                term = p (outer 2 10) (outer 3 11)
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right term
            icEval term @?= eval term
            -- 2 selectors + 2 distinct outers; the nested bodies reuse
            -- the doLeft selector template
            Map.lookup "template-compiled" stats @?= Just 4
            Map.lookup "template-reused" stats @?= Just 2
        ]
    , testGroup "env splitting"
        [ testCase "disjoint projections split with no duplication" $ do
            let term = se (p (d 2 (p (LeftB EnvB) (RightB EnvB)))
                          (p z (p z z)))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p z (p z z))
            Map.lookup "split-pair" stats @?= Just 1
            Map.lookup "dup-pair" stats @?= Nothing
            Map.lookup "left-pair" stats @?= Nothing
            Map.lookup "right-pair" stats @?= Nothing
            Map.lookup "era-pair" stats @?= Nothing
        , testCase "whole-and-part use duplicates exactly once" $ do
            -- the whole env is copied (the analyzer's contraction), then
            -- one copy is split for the component. The env is literal data, so
            -- it is a constant: copied as one leaf, opened by the split
            let term = se (p (d 2 (p EnvB (LeftB EnvB))) (p z z))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p (p z z) z)
            Map.lookup "dup-leaf" stats @?= Just 1
            Map.lookup "dup-pair" stats @?= Nothing
            Map.lookup "split-pair" stats @?= Just 1
        , expectTest "unused env component is erased, not projected"
            (se (p (d 2 (LeftB EnvB)) (p z (p z z)))) (Right z)
        , expectTest "deep disjoint paths route directly"
            (se (p (d 2 (p (LeftB (RightB EnvB))
                          (p (LeftB EnvB) (RightB (RightB EnvB)))))
                 (p z (p (p z z) z))))
            (Right (p (p z z) (p z z)))
        , diffTest "projections of a zero env"
            (se (p (d 2 (p (LeftB EnvB) (RightB EnvB))) z))
        , testCase "projections of a bare defer env are stuck" $
            -- (asserted on the net only: the reference evaluator is
            -- partial on a demanded projection of bare code)
            case icEval (se (p (d 2 (p (LeftB EnvB) (RightB EnvB)))
                             (d 9 z))) of
              Left (GenericRunTimeError msg _) -> assertBool
                ("stuck on shape, got: " <> msg)
                ("not a pair" `isInfixOf` msg)
              other -> assertFailure $
                "expected a stuck report, got " <> show other
        , diffTest "projections of an aborted env"
            (se (p (d 2 (p (LeftB EnvB) (RightB EnvB)))
                 (AbortB userO (p z z))))
        , testCase "wiring consumes exactly the guidance-published usage" $ do
            let body = p (LeftB EnvB) (p (RightB (RightB EnvB)) (LeftB EnvB))
                lr = inferEALWithLifting (compiled2Term3 (d 2 body))
            case Map.elems (ealGuidance lr) of
              [Right cg] -> cgUsage cg @?= envUsage body
              other -> assertFailure $
                "expected one certified body, got " <> show other
        ]
    , testGroup "closure dup plans"
        [ testCase "guided duplication copies the closure skeleton" $ do
            -- a data-captured closure applied twice: its dup meets the
            -- closure pair, and with a layout the whole skeleton (ref,
            -- capture pair, zeros) copies in one interaction
            let clo = p (d 5 (LeftB EnvB)) (p z z)
                body = p (app EnvB (p z z)) (app EnvB (p z z))
                term = se (p (d 1 body) clo)
                layouts = ealCaptureLayouts
                  (inferEALWithLifting (compiled2Term3 term))
                (r, stats) = icEvalDetailedWith layouts defaultFuel term
                (r0, stats0) = icEvalDetailed defaultFuel term
            assertBool "has layouts" (not (Map.null layouts))
            -- guided and generic runs agree, and match the reference
            r @?= r0
            r @?= Right (p (p z z) (p z z))
            icEval term @?= eval term
            -- the guided run replaced the fan cascade
            assertBool "plan fired"
              (Map.findWithDefault 0 "dup-closure" stats > 0)
            assertBool "skeleton copied"
              (Map.findWithDefault 0 "dup-plan-copy" stats > 0)
            Map.lookup "dup-pair" stats @?= Nothing
            Map.lookup "dup-leaf" stats @?= Nothing
            -- the generic run paid the cascade the plan avoided
            assertBool "generic cascade present"
              (Map.findWithDefault 0 "dup-pair" stats0 > 0)
        , testCase "guided run agrees on a real program" $
            case parse "main = take $5 [1,2,3]" of
              Left e -> assertFailure $ "parse failed: " <> e
              Right t3 -> case compileUnitTest t3 of
                Left e -> assertFailure $ "compile failed: " <> show e
                Right c -> do
                  let t = se (p (d 0 c) z)
                      layouts = ealCaptureLayouts (inferEALCompiled c)
                      (r, stats) = icEvalDetailedWith layouts defaultFuel t
                      (r0, _) = icEvalDetailed defaultFuel t
                  assertBool "has layouts" (not (Map.null layouts))
                  r @?= r0
                  assertBool "plan fired on real closures"
                    (Map.findWithDefault 0 "dup-closure" stats > 0)
        ]
    , testGroup "closure erasure plans"
        [ testCase "guided erasure drops the closure skeleton" $ do
            -- a data-captured closure in a discarded env component: the
            -- splitter's eraser meets the closure pair, and with a layout
            -- the whole skeleton (ref, capture pair, zeros) drops in one
            -- interaction. Construction alone publishes the layout — the
            -- closure is never applied.
            let clo = p (d 5 (LeftB EnvB)) (p z z)
                term = se (p (d 1 (RightB EnvB)) (p clo z))
                layouts = ealCaptureLayouts
                  (inferEALWithLifting (compiled2Term3 term))
                (r, stats) = icEvalDetailedWith layouts defaultFuel term
                (r0, stats0) = icEvalDetailed defaultFuel term
            assertBool "has layouts" (not (Map.null layouts))
            -- guided and generic runs agree, and match the reference
            r @?= r0
            r @?= Right z
            icEval term @?= eval term
            -- the guided run replaced the eraser cascade
            assertBool "plan fired"
              (Map.findWithDefault 0 "era-closure" stats > 0)
            assertBool "skeleton dropped"
              (Map.findWithDefault 0 "era-plan-drop" stats > 0)
            Map.lookup "era-pair" stats @?= Nothing
            Map.lookup "era-leaf" stats @?= Nothing
            -- the generic run paid the cascade the plan avoided
            assertBool "generic cascade present"
              (Map.findWithDefault 0 "era-pair" stats0 > 0)
        , testCase "a shape the value outgrew falls back to the frontier" $ do
            -- the same hash constructed with two different captures merges
            -- to a weaker shape; erasure must still be correct, dropping
            -- what the merged shape vouches for and fanning out the rest
            let cloA = p (d 5 (LeftB EnvB)) (p z z)
                cloB = p (d 5 (LeftB EnvB)) (p (d 6 z) z)
                term = p (se (p (d 1 (RightB EnvB)) (p cloA z)))
                         (se (p (d 2 (RightB EnvB)) (p cloB z)))
                layouts = ealCaptureLayouts
                  (inferEALWithLifting (compiled2Term3 term))
                (r, _) = icEvalDetailedWith layouts defaultFuel term
            r @?= icEvalIC term
            r @?= Right (p z z)
        ]
    , testGroup "driver admission"
        [ testCase "a certified program is admitted and runs guided" $
            case parse "main = take $5 [1,2,3]"
                   >>= first show . compileUnitTest of
              Left e -> assertFailure $ "compile failed: " <> e
              Right c -> case admitIC c of
                Left refusal -> assertFailure $ "refused: " <> refusal
                Right plan -> do
                  -- the driver's shape: admit the program once, then
                  -- evaluate its applications under the granted plan
                  let t = se (p (d 0 c) z)
                      (m, r) = evalIC plan t
                  assertBool "layouts granted"
                    (not (Map.null (icPlanLayouts plan)))
                  r @?= eval t
                  assertBool "interactions measured"
                    (icMeterInteractions m > 0)
        , testCase "an uncertified program is refused with the verdict" $
            case admitIC omegaApplied of
              Left refusal -> assertBool ("refusal names it: " <> refusal)
                ("does not certify" `isInfixOf` refusal)
              Right _ -> assertFailure "omega must not be admitted"
        ]
    , testGroup "application"
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
    , testGroup "constants"
        [ testCase "literal data in an untaken branch is never built" $ do
            -- the branch pair is itself closed data: one constant, opened once
            -- by the selection, its untaken side dropped as a single leaf
            let term = GateSwitchEE z (num 40) z
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right z
            Map.lookup "const-open" stats @?= Just 1
            Map.lookup "era-pair" stats @?= Nothing
        , testCase "a constant opens one layer per use" $ do
            let term = RightB (num 40)
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (num 39)
            Map.lookup "const-open" stats @?= Just 1
        , testCase "a copied constant is copied whole" $ do
            let term = se (p (d 2 (p EnvB EnvB)) (num 40))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p (num 40) (num 40))
            Map.lookup "dup-leaf" stats @?= Just 1
            Map.lookup "dup-pair" stats @?= Nothing
        , expectTest "a constant reads back as its data"
            (p (num 3) (d 5 (num 2))) (Right (p (num 3) (d 5 (num 2))))
        ]
    , testGroup "abort"
        [ expectTest "an abort aborts with its message"
            (AbortB userO (p z z)) (Left (AbortRunTime userO msgPair))
        , expectTest "a Zero message still aborts"
            (AbortB userO z) (Left (AbortRunTime userO ZeroB))
        , expectTest "aborted values poison projections"
            (LeftB (AbortB userO (p z z))) (Left (AbortRunTime userO msgPair))
        , expectTest "a discarded aborted value is no abort"
            (GateSwitchEE z (LeftB (AbortB userO (p z z))) z) (Right z)
        , expectTest "an abort in the message is the one that counts"
            (AbortB userO (AbortB caseO (p z z))) (Left (AbortRunTime caseO msgPair))
        , expectTest "an abort under a defer has not fired"
            (d 7 (AbortB userO (p z z))) (Right (d 7 (AbortB userO (p z z))))
        , expectTest "a passing refinement check yields its value"
            (refinementCheckB userO (p (d 32 (LeftB EnvB)) z) (p z z)) (Right (p z z))
        , expectTest "a failing refinement check aborts with the value under a pair"
            (refinementCheckB userO (p (d 31 z) z) (p z z))
            (Left (AbortRunTime userO (PairB msgPair msgPair)))
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
        , corpus "main = succByte 0"
        , corpus "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succByte) 0"
        , corpus "main = plus $3 $2 succByte 0"
        , corpus "main = times $3 $2 succByte 0"
        , corpus "main = dEqual 2 1"
        , corpus "main = dEqual 2 2"
        , corpus "main = listLength [1,2,3]"
        , corpus "main = listPlus [1,2] [3,4]"
        , corpus "main = listEqual \"ab\" \"ab\""
        , corpus "main = map left [1,2]"
        , corpus "main = foldr (\\a b -> plus (d2c a) (d2c b) succByte 0) 1 [2,4,6]"
        , corpus "main = take $5 [1,2,3]"
        , corpus "main = c2Byte (minus $4 $3)"
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
        , testCase "strict ite: a diverging dead branch collapses, not runs" $ do
            -- iteB_-style raw branches enter the net as in-flight
            -- computations, but instantiation is demand-checked: once the
            -- selector's eraser reaches the dead branch, its parked
            -- applications collapse instead of unrolling omega to fuel
            -- death, and the net agrees with the lazy reference
            let strict = se (p (d 201 (se (p (se (p GateB (p z z)))
                                            (p omegaApplied (LeftB EnvB)))))
                             (p z z))
                (r, stats) = icEvalDetailed 50000 strict
            eval strict @?= Right z
            r @?= Right z
            assertBool "dead applications collapsed"
              (Map.findWithDefault 0 "apply-erased" stats > 0)
        , expectTest "strict ite with a stuck dead branch still agrees"
            -- bounded dead code is fine under speculation: the stuck value
            -- is erased with the unselected branch
            (se (p (d 202 (se (p (se (p GateB (p z z)))
                                (p (se (p (p z z) z)) (LeftB EnvB)))))
                  (p z z)))
            (Right z)
        ]
    , testGroup "programs with shared definitions certify and run under --ic"
        -- a definition used both directly and inside a closure that gets
        -- copied (by the program, or by sizing's unrolling of a recursion)
        -- needs two box depths if it is shared as one value; copied into
        -- each use, it certifies. All three run under --ic at 88acbdb4;
        -- with definitions only shared, the first is refused at compile
        -- time and the others at admission ("a duplicated value cannot
        -- be boxed")
        [ driverAdmits ("main = \\input -> (let t = \\f x -> f (f x)\n"
                     <> "                    in t (\\b -> t id 0) 0, 0)")
        , driverAdmits "main = \\input -> (concat [\"a\", \"b\"], 0)"
        , driverAdmits ("main = \\input -> (concat [succByte (left input), \" is \"]"
                     <> ", 0)")
          -- a recursive function inside its own step argument, directly
          -- and through a wrapper with no recursion of its own
        , driverAdmits "main = \\input -> (d2c 1 (\\x -> d2c 1 succByte x) 0, 0)"
        , driverAdmits ("main = \\input -> (foldr (\\a b -> foldr (\\x l -> (x,l)) b a)"
                     <> " 0 [[1],[2]], 0)")
        , driverAdmits "main = \\input -> (concat [concat [\"a\", \"b\"], \"c\"], 0)"
          -- a step that passes its argument through (every link of the
          -- sized chain applies the one step, and test, to the previous
          -- link's result)
        , driverAdmits "main = \\input -> (map (\\a -> 0) [d2c 1 id [1]], 0)"
          -- the same shapes under main's input lambda, sized against
          -- input a refinement bounds
        , driverAdmits ("validPlayer = \\x -> not (toBool ($3 left x))\n"
                     <> "main = \\input -> let p : validPlayer = left input\n"
                     <> "                 in (concat [concat [\"a\", \"b\"], (d2c p succByte 0, 0)], 0)")
        ]
    , testGroup "post-sizing guidance derived from the unsized certificate"
        [ derivedAgrees "main = \\input -> (d2c 2 (\\x -> (x,0)) 0, 0)"
        , derivedAgrees "main = \\input -> (map (\\x -> (x,0)) [1,2], 0)"
        , derivedAgrees "main = \\input -> (d2c 1 (\\x -> d2c 1 succByte x) 0, 0)"
        , derivedAgrees "main = \\input -> (concat [concat [\"a\", \"b\"], \"c\"], 0)"
          -- a pass-through step: no level is shared by every chain length
          -- at the post-sizing levels, but a uniform one exists a level up
        , derivedAgrees "main = \\input -> (map (\\a -> 0) [d2c 1 id [1]], 0)"
        , derivedAgrees ("validPlayer = \\x -> not (toBool ($3 left x))\n"
                      <> "main = \\input -> let p : validPlayer = left input\n"
                      <> "                 in (concat [concat [\"a\", \"b\"], (d2c p succByte 0, 0)], 0)")
        , testCase "a sized program that is not the certified one is not derived" $
            case ( parse "main = \\input -> (d2c 2 succByte 0, 0)"
                 , compileMainReporting MainSizing
                     (parseAuxModule "main = \\input -> (d2c 3 succByte 0, 0)" : prelude)
                     "AuxModule" ) of
              (Right t3, Right other) ->
                case deriveSizedGuidance (chainLinks (sizingReportCounts (cpSizing other))) (const False)
                       t3 (inferEALFaithful t3) (cpExpr other) of
                  Left _  -> pure ()
                  Right _ -> assertFailure "derived guidance for another program"
              _failed -> assertFailure "setup failed"
        ]
    , testGroup "EAL boundary experiments"
        [ testCase "EAL-certified numeral composition: runtime agrees" $
            -- numeral-of-numeral composition ($3 applied to $2) in the
            -- let-form resolution: the body binding `succ` used to make
            -- the greedy constraint solver give up on a zero-weight
            -- equation cycle; the exact solver (2026-10-13) certifies it,
            -- with boxes passing through the applications of the boxed
            -- numeral results
            case parse "main = $3 $2 succByte 0" of
              Left e -> assertFailure $ "parse failed: " <> e
              Right t3 -> do
                case ealLiftedMain (inferEALWithLifting t3) of
                  Right _ -> pure ()
                  Left e -> assertFailure $
                    "expected EAL acceptance, got " <> show e
                case compiled "main = $3 $2 succByte 0" of
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
