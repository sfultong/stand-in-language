{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

module SizingTests where

import Data.Foldable (fold)
import Data.Functor.Foldable (cata)
import Data.List (isInfixOf)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import qualified System.IO.Strict as Strict
import Test.Hspec

import Telomare.Driver (CompiledProgram (..), SizingOption (DebugSizing),
                        compileModulesWith)
import Telomare.IR.Base (AbortKind (..), AbortOrigin (..), AbortableF (..),
                         pattern AbortFW)
import Telomare.IR.Loc
import Telomare.Size (SizingReport (..), SizingSettings (SizingSettings),
                      renderSizingCertificate)
import Telomare.Size.IR (SizedRecursion (..))
import TestModules (libraryModules)

limitsDir :: FilePath
limitsDir = "test/programs/limits/"

-- |A program plus the library modules it may import, as the CLI would load
-- them.
loadWith :: FilePath -> String -> IO [(String, String)]
loadWith path moduleName = do
  library <- libraryModules
  source <- Strict.readFile path
  pure $ library <> [(moduleName, source)]

-- |Compile a program alongside the prelude, at a chosen sizing budget.
compileProgram :: SizingOption -> FilePath -> String -> IO (Either String SizingReport)
compileProgram sizingOption path moduleName = do
  modules <- loadWith path moduleName
  pure . fmap cpSizing $ compileModulesWith sizingOption modules moduleName

-- |Compile at the budget the CLI uses.
compileAtFullBudget :: FilePath -> String -> IO (Either String SizingReport)
compileAtFullBudget = compileProgram (DebugSizing (SizingSettings 65536 True))

sizingSpec :: Spec
sizingSpec = do
  describe "sizing failures name the recursion and say why" $ do
    -- The distinction these two tests draw is the whole point: one is fixable
    -- by a bigger budget and the other is not, and before this they were
    -- reported identically.
    it "reports unbounded input as unfixable by budget" $ do
      result <- compileAtFullBudget
        (limitsDir <> "unbounded-input-recursion.tel") "unbounded-input-recursion"
      case result of
        Right _ -> expectationFailure "expected this program to fail sizing"
        Left err -> do
          err `shouldSatisfy` isInfixOf "depends on input that nothing bounds"
          err `shouldSatisfy` isInfixOf "unbounded-input-recursion:"

    it "reports an exhausted budget as an exhausted budget" $ do
      result <- compileProgram (DebugSizing (SizingSettings 5 True))
        (limitsDir <> "over-budget-recursion.tel") "over-budget-recursion"
      case result of
        Right _ -> expectationFailure "expected this program to exhaust the budget"
        Left err -> do
          err `shouldSatisfy` isInfixOf "had still not stopped after 6 unrollings"
          err `shouldSatisfy` isInfixOf "over-budget-recursion:"

    it "sizes the same program once the budget is big enough" $ do
      result <- compileAtFullBudget
        (limitsDir <> "over-budget-recursion.tel") "over-budget-recursion"
      case result of
        Left err -> expectationFailure $ "expected this program to size:\n" <> err
        Right _  -> pure ()

  describe "sizing results are reported" $ do
    it "gives every recursion site a count and a source location" $ do
      result <- compileAtFullBudget "test/programs/simpleplus.tel" "simpleplus"
      case result of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right report -> do
          let counts = Map.toList . unSizedRecursion $ sizingReportCounts report
          counts `shouldSatisfy` not . null
          -- A site with no count would mean the compiler baked in a loop bound
          -- it could not justify.
          counts `shouldSatisfy` all (isJust . snd)
          -- Every site is locatable, which is what makes the report actionable.
          counts `shouldSatisfy` all
            (\(tok, _) -> case Map.lookup tok (sizingReportLocs report) of
               Just loc -> isJust (locStartLineColumn loc)
               Nothing  -> False)

    it "keeps simpleplus.tel's inferred counts stable" $ do
      result <- compileAtFullBudget "test/programs/simpleplus.tel" "simpleplus"
      case result of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right report ->
          -- The `d2c` calls simpleplus makes, `Num 255`'s walk over a byte
          -- (the 256), and the prelude's own recursions. If these move,
          -- sizing precision moved with them.
          (snd <$> Map.toAscList (unSizedRecursion (sizingReportCounts report)))
            `shouldBe` [Just 256, Just 7, Just 10, Just 10, Just 10, Just 11]

    it "sizes a recursion past a gate on a superposition whose sides go opposite ways" $ do
      -- y is 8 exactly where the gate on x picks the recursion, so 8
      -- iterations are needed; a gate that flattened x's superposition
      -- under the wrong input once sized it for y = 3
      result <- compileAtFullBudget "test/programs/mislabeled-size.tel" "mislabeled-size"
      case result of
        Left err -> expectationFailure $ "failed to compile mislabeled-size.tel:\n" <> err
        Right report ->
          (snd <$> Map.toAscList (unSizedRecursion (sizingReportCounts report)))
            `shouldSatisfy` all (maybe False (>= 9))

    it "names the budget it searched under" $ do
      result <- compileAtFullBudget "test/programs/simpleplus.tel" "simpleplus"
      case result of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right report -> do
          sizingReportBudget report `shouldBe` 65536
          renderSizingCertificate report `shouldSatisfy` isInfixOf "65536"

  describe "where refinement checks go" $ do
    it "runs simpleplus.tel's input check before main, and erases the Prelude's Bool checks" $ do
      -- the Prelude's Bool checks always pass where simpleplus calls them;
      -- its input check depends on the input alone, matters wherever it
      -- fails (its value is in the output), and the case on the input means
      -- it cannot fail on the input-less first call. succByte's Num check
      -- stays in main: validDigit bounds only a digit's left spine, so
      -- `succByte x` fails on an input character that is not a numeral
      kinds <- remainingChecks "test/programs/simpleplus.tel" "simpleplus"
      kinds `shouldBe` Right ([RefinementAbort], [RefinementAbort])

    it "erases a check that holds because two uses of one input agree" $ do
      -- deciding it means remembering, in the branch that runs the check,
      -- which way the input went for the value checked
      kinds <- remainingChecks "test/programs/correlated-check.tel" "correlated-check"
      kinds `shouldBe` Right ([], [])

    it "keeps a check that fails because two uses of one input agree" $ do
      -- the same shape, with the check reversed: it fails wherever it runs
      kinds <- remainingChecks "test/programs/anticorrelated-check.tel" "anticorrelated-check"
      kinds `shouldBe` Right ([RefinementAbort], [])

    it "runs a check on the input alone before main" $ do
      -- `not` refines its argument as a Bool, which fails only when the
      -- input's left is a pair, so never on the input-less first call
      kinds <- remainingChecks "test/programs/notinput.tel" "notinput"
      kinds `shouldBe` Right ([], [RefinementAbort])

    it "erases a check on the state that every state main makes passes" $ do
      kinds <- remainingChecks "test/programs/state-invariant.tel" "state-invariant"
      kinds `shouldBe` Right ([], [])

    it "keeps a check on the state that a state main makes fails" $ do
      kinds <- remainingChecks "test/programs/state-invariant-broken.tel" "state-invariant-broken"
      kinds `shouldBe` Right ([RefinementAbort], [])

    it "keeps a check that every state main makes passes, but the first call fails" $ do
      kinds <- remainingChecks "test/programs/state-invariant-first-call.tel" "state-invariant-first-call"
      kinds `shouldBe` Right ([RefinementAbort], [])

    it "erases a check on the state that every state the loop goes on with passes" $ do
      kinds <- remainingChecks "test/programs/state-invariant-halt.tel" "state-invariant-halt"
      kinds `shouldBe` Right ([], [])

  describe "a refinement bounds what its checked value flows into" $ do
    it "sizes a recursion by the check in its own case alternative" $ do
      result <- compileAtFullBudget "test/programs/branch-refinement.tel" "branch-refinement"
      case result of
        Left err -> expectationFailure $ "expected this program to size:\n" <> err
        Right _  -> pure ()

    it "does not bound one alternative's input by another's check" $ do
      -- the checks used to bound the whole input, as if every input passed
      -- every check main met
      result <- compileAtFullBudget "test/programs/branch-refinement-leak.tel" "branch-refinement-leak"
      case result of
        Right _ -> expectationFailure "expected this program to fail sizing"
        Left err -> err `shouldSatisfy` isInfixOf "depends on input that nothing bounds"

    it "does not bound by a check whose passing branch it cannot follow" $ do
      -- the unknown branch used to be read as impossible, bounding `left s`
      -- to Zero, and the program miscompiled
      result <- compileAtFullBudget "test/programs/unknown-check-branch.tel" "unknown-check-branch"
      case result of
        Right _ -> expectationFailure "expected this program to fail sizing"
        Left err -> err `shouldSatisfy` isInfixOf "depends on input that nothing bounds"

-- |The kinds of the refinement checks a compiled program's main still
-- makes, and those its input prologue makes.
remainingChecks :: FilePath -> String -> IO (Either String ([AbortKind], [AbortKind]))
remainingChecks path moduleName = do
  modules <- loadWith path moduleName
  pure $ (\cp -> (kindsIn (cpExpr cp), foldMap kindsIn (cpPrologue cp)))
    <$> compileModulesWith (DebugSizing (SizingSettings 65536 True)) modules moduleName
  where
    kindsIn = Set.toList . Set.map abortKind . cata (\case
      AbortFW (AbortF o s) -> Set.insert o s
      x                    -> fold x)
