{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor
import qualified Data.Map as Map
import qualified System.IO.Strict as Strict
import Telomare.Driver (compileUnitTest)
import Telomare.EAL
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.IR.Base (BasicExprF (..), FunctionIndex (FunctionIndex),
                         StuckF (..))
import Telomare.IR.Core (Term3, Term3F (..))
import Telomare.IR.Loc (LocTag (..))
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferMap (..), deferLift, main2Term3, main2Term3let)
import Test.Tasty
import Test.Tasty.HUnit

-- * Term construction helpers

l :: LocTag
l = UnknownLoc

z :: Term3
z = l :< Term3B ZeroSF

p :: Term3 -> Term3 -> Term3
p a b = l :< Term3B (PairSF a b)

env :: Term3
env = l :< Term3S EnvSF

defer :: Int -> Term3 -> Term3
defer i b = l :< Term3S (DeferSF (FunctionIndex i) b)

setEnv :: Term3 -> Term3
setEnv x = l :< Term3S (SetEnvSF x)

gateB :: Term3
gateB = l :< Term3S GateSF

-- | Full gate switch: apply gate to the scrutinee, then to the branch pair.
gateSwitch :: Term3 -> Term3 -> Term3 -> Term3
gateSwitch a b s = setEnv (p (setEnv (p gateB s)) (p a b))

lft :: Term3 -> Term3
lft x = l :< Term3S (LeftSF x)

rgt :: Term3 -> Term3
rgt x = l :< Term3S (RightSF x)

-- * Assertion helpers

deferBang :: EALResult -> Int -> Int
deferBang r i = Map.findWithDefault (-1) (FunctionIndex i) (ealDeferBangs r)

expectMain :: Term3 -> IO EALResult
expectMain term = case ealLiftedMain (inferEALWithLifting term) of
  Left e  -> assertFailure
    ("expected successful lifted inference, got " <> show e)
  Right r -> pure r

expectMainFail :: (EALError -> Bool) -> String -> Term3 -> IO ()
expectMainFail matches what term =
  case ealLiftedMain (inferEALWithLifting term) of
    Left e | matches e -> pure ()
    other -> assertFailure $ "expected " <> what <> ", got " <> show other

unitTestEAL' parse s = case parse s of
  Left e -> assertFailure $ concat ["failed to parse ", s, " ", show e]
  Right g -> case ealLiftedMain (inferEALWithLifting g) of
    Left e -> assertFailure
      ("expected successful lifted inference, got " <> show e)
    Right _r -> pure ()

gateTest =
  "main = let f = \\a b -> (a,b)\n" <>
  "           g = if 1 then f 1 else left\n" <>
  "       in g 1"
main :: IO ()
main = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    parseAndExpand (name, content) = (,) name <$>
      (runParseModule name content >>= first renderExpansionError . expandModule)
    parse :: Bool -> String -> Either String Term3
    parse appLet str = do
      ms <- traverse parseAndExpand
        [("Prelude", preludeFile), ("AuxModule", "import Prelude\n" <> str)]
      first show $ (if appLet then main2Term3let else main2Term3) ms "AuxModule"
    unitTestEAL = unitTestEAL' (parse False)
    -- the main verdicts on the same program before and after sizing
    sizedVerdicts s = case parse False s of
      Left e -> assertFailure $ "parse failed: " <> e
      Right t3 -> case compileUnitTest t3 of
        Left e -> assertFailure $ "compile failed: " <> show e
        Right c -> pure ( ealLiftedMain (inferEALWithLifting t3)
                        , ealLiftedMain (inferEALCompiled c) )
  defaultMain $ testGroup "EAL inference"
    [ testCase "identity Defer is linear, level 0" $ do
        r <- expectMain $ defer 1 env
        deferBang r 1 @?= 0
        ealMaxLevel r @?= 0
    , testCase "disjoint projections are linear destructuring" $ do
        r <- expectMain . defer 1 $ p (lft env) (rgt env)
        deferBang r 1 @?= 0
        ealMaxLevel r @?= 0
    , testCase "env shuffle combinator (three disjoint paths) is linear" $ do
        -- the pervasive compiled pattern: \x -> ((x.RL, (x.L, x.RR)))
        r <- expectMain . defer 1 $
          p (lft (rgt env)) (p (lft env) (rgt (rgt env)))
        deferBang r 1 @?= 0
        ealMaxLevel r @?= 0
    , testCase "duplicated env path needs one box" $ do
        r <- expectMain . defer 1 $ p (lft env) (lft env)
        deferBang r 1 @?= 1
        ealMaxLevel r @?= 1
    , testCase "overlapping whole-and-part use is contraction" $ do
        r <- expectMain . defer 1 $ p env (lft env)
        deferBang r 1 @?= 1
    , testCase "church-two style double application" $ do
        -- \e -> e.L (e.L e.R), applications in Telomare SetEnv form
        r <- expectMain . defer 1 . setEnv $
          p (lft env) (setEnv (p (lft env) (rgt env)))
        deferBang r 1 @?= 1
        ealMaxLevel r @?= 1
    , testCase "duplicated closure applied at both sites" $ do
        r <- expectMain . defer 1 $
          p (setEnv (p (lft env) z)) (setEnv (p (lft env) z))
        deferBang r 1 @?= 1
        ealMaxLevel r @?= 1
    , testCase "gate branches count multiplicatively" $ do
        r <- expectMain . defer 1 $ gateSwitch env env z
        deferBang r 1 @?= 1
    , testCase "sibling contractions dedupe, levels preserved" $ do
        let dupBody = p (lft env) (lft env)
            apply i = setEnv (p (defer i dupBody) (lft env))
        r <- expectMain . defer 1 $ p (apply 2) (apply 3)
        deferBang r 1 @?= 1
        -- defers 2 and 3 share one body; its first-seen index survives
        deferBang r 2 @?= 1
        ealMaxLevel r @?= 1
    , testCase "self-application blows the level cap" $
        -- omega applied to omega: the level equations demand an unbounded
        -- box tower, surfacing as a solver cap failure. (Unapplied omega is
        -- a value and correctly accepted.)
        let omega = defer 1 . setEnv $ p (lft env) env
            gaveUp = \case EALSolverGaveUp _ -> True; _ -> False
        in expectMainFail gaveUp "solver cap failure"
          . setEnv $ p omega (p omega z)
    , testCase "applying data is a type mismatch" $
        let mismatch = \case EALTypeMismatch _ _ -> True; _ -> False
        in expectMainFail mismatch "type mismatch" $ setEnv z
    , testCase "duplicated program input needs a box" $ do
        r <- expectMain $ p env env
        ealTopLevelBang r @?= 1
    , testCase "usage analysis reports contraction path" $
        case contractionSites . envUsageL . snd . deferLift $
          p (lft env) (lft env) of
          [([SL], _)] -> pure ()
          other -> assertFailure $ "expected contraction at path L, got "
            <> show (fmap fst other)
    , testCase "simple main test" $ unitTestEAL "main = succ 0"
    , testCase "lambda church application main" $
        unitTestEAL "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"
    , testCase "church literal main: numeral-of-numeral composition is rejected" $
        -- $3 applied to $2 iterates the iterator: each composition rung
        -- needs the inner numeral one level deeper, which the monomorphic
        -- per-site analysis cannot express (the let-polymorphism
        -- limitation in the module header) — the level equations demand an
        -- unbounded tower. Flat uses (plus $3 $2 succ 0) accept.
        case parse False "main = $3 $2 succ 0" of
          Left e -> assertFailure ("parse failed: " <> e)
          Right g -> case ealLiftedMain (inferEALWithLifting g) of
            Left (EALSolverGaveUp _) -> pure ()
            other -> assertFailure $
              "expected level-cap rejection, got " <> show other
    , testCase "gate inconstency" $ unitTestEAL gateTest
    , testCase "deferLift dedupes identical sibling bodies" $ do
        let dupBody = p (lft env) (lft env)
            apply i = setEnv (p (defer i dupBody) (lft env))
            (DeferMap dm, _) = deferLift . defer 1 $ p (apply 2) (apply 3)
        Map.size dm @?= 2
    , testCase "failing body is localized, dependents report it" $ do
        let bad = defer 2 $ setEnv z -- applying data
            good = defer 3 env
            lr = inferEALWithLifting . defer 1 $ p (p bad good) z
            rs = Map.elems $ ealBodyResults lr
        length [() | Left (EALTypeMismatch _ _) <- rs] @?= 1
        length [() | Left (EALDependencyFailed _) <- rs] @?= 1
        length [() | Right _ <- rs] @?= 1
        case ealLiftedMain lr of
          Left (EALDependencyFailed _) -> pure ()
          other -> assertFailure $
            "expected dependency failure for main, got " <> show other
    -- Gate-position experiment (2026-09): pre- and post-sizing verdicts
    -- agree on every probed program, because the sized output keeps the
    -- same repeat-frame and dead-branch structure the analyzer trips on.
    -- Moving the gate does not change what it admits; analyzer precision
    -- is the lever.
    , testCase "sizing preserves acceptance and max level" $ do
        (pre, post) <- sizedVerdicts
          "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"
        case (pre, post) of
          (Right a, Right b) -> ealMaxLevel b @?= ealMaxLevel a
          other -> assertFailure $
            "expected acceptance on both sides of sizing, got " <> show other
    , testCase "sizing preserves the church-literal level-cap rejection" $ do
        (pre, post) <- sizedVerdicts "main = $3 $2 succ 0"
        let gaveUp = \case Left (EALSolverGaveUp _) -> True; _ -> False
        assertBool "pre-sizing" (gaveUp pre)
        assertBool "post-sizing" (gaveUp post)
    , testCase "sized recursion machinery certifies (d2c)" $ do
        -- with must-fail shape checks and the strict level-flat chain, the
        -- {t,r,b} machinery itself is inside the EAL fragment
        (pre, post) <- sizedVerdicts "main = d2c 3 succ 0"
        case (pre, post) of
          (Right _, Right p) -> assertBool "bounded level" (ealMaxLevel p <= 3)
          other -> assertFailure $
            "expected acceptance on both sides of sizing, got " <> show other
    , testCase "trimmed captures certify a function-wrapped recursive call" $ do
        -- an inlined lambda (succ here) used to capture the entire env
        -- inside the recursion step, forcing a root contraction whose
        -- interaction with the step/approximant application cycle demanded
        -- an unbounded tower; with trimmed lambda captures the closure
        -- creation is disjoint path projections and the program certifies
        (_, post) <- sizedVerdicts
          "main = let g = {id, \\recur l -> succ (recur (right l)), \\l -> 0} in g [1]"
        case post of
          Right r -> assertBool "bounded level" (ealMaxLevel r <= 3)
          other -> assertFailure $ "expected acceptance, got " <> show other
    , testCase "curried recursion is the remaining level frontier" $ do
        -- the inner \accum lambda's trimmed capture still carries the
        -- approximant, and the resulting application cycle demands levels
        -- the monomorphic analysis cannot assign (or the greedy solver
        -- cannot find); foldr-family programs live behind this
        (_, post) <- sizedVerdicts
          "main = let g = {id, \\recur l -> \\accum -> recur (right l) accum, \\l -> \\accum -> accum} in g [1] 0"
        case post of
          Left (EALSolverGaveUp _) -> pure ()
          other -> assertFailure $
            "expected level-cap rejection, got " <> show other
    , testCase "a rejected sized program's bodies still all tag standalone" $
        case parse False "main = listLength [1,2,3]" of
          Left e -> assertFailure $ "parse failed: " <> e
          Right t3 -> case compileUnitTest t3 of
            Left e -> assertFailure $ "compile failed: " <> show e
            Right c -> do
              let rs = Map.elems . ealBodyResults $ inferEALCompiled c
              assertBool "has bodies" (not (null rs))
              length [() | Left _ <- rs] @?= 0
    ]
