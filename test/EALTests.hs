module Main where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor
import Data.Either (rights)
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
    expandNamed name content =
      case runParseModule name content
             >>= first renderExpansionError . expandModule of
        Right m -> m
        Left e  -> error e
    prelude = [("Prelude", expandNamed "Prelude" preludeFile)]
    parseAuxModule str =
      ("AuxModule", expandNamed "AuxModule" ("import Prelude\n" <> str))
    parse :: Bool -> String -> Either String Term3
    parse appLet str = if appLet
      then first show $ main2Term3let (parseAuxModule str:prelude) "AuxModule"
      else first show $ main2Term3 (parseAuxModule str:prelude) "AuxModule"
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
    , testCase "self-application blows the dispatch depth cap" $
        -- omega applied to omega: each derivation of the body re-applies
        -- it, so dispatch nesting climbs without bound and the cap
        -- rejects it — the analogue of a flow analyzer's level blowout.
        -- Unapplied omega is a value and its body certifies standalone.
        let omega = defer 1 . setEnv $ p (lft env) env
            lr = inferEALWithLifting . setEnv $ p omega (p omega z)
            rs = Map.elems $ ealGuidance lr
        in do
          length [() | Right _ <- rs] @?= 1
          case ealLiftedMain lr of
            Left (EALSolverGaveUp _) -> pure ()
            other -> assertFailure $
              "expected dispatch depth rejection, got " <> show other
    , testCase "applying data certifies (it sticks, lazily)" $ do
        -- applying data sticks immediately at runtime, and stuckness is a
        -- value until demanded: bounded work, nothing for the certificate
        -- to reject (shape errors are the language checker's job, and
        -- sized recursion machinery leaves data in dead applied
        -- positions). A pair in function position is still rejected.
        r <- expectMain $ setEnv z
        ealMaxLevel r @?= 0
    , testCase "duplicated program input needs a box" $ do
        r <- expectMain $ p env env
        ealTopLevelBang r @?= 1
    , testCase "usage analysis reports contraction path" $
        case contractionSite . envUsageL . snd . deferLift $
          p (lft env) (lft env) of
          Just ([SL], _) -> pure ()
          other -> assertFailure $ "expected contraction at path L, got "
            <> show (fmap fst other)
    , testCase "guidance carries path usage, bangs, and speculation" $ do
        let lr = inferEALWithLifting . defer 1 $ p (lft env) (rgt env)
        case Map.elems (ealGuidance lr) of
          [Right cg] -> do
            cgUsage cg @?= Map.fromList [([SL], 1), ([SR], 1)]
            cgEnvBang cg @?= 0
            cgMaxLevel cg @?= 0
            cgSpeculatable cg @?= True
          other -> assertFailure $
            "expected one certified body, got " <> show other
    , testCase "guidance publishes capture layouts" $ do
        -- a closure with a data capture, applied directly: the global
        -- pass grounds each construction's package into a shape
        let clo = p (defer 5 (lft env)) (p z z)
            term = setEnv (p (defer 1 (setEnv (p (lft env) (rgt env)))) clo)
            lr = inferEALWithLifting term
            layoutOf i = [ cgCaptureLayout g
                         | Right g <- Map.elems (ealGuidance lr)
                         , cgIndex g == FunctionIndex i ]
        case ealLiftedMain lr of
          Right _ -> pure ()
          Left e -> assertFailure ("expected acceptance, got " <> show e)
        -- the inner closure carries data
        layoutOf 5 @?= [Just (CapPair CapData CapData)]
        -- the outer body is constructed against the closure itself:
        -- code-headed pair with a symbolic capture position
        layoutOf 1 @?= [Just (CapPair CapCode CapOther)]
        -- and the collected map is what a runtime consumer receives
        Map.size (ealCaptureLayouts lr) @?= 2
    , testCase "guidance withholds speculation from unsized bodies" $
        -- pre-sizing, the recursion oracle's work is unbounded: its body
        -- (and every body referencing it) must not be marked speculatable,
        -- while sizing-free bodies in the same program still are
        case parse False "main = d2c 1 succ 0" of
          Left e -> assertFailure ("parse failed: " <> e)
          Right g -> do
            let cgs = rights (Map.elems (ealGuidance (inferEALWithLifting g)))
            assertBool "has certified bodies" (not (null cgs))
            assertBool "some body carries the oracle"
              (not (all cgSpeculatable cgs))
            assertBool "some body is speculation-safe"
              (any cgSpeculatable cgs)
    , testCase "simple main test" $ unitTestEAL "main = succ 0"
    , testCase "lambda church application certifies" $
        -- BENCHMARK FLIPPED: the iterated function's application sites
        -- each dispatch their own fresh derivation, so the bang classes
        -- that used to collide are per-site, and pair conduits carry the
        -- boxes contraction demands
        unitTestEAL "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"
    , testCase "church literal composition certifies" $
        -- BENCHMARK FLIPPED, past the flow analyzer: $3 applied to $2
        -- iterates the iterator, which needs each composition rung at its
        -- own level — per-apply-site dispatch expresses that where both
        -- the old occurs check and a monomorphic flow analysis could not
        case parse False "main = $3 $2 succ 0" of
          Left e -> assertFailure ("parse failed: " <> e)
          Right g -> case ealLiftedMain (inferEALWithLifting g) of
            Right r -> assertBool "bounded level" (ealMaxLevel r <= 6)
            other -> assertFailure $
              "expected acceptance, got " <> show other
    , testCase "gate joining structurally different closures certifies" $
        -- BENCHMARK FLIPPED (the original 0CFA-switch motivation): `f 1`
        -- builds a pair containing its argument, `left` projects one out;
        -- code tags union at the join instead of unifying arrow
        -- structure, and the type cycle the join used to manufacture
        -- collapses to data
        unitTestEAL gateTest
    , testCase "closure-capturing closures join at a gate" $
        -- BENCHMARK FLIPPED: per-tag capture records let a
        -- function-bearing capture and a data capture ride through the
        -- same join, each resolved only at its own tag's dispatch
        unitTestEAL
          ("main = let compose = \\f g x -> f (g x)\n" <>
           "           h = compose succ succ\n" <>
           "           g = if 1 then h else left\n" <>
           "       in g 1")
    , testCase "real Prelude programs certify (listEqual)" $
        -- BENCHMARK FLIPPED: with captures per tag, the Prelude
        -- combinator plumbing types end to end
        case parse False "main = listEqual \"ab\" \"ab\"" of
          Left e -> assertFailure ("parse failed: " <> e)
          Right g -> case ealLiftedMain (inferEALWithLifting g) of
            Right r -> assertBool "bounded level" (ealMaxLevel r <= 3)
            other -> assertFailure $
              "expected acceptance, got " <> show other
    , testCase "filter over range certifies" $
        -- BENCHMARK FLIPPED: its failing body was a solver repair pump,
        -- broken by the occurrence slack
        case parse False
          "main = left (filter (\\x -> dEqual x 2) (range 0 3))" of
          Left e -> assertFailure ("parse failed: " <> e)
          Right g -> case ealLiftedMain (inferEALWithLifting g) of
            Right r -> assertBool "bounded level" (ealMaxLevel r <= 3)
            other -> assertFailure $
              "expected acceptance, got " <> show other
    , testCase "deferLift dedupes identical sibling bodies" $ do
        let dupBody = p (lft env) (lft env)
            apply i = setEnv (p (defer i dupBody) (lft env))
            (DeferMap dm, _) = deferLift . defer 1 $ p (apply 2) (apply 3)
        Map.size dm @?= 2
    , testCase "failing body is localized, dependents report it" $ do
        let bad = defer 2 $ setEnv (p (p z z) z) -- a pair applied as code
            good = defer 3 env
            lr = inferEALWithLifting . defer 1 $ p (p bad good) z
            rs = Map.elems $ ealGuidance lr
        length [() | Left (EALTypeMismatch _ _) <- rs] @?= 1
        length [() | Left (EALDependencyFailed _) <- rs] @?= 1
        length [() | Right _ <- rs] @?= 1
        case ealLiftedMain lr of
          Left (EALDependencyFailed _) -> pure ()
          other -> assertFailure $
            "expected dependency failure for main, got " <> show other
    , testCase "sizing preserves church application acceptance" $ do
        (pre, post) <- sizedVerdicts
          "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"
        case (pre, post) of
          (Right a, Right b) -> ealMaxLevel b @?= ealMaxLevel a
          other -> assertFailure $
            "expected acceptance on both sides of sizing, got " <> show other
    , testCase "sizing preserves church-literal acceptance" $ do
        (pre, post) <- sizedVerdicts "main = $3 $2 succ 0"
        case (pre, post) of
          (Right a, Right b) -> ealMaxLevel b @?= ealMaxLevel a
          other -> assertFailure $
            "expected acceptance on both sides of sizing, got " <> show other
    , testCase "d2c certifies before and after sizing" $ do
        -- BENCHMARK FLIPPED on both sides: per-tag captures type the
        -- oracle scaffolding pre-sizing and the strict level-flat chain
        -- post-sizing
        (pre, post) <- sizedVerdicts "main = d2c 3 succ 0"
        case (pre, post) of
          (Right _, Right b) -> assertBool "bounded level" (ealMaxLevel b <= 3)
          other -> assertFailure $
            "expected acceptance on both sides of sizing, got " <> show other
    , testCase "function-wrapped recursive call certifies" $ do
        (pre, post) <- sizedVerdicts
          "main = let g = {id, \\recur l -> succ (recur (right l)), \\l -> 0} in g [1]"
        case (pre, post) of
          (Right _, Right b) -> assertBool "bounded level" (ealMaxLevel b <= 3)
          other -> assertFailure $
            "expected acceptance on both sides of sizing, got " <> show other
    , testCase "curried recursion certifies" $ do
        -- BENCHMARK FLIPPED (the frontier both analyzers shared since the
        -- 0CFA era): its blocker was the abort base's dead data-in-applied
        -- position; with that tolerated and the caps sized for real
        -- chains, the levels fit
        (_, post) <- sizedVerdicts
          "main = let g = {id, \\recur l -> \\accum -> recur (right l) accum, \\l -> \\accum -> accum} in g [1] 0"
        case post of
          Right r -> assertBool "bounded level" (ealMaxLevel r <= 6)
          other -> assertFailure $
            "expected acceptance, got " <> show other
    , testCase "sized foldr certifies" $
        -- BENCHMARK FLIPPED — the last certification failure in the
        -- corpus. The greedy assigner was pumping the occurrence-equation
        -- family (shared frame bang as rhs, shared prefix edges on the
        -- lhs); the private slack per occurrence makes repair local and
        -- the whole foldr family certifies at level 1.
        case parse False "main = foldr (\\x l -> (x,l)) 0 [1,2]" of
          Left e -> assertFailure $ "parse failed: " <> e
          Right t3 -> case compileUnitTest t3 of
            Left e -> assertFailure $ "compile failed: " <> show e
            Right c -> do
              let lr = inferEALCompiled c
                  rs = Map.elems (ealGuidance lr)
              assertBool "has bodies" (not (null rs))
              length [() | Left _ <- rs] @?= 0
              case ealLiftedMain lr of
                Right r -> assertBool "bounded level" (ealMaxLevel r <= 3)
                other -> assertFailure $
                  "expected acceptance, got " <> show other
    ]
