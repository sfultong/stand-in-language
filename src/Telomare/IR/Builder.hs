{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

-- |A small monadic DSL for constructing lowered terms while threading the
-- supply of function indexes and unsized-recursion tokens. Used by the
-- core lowering ('Telomare.Resolve.splitExpr') and by tests that
-- hand-assemble expected 'Term3' values.
module Telomare.IR.Builder where

import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Functor.Foldable (Base, Corecursive (embed), Recursive (project))
import Telomare.IR.Base (BasicBase (..), BasicExprF (..), CarryAnno (..),
                         FunctionIndex, StuckBase (..), StuckF (..),
                         UnsizedRecursionToken, pattern EnvB,
                         pattern FillFunctionEE, pattern GateB, pattern LeftB,
                         pattern PairB, pattern PairP, pattern RightB,
                         pattern SetEnvB, pattern StuckEE, pattern ZeroB,
                         varB)
import Telomare.IR.Core (Term3, Term3F (..))
import Telomare.IR.Loc (LocTag)

type Term3Builder g = State (FunctionIndex, UnsizedRecursionToken) g

buildTerm :: (Corecursive g) => Term3Builder g -> g
buildTerm = flip State.evalState (toEnum 0, toEnum 0)

deferS :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => g -> Term3Builder g
deferS x = do
  fi <- State.gets fst
  State.modify (\(_, urt) -> (succ fi, urt))
  pure . StuckEE $ DeferSF fi x

-- TODO: replace with PairP?
pairS :: (Base g ~ CofreeT.CofreeF f a, BasicBase f, Recursive g, Corecursive g, Monad m) => m g -> m g -> m g
pairS a b = do
  a' <- a
  b' <- b
  let l CofreeT.:< _ = project a'
  pure . embed $ l CofreeT.:< embedB (PairSF a' b')

clamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
clamS x = pairS (x >>= deferS) $ pure ZeroB

lamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
lamS x = pairS (x >>= deferS) $ pure EnvB

twiddleS :: forall g f w. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w)
  => Term3Builder g
twiddleS = deferS . PairP (LeftB $ RightB EnvB) . PairP (LeftB EnvB) $ RightB (RightB EnvB)

appS :: forall g f w. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w)
  => Term3Builder g -> Term3Builder g -> Term3Builder g
appS c i = SetEnvB . SetEnvB <$> pairS twiddleS (pairS i c)

-- | Builder-level lazy if-then-else: the 'Telomare.Machine.iteB' encoding,
-- but each branch closure gets a fresh defer index from the builder supply
-- instead of the reserved sizing-step indexes (which must keep one grammar
-- per index).
iteS :: (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g -> Term3Builder g -> Term3Builder g
iteS i t e = do
  i' <- i
  ec <- e >>= deferS
  tc <- t >>= deferS
  pure $ FillFunctionEE (FillFunctionEE (FillFunctionEE GateB i') (PairB ec tc)) EnvB

-- | The per-use-site sizing oracle: a closed closure whose body is the
-- sizing hole for one recursion token. The wrapper applies it to its
-- captured @(tWrap, (recur, (base, 0)))@ triple; the sizing pass expands
-- the hole into successive step unfoldings, and size substitution finally
-- replaces it with the n-fold approximant chain
-- ('Telomare.Machine.sizedRecursionChain'). One oracle per syntactic use
-- of a recursive binding, so each use site sizes independently.
unsizedRecursionOracle :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
unsizedRecursionOracle l tok = clamS . pure . embed $ l CofreeT.:< Term3Unsized tok

-- | A church numeral: @\\f x -> f (f ... (f x))@ as plain nested
-- applications of a shared f. Bounded iteration by duplication of the
-- iterated function is the encoding both EAL certification and a
-- sharing-based runtime want; the old form (a self-applying frame driven
-- by nested SetEnvs) was outside the EAL fragment and foreclosed sharing.
i2CB :: LocTag -> Int -> Term3Builder Term3
i2CB _l n = clamS . lamS $ iterate (appS (pure $ varB 1)) (pure $ varB 0) !! n

-- | @{t, r, b}@: a closure over the evaluated test/recur/base triple that,
-- once handed its per-site oracle, becomes the recursion function
-- @\\x -> approximants x@. The recursion itself is Y-approximant
-- composition: sizing replaces the oracle's hole with @step^n base@ where
-- @step recur i = if t i then r recur i else b i@, so no function ever
-- applies itself.
unsizedRecursionWrapper :: LocTag -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3
unsizedRecursionWrapper _loc t r b =
  let -- the test behind a syntactically definite closure, so the sizing
      -- pass can wrap its body ('RecursionTestF') whatever shape t's own
      -- value takes (it may be a superposition during abstract evaluation)
      tWrap = pairS ((>>= deferS) (appS (pure $ varB 1) (pure $ varB 0))) (pairS t $ pure ZeroB)
      trb = pairS tWrap . pairS r . pairS b $ pure ZeroB
      -- env: (x, (oracle, trb)); apply the oracle to trb, the resulting
      -- approximant chain to x
      innerBody = appS (appS (pure $ varB 1) (pure . RightB $ RightB EnvB)) (pure $ varB 0)
      -- env: (oracle, trb); capture it and await x
      mainBody = pairS (innerBody >>= deferS) (pure EnvB)
  in pairS (mainBody >>= deferS) trb
