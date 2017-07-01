module SIL.Optimizer where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL

-- TODO think about how removing var indexing will make it hard to figure out closure arity
-- oh wait, closures will all take one argument and return one argument, and closure
-- rewriting can make it so that returned argument is ZeroType, as long as what we pass in
-- contains prerequisite closures.


-- IExpr annotated with unbound vars
data IExprV
  = VZero
  | VPair IExprV IExprV
  | VVar IExprV
  | VApp IExprV IExprV
  | VAnno IExprV IExprV
  | VGate IExprV
  | VLeft IExprV
  | VRight IExprV
  | VTrace IExprV
  | VClosure IExprV IExprV
  deriving (Eq, Show, Ord)

partiallyApply :: IExpr -> IExpr
partiallyApply = endoMap f where
  f (App (Closure (Closure ic Zero) env) i) = Closure ic (Pair i env)
  f x = x

applyOuterVarsSingle :: Int -> (IExpr -> IExpr) -> IExpr -> (IExpr, Set Int)
applyOuterVarsSingle applied wrapper x =
  let (nx, vx) = applyOuterVars applied x in (wrapper nx, vx)

applyToInnerClosure :: Int -> IExpr -> IExpr
applyToInnerClosure applied (Closure c@(Closure _ _) Zero) =
  Closure (applyToInnerClosure applied c) Zero
applyToInnerClosure applied (Closure c Zero) =
  let (nc, vc) = applyOuterVars 0 c
      outerVars = filter (>= applied) $ Set.toAscList vc
      wrappedC = foldr (\i c -> App c . Var $ i2g i) nc outerVars
  in wrappedC
applyToInnerClosure _ x = error $ concat ["applytoIC, how did we get ", show x]

-- apply outer vars to inner closures
applyOuterVars :: Int -> IExpr -> (IExpr, Set Int)
applyOuterVars _ Zero = (Zero, Set.empty)
applyOuterVars applied (Pair a b) =
  let (na, nav) = applyOuterVars applied a
      (nb, nbv) = applyOuterVars applied b
  in (Pair na nb, Set.union nav nbv)
applyOuterVars _ (Var v) = (Var v, Set.singleton $ g2i v)
applyOuterVars applied (App c i) =
  let (ni, vi) = applyOuterVars applied i
      (nc, vc) = applyOuterVars (applied + 1) c
  in (App nc ni, Set.union vi vc)
applyOuterVars applied (Anno c t) =
  let (nc, vc) = applyOuterVars applied c
      (nt, vt) = applyOuterVars applied t
  in (Anno nc nt, Set.union vc vt)
applyOuterVars applied (Gate g) = applyOuterVarsSingle applied Gate g
applyOuterVars applied (PLeft x) = applyOuterVarsSingle applied PLeft x
applyOuterVars applied (PRight x) = applyOuterVarsSingle applied PRight x
applyOuterVars applied (Trace x) = applyOuterVarsSingle applied Trace x
applyOuterVars applied c@(Closure _ _) = (applyToInnerClosure applied c, Set.empty)

optimize :: IExpr -> IExpr
optimize = partiallyApply . fst . applyOuterVars 0
