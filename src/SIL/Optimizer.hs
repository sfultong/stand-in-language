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

{- TODO something to convert all closures that don't return zerotype to ones that do

  \a b -> (a,b) : D -> (D -> D)

  (\f x -> f x) ((\a b -> (a,b)) 0) 1

-}


-- converts nested grammar that can be computed locally
precompute :: IExpr -> IExpr
precompute = endoMap f where
  f (PLeft (Pair x _)) = x
  f (PRight (Pair _ x)) = x
  f x = x

optimize :: IExpr -> IExpr
optimize = precompute
