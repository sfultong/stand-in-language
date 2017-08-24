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

-- merge and push checks up to top level of expression
promoteChecks :: IExpr -> IExpr
promoteChecks = endoMap f where
  f (Check (Check x tci) tco) =
    Check x
    (Closure
     (App
      (Closure
       (App
        (Gate (PLeft Var))
        (Pair
         (App tci (PLeft (PRight Var)))
         (PLeft Var)
        )
       )
       Zero
      )
      (App tco (PLeft Var))
     )
     Zero
    )
  f (Pair (Check a tca) (Check b tcb)) =
    Check (Pair a b)
    (Closure
     (App
      (Closure
       (App
        (Gate (PLeft Var))
        (Pair
         (App tca (PRight (PLeft (PRight Var))))
         (PLeft Var)
        )
       )
       Zero
      )
      (App tcb (PLeft (PLeft Var)))
     )
     Zero
    )

{- TODO something to convert all closures that don't return zerotype to ones that do

  \a b -> {a,b} : D -> (D -> D)

  (\f x -> f x) ((\a b -> {a,b}) 0) 1

-}

optimize :: IExpr -> IExpr
optimize = partiallyApply
