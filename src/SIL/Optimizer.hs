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
  f (Check (Check x tci) (Check tc tctc)) =
    Check x
    (Closure
     (App
      (Closure
       (App
        (Gate (PLeft Var))
        (Pair
         (PLeft Var)
         (App
          (Closure
           (App
            (Gate (PLeft Var))
            (Pair
             (PLeft Var)
             (App tc x)
            )
           )
           Zero
          )
          (App tctc tc)
         )
        )
       )
       Zero
      )
      (App tci x)
     )
     Zero
    )
  f (Check (Check x tci) tco) =
    Check x
    (Closure
     (App
      (Closure
       (App
        (Gate (PLeft Var))
        (Pair
         (PLeft Var)
         (App tci (PLeft (PRight Var)))
        )
       )
       Zero
      )
      (App tco (PLeft Var))
     )
     Zero
    )
  f (Check x (Check tc tctc)) =
    Check x
    (Closure
     (App
      (Closure
       (App
        (Gate (PLeft Var))
        (Pair
         (PLeft Var)
         (App tc x)
        )
       )
       Zero
      )
      (App tctc tc)
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
         (PLeft Var)
         (App tca (PLeft (PLeft (PRight Var))))
        )
       )
       Zero
      )
      (App tcb (PRight (PLeft Var)))
     )
     Zero
    )
  f (Pair (Check a tca) b) =
    Check (Pair a b)
    (Closure
     (App
      tca
      (PRight (PLeft Var))
     )
     Zero
    )
  f (Pair a (Check b tcb)) =
    Check (Pair a b)
    (Closure
     (App
      tcb
      (PLeft (PLeft Var))
     )
     Zero
    )
    -- should I use a closure that ignores its argument and just applies a to the check
    -- or should I synthesize a from its components?
  f (PLeft (Check a tca)) =
    Check (PLeft a)
    (Closure
     (App tca a)
     Zero
    )
  f (PRight (Check a tcb)) =
    Check (PRight a)
    (Closure
     (App tcb a)
     Zero
    )
  f (Trace (Check x tc)) =
    Check (Trace x) tc
  f (Gate (Check x tc)) =
    Check (Gate x)
    (Closure
     (App tc x)
     Zero
    )
  f (App (Check c tcc) (Check i tci)) =
    Check (App c i)
    (Closure
     (App
      (Closure
       (App
        (Gate (PLeft Var))
        (Pair
         (PLeft Var)
         (App tci i)
        )
       )
       Zero
      )
      (App tcc c)
     )
     Zero
    )
  f (App (Check x tc) i) =
    Check (App x i)
    (Closure
     (App tc x)
     Zero
    )
  f (App c (Check x tc)) =
    Check (App c x)
    (Closure
     (App tc x)
     Zero
    )
  f (Closure (Check c tc) Zero) =
    Check (Closure c Zero)
    (Closure
     (App tc c)
     Zero
    )
  f x = x

{- TODO something to convert all closures that don't return zerotype to ones that do

  \a b -> {a,b} : D -> (D -> D)

  (\f x -> f x) ((\a b -> {a,b}) 0) 1

-}

optimize :: IExpr -> IExpr
optimize = partiallyApply
