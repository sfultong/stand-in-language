module SIL.RunTime where

import Data.Functor.Identity
import Debug.Trace
import Control.Monad.Fix

import SIL
import SIL.Optimizer

lookupEnv :: IExpr -> Int -> Maybe IExpr
lookupEnv (Pair i _) 0 = Just i
lookupEnv (Pair _ c) n = lookupEnv c (n - 1)
lookupEnv _ _ = Nothing

{-
iEval :: Monad m => ([Result] -> IExpr -> m Result)
  -> [Result] -> IExpr -> m Result
-}
iEval f env g = let f' = f env in case g of
  Zero -> pure Zero
  Pair a b -> do
    na <- f' a
    nb <- f' b
    pure $ Pair na nb
  Var -> pure env
  Anno c t -> f' c
  App g cexp -> do --- given t, type {{a,t},{a,t}}
    ng <- f' g
    i <- f' cexp
    apply f ng i
  Gate x -> f' x >>= \g -> case g of
    Zero -> pure $ Closure (PLeft (PLeft Var)) Zero
    _ -> pure $ Closure (PRight (PLeft Var)) Zero
  PLeft g -> f' g >>= \g -> case g of
    (Pair a _) -> pure a
    _ -> pure Zero
  PRight g -> f' g >>= \g -> case g of
    (Pair _ x) -> pure x
    _ -> pure Zero
  Trace g -> f' g >>= \g -> pure $ trace (show g) g
  Closure c Zero -> pure $ Closure c env
  Closure _ e -> fail $ concat ["unexpected closure with environment ", show e]

{-
apply :: Monad m => ([Result] -> IExpr -> m Result) -> Result -> Result -> m Result
-}
apply f (Closure g env) v = f (Pair v env) g
apply _ g _ = error $ "not a closure " ++ show g

toChurch :: Int -> IExpr
toChurch x =
  let inner 0 = PLeft Var
      inner x = App (PLeft $ PRight Var) (inner (x - 1))
  in lam (lam (inner x))

simpleEval :: IExpr -> IO IExpr
simpleEval = fix iEval Zero

optimizedEval :: IExpr -> IO IExpr
optimizedEval = fmap optimize . simpleEval

pureEval :: IExpr -> IExpr
pureEval g = runIdentity $ fix iEval Zero g

showPass :: Show a => IO a -> IO a
showPass a = a >>= print >> a

tEval :: IExpr -> IO IExpr
tEval = fix (\f e g -> showPass $ iEval f e g) Zero

typedEval :: (IExpr -> DataType -> Bool) -> IExpr -> (IExpr -> IO ()) -> IO ()
typedEval typeCheck iexpr prettyPrint = if typeCheck iexpr ZeroType
  then simpleEval iexpr >>= prettyPrint
  else putStrLn "failed typecheck"

debugEval :: (IExpr -> DataType -> Bool) -> IExpr -> IO ()
debugEval typeCheck iexpr = if typeCheck iexpr ZeroType
  then tEval iexpr >>= (print . PrettyIExpr)
  else putStrLn "failed typecheck"

fullEval typeCheck i = typedEval typeCheck i print

prettyEval typeCheck i = typedEval typeCheck i (print . PrettyIExpr)

evalLoop :: (IExpr -> DataType -> Bool) -> IExpr -> IO ()
evalLoop typeCheck iexpr = if typeCheck iexpr (ArrType ZeroType ZeroType)
  then let mainLoop s = do
             result <- simpleEval $ App optIExpr s
             case result of
               Zero -> putStrLn "aborted"
               (Pair disp newState) -> do
                 putStrLn . g2s $ disp
                 case newState of
                   Zero -> putStrLn "done"
                   _ -> do
                     inp <- s2g <$> getLine
                     mainLoop $ Pair inp newState
               r -> putStrLn $ concat ["runtime error, dumped ", show r]
           optIExpr = optimize iexpr
       in mainLoop Zero
  else putStrLn "failed typecheck"
