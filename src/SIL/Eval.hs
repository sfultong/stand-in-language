{-# LANGUAGE LambdaCase #-}
module SIL.Eval where

import Control.Monad.Except
import Data.Functor.Foldable

import SIL
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer

{-
data ExpP
  = ZeroP
  | PairP ExpP ExpP
  | VarP
  | SetEnvP ExpP Bool
  | DeferP ExpP
  | AbortP ExpP
  | GateP ExpP
  | LeftP ExpP
  | RightP ExpP
  | TraceP ExpP
  deriving (Eq, Show, Ord)

instance EndoMapper ExpP where
  endoMap f ZeroP = f ZeroP
  endoMap f (PairP a b) = f $ PairP (endoMap f a) (endoMap f b)
  endoMap f VarP = f VarP
  endoMap f (SetEnvP x fe) = f $ SetEnvP (endoMap f x) fe
  endoMap f (DeferP x) = f . DeferP $ endoMap f x
  endoMap f (AbortP x) = f . AbortP $ endoMap f x
  endoMap f (GateP x) = f . GateP $ endoMap f x
  endoMap f (LeftP x) = f . LeftP $ endoMap f x
  endoMap f (RightP x) = f . RightP $ endoMap f x
  endoMap f (TraceP x) = f . TraceP $ endoMap f x
-}

data EvalError
  = RTE RunTimeError
  | TCE TypeCheckError
  deriving (Eq, Ord, Show)

type ExpP = ExprA Bool

{-
annotateEnv :: Expr -> (Bool, ExpP)
annotateEnv Zero = (True, ZeroP)
annotateEnv (Pair a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, PairP na nb)
annotateEnv Env = (False, VarP)
annotateEnv (SetEnv x) = let (xt, nx) = annotateEnv x in (xt, SetEnvP nx xt)
annotateEnv (Defer x) = let (_, nx) = annotateEnv x in (True, DeferP nx)
annotateEnv (Abort x) = AbortP <$> annotateEnv x
annotateEnv (Gate x) = GateP <$> annotateEnv x
annotateEnv (PLeft x) = LeftP <$> annotateEnv x
annotateEnv (PRight x) = RightP <$> annotateEnv x
annotateEnv (Trace x) = TraceP <$> annotateEnv x
-}
annotateEnv :: Expr -> ExpP
annotateEnv = cata $ \orig -> case orig of
  EnvF -> Fix $ ExprAF False EnvF
  DeferF x -> Fix $ ExprAF True (DeferF x)
  x -> let protectedVars = foldl (\b a -> b && (eanno $ project a)) True x
       in Fix $ ExprAF protectedVars x

{-
purePEval :: ExpP -> Either RunTimeError Expr
purePEval = case optimize <$> toSIL x of
  Just e -> pureEval e
  Nothing -> Left $ ResultConversionError "should be impossible"

pexprToExpr :: ExpP -> Expr
pexprToExpr = cata (embed . exprA)
-}

{-
instance AbstractRunTime ExpP where
  fromSIL = annotateEnv
  toSIL = pure . cata (embed . exprA)
  eval x = case fromSIL <$> purePEval x of
    Right r -> pure r
    Left f -> throwError f
-}

{-
fromFullEnv :: Applicative a => (ExpP -> a Expr) -> ExpP -> a Expr
fromFullEnv _ ZeroP = pure Zero
fromFullEnv f (PairP a b) = Pair <$> f a <*> f b
fromFullEnv _ VarP = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x) = Defer <$> f x
fromFullEnv f (AbortP x) = Abort <$> f x
fromFullEnv f (GateP x) = Gate <$> f x
fromFullEnv f (LeftP x) = PLeft <$> f x
fromFullEnv f (RightP x) = PRight <$> f x
fromFullEnv f (TraceP x) = Trace <$> f x
-}

partiallyEvaluate :: ExpP -> Either RunTimeError Expr
{-
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= (pureEval . optimize))
partiallyEvaluate x = fromFullEnv partiallyEvaluate x
-}
partiallyEvaluate = cata $ \case
  (ExprAF True e@(SetEnvF _)) -> (embed <$> sequence e) >>= pureEval
  x -> (embed . exprA) <$> sequence x

eval' :: Expr -> Either EvalError Expr
eval' expr = case inferType expr of
  Left err -> Left $ TCE err
  Right _ -> case partiallyEvaluate $ annotateEnv expr of
    Left err -> Left $ RTE err
    Right x -> pure x

evalLoop :: Expr -> IO ()
evalLoop iexpr = case eval' iexpr of
  Left err -> putStrLn . concat $ ["Failed compiling main, ", show err]
  Right peExp ->
    let mainLoop s = do
             result <- optimizedEval (app peExp s)
             case result of
               Zero -> putStrLn "aborted"
  {-
               (Pair disp newState) -> do
                 putStrLn . g2s $ disp
                 case newState of
                   Zero -> putStrLn "done"
                   _ -> do
                     inp <- s2g <$> getLine
                     mainLoop $ Pair inp newState
-}
               (Pair disp newState) -> case (g2s disp, newState) of
                 (Nothing, _) -> putStrLn ("error decoding " <> show disp)
                 (Just m, Zero) -> do
                   putStrLn m
                   putStrLn "done"
                 (Just m, _) -> do
                   putStrLn m
                   inp <- s2g <$> getLine
                   mainLoop $ Pair inp newState
               r -> putStrLn $ concat ["runtime error, dumped ", show r]
    in mainLoop Zero
