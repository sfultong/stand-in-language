module SIL.Eval where

import Control.Monad.Except

import SIL
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer

data ExpP
  = ZeroP
  | PairP ExpP ExpP
  | VarP
  | SetEnvP ExpP Bool
  | DeferP ExpP
  | TwiddleP ExpP
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
  endoMap f (TwiddleP x) = f . TwiddleP $ endoMap f x
  endoMap f (AbortP x) = f . AbortP $ endoMap f x
  endoMap f (GateP x) = f . GateP $ endoMap f x
  endoMap f (LeftP x) = f . LeftP $ endoMap f x
  endoMap f (RightP x) = f . RightP $ endoMap f x
  endoMap f (TraceP x) = f . TraceP $ endoMap f x

data EvalError
  = RTE RunTimeError
  | TCE TypeCheckError
  deriving (Eq, Ord, Show)

type ExpFullEnv = ExprA Bool

annotateEnv :: IExpr -> (Bool, ExpP)
annotateEnv Zero = (True, ZeroP)
annotateEnv (Pair a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, PairP na nb)
annotateEnv Env = (False, VarP)
annotateEnv (SetEnv x) = let (xt, nx) = annotateEnv x in (xt, SetEnvP nx xt)
annotateEnv (Defer x) = let (_, nx) = annotateEnv x in (True, DeferP nx)
annotateEnv (Twiddle x) = TwiddleP <$> annotateEnv x
annotateEnv (Abort x) = AbortP <$> annotateEnv x
annotateEnv (Gate x) = GateP <$> annotateEnv x
annotateEnv (PLeft x) = LeftP <$> annotateEnv x
annotateEnv (PRight x) = RightP <$> annotateEnv x
annotateEnv (Trace x) = TraceP <$> annotateEnv x

fromFullEnv :: Applicative a => (ExpP -> a IExpr) -> ExpP -> a IExpr
fromFullEnv _ ZeroP = pure Zero
fromFullEnv f (PairP a b) = Pair <$> f a <*> f b
fromFullEnv _ VarP = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x) = Defer <$> f x
fromFullEnv f (TwiddleP x) = Twiddle <$> f x
fromFullEnv f (AbortP x) = Abort <$> f x
fromFullEnv f (GateP x) = Gate <$> f x
fromFullEnv f (LeftP x) = PLeft <$> f x
fromFullEnv f (RightP x) = PRight <$> f x
fromFullEnv f (TraceP x) = Trace <$> f x

partiallyEvaluate :: ExpP -> Either RunTimeError IExpr
-- partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= pureREval)
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= (pureEval . optimize))
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

eval :: IExpr -> Either EvalError IExpr
eval expr = case inferType expr of
  Left err -> Left $ TCE err
  Right _ -> case partiallyEvaluate (snd $ annotateEnv expr) of
    Left err -> Left $ RTE err
    Right x -> pure x

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case eval iexpr of
  Left err -> putStrLn . concat $ ["Failed compiling main, ", show err]
  Right peExp ->
    let mainLoop s = do
             result <- optimizedEval (app peExp s)
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
    in mainLoop Zero
