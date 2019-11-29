module SIL.Eval where

import Control.Monad.Except

import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer

data ExpP
  = ZeroP
  | PairP ExpP ExpP
  | VarP
  | SetEnvP ExpP Bool
  | DeferP ExpP
  | AbortP
  | GateP ExpP ExpP
  | LeftP ExpP
  | RightP ExpP
  | TraceP
  deriving (Eq, Show, Ord)

instance EndoMapper ExpP where
  endoMap f ZeroP = f ZeroP
  endoMap f (PairP a b) = f $ PairP (endoMap f a) (endoMap f b)
  endoMap f VarP = f VarP
  endoMap f (SetEnvP x fe) = f $ SetEnvP (endoMap f x) fe
  endoMap f (DeferP x) = f . DeferP $ endoMap f x
  endoMap f AbortP = f AbortP
  endoMap f (GateP a b) = f $ GateP (endoMap f a) (endoMap f b)
  endoMap f (LeftP x) = f . LeftP $ endoMap f x
  endoMap f (RightP x) = f . RightP $ endoMap f x
  endoMap f TraceP = f TraceP

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
annotateEnv Abort = (True, AbortP)
annotateEnv (Gate a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, GateP na nb)
annotateEnv (PLeft x) = LeftP <$> annotateEnv x
annotateEnv (PRight x) = RightP <$> annotateEnv x
annotateEnv Trace = (False, TraceP)

fromFullEnv :: Applicative a => (ExpP -> a IExpr) -> ExpP -> a IExpr
fromFullEnv _ ZeroP = pure Zero
fromFullEnv f (PairP a b) = Pair <$> f a <*> f b
fromFullEnv _ VarP = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x) = Defer <$> f x
fromFullEnv _ AbortP = pure Abort
fromFullEnv f (GateP a b) = Gate <$> f a <*> f b
fromFullEnv f (LeftP x) = PLeft <$> f x
fromFullEnv f (RightP x) = PRight <$> f x
fromFullEnv _ TraceP = pure Trace

instance SILLike ExpP where
  fromSIL = snd . annotateEnv
  toSIL = fix fromFullEnv

partiallyEvaluate :: ExpP -> Either RunTimeError IExpr
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= (pureEval . optimize))
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

eval' :: IExpr -> Either EvalError IExpr
eval' expr = case inferType expr of
  Left err -> Left $ TCE err
  {-
  Right _ -> case partiallyEvaluate (snd $ annotateEnv expr) of
    Left err -> Left $ RTE err
    Right x -> pure x
-}
  Right _ -> pure expr

findChurchSize :: Term2 -> IExpr
findChurchSize term =
  let abortsAt i = snd . fix pEval PZero . fromSIL $ convertPT i term
      -- evaluating large church numbers is currently impractical, just fail if found
      (ib, ie) = if abortsAt 255 term then (0, 255) else error "findchurchsize TODO" -- (256, maxBound)
      findC b e | b > e = b
      findC b e = let midpoint = div (b + e) 2
                  in if abortsAt midpoint then findC b midpoint else findC (midpoint + 1) e
  in convertPT (findC ib ie) term

resolveBinding :: String -> Bindings -> Maybe IExpr
resolveBinding name bindings = Map.lookup name bindings >>=
  \b -> convertPT <$> debruijinize [] b

printBindingTypes :: Bindings -> IO ()
printBindingTypes bindings =
  let showType (s, iexpr) = putStrLn $ case inferType iexpr of
        Left pa -> concat [s, ": bad type -- ", show pa]
        Right ft ->concat [s, ": ", show . PrettyPartialType $ ft]
      resolvedBindings = mapM (\(s, b) -> debruijinize [] b >>=
                                (\b -> pure (s, convertPT b))) $ Map.toList bindings
  in resolvedBindings >>= mapM_ showType

parseMain :: Bindings -> String -> Either ParseError IExpr
parseMain prelude s = parseWithPrelude prelude s >>= getMain where
  getMain bound = case Map.lookup "main" bound of
    Nothing -> fail "no main method found"
    Just main -> convertPT <$> debruijinize [] main

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case eval' iexpr of
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
