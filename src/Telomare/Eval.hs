{-# LANGUAGE LambdaCase #-}
module Telomare.Eval where

import           Control.Monad.Except
import           Data.Map             (Map)
import qualified Data.Map             as Map
import           Debug.Trace

import           Telomare
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker
-- TODO: FIX.
-- Maybe specifying ghc's all-cabal-hashes
-- import Telomare.Serializer

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
  endoMap f ZeroP          = f ZeroP
  endoMap f (PairP a b)    = f $ PairP (endoMap f a) (endoMap f b)
  endoMap f VarP           = f VarP
  endoMap f (SetEnvP x fe) = f $ SetEnvP (endoMap f x) fe
  endoMap f (DeferP x)     = f . DeferP $ endoMap f x
  endoMap f AbortP         = f AbortP
  endoMap f (GateP a b)    = f $ GateP (endoMap f a) (endoMap f b)
  endoMap f (LeftP x)      = f . LeftP $ endoMap f x
  endoMap f (RightP x)     = f . RightP $ endoMap f x
  endoMap f TraceP         = f TraceP

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
fromFullEnv _ ZeroP         = pure Zero
fromFullEnv f (PairP a b)   = Pair <$> f a <*> f b
fromFullEnv _ VarP          = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x)    = Defer <$> f x
fromFullEnv _ AbortP        = pure Abort
fromFullEnv f (GateP a b)   = Gate <$> f a <*> f b
fromFullEnv f (LeftP x)     = PLeft <$> f x
fromFullEnv f (RightP x)    = PRight <$> f x
fromFullEnv _ TraceP        = pure Trace

instance TelomareLike ExpP where
  fromTelomare = snd . annotateEnv
  toTelomare = fix fromFullEnv

partiallyEvaluate :: ExpP -> Either RunTimeError IExpr
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= (pureEval . optimize))
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

eval' :: IExpr -> Either String IExpr
eval' = pure

findChurchSize :: Term3 -> Term4
{-
findChurchSize term =
  let abortsAt i = (\(PResult (_, b)) -> b) . fix pEval PZero . fromTelomare $ convertPT i term
      -- evaluating large church numbers is currently impractical, just fail if found
      (ib, ie) = if not (abortsAt 255) then (0, 255) else error "findchurchsize TODO" -- (256, maxBound)
      findC b e | b > e = b
      findC b e = let midpoint = (\n -> trace ("midpoint is now " <> show n) n) $ div (b + e) 2
                  in if abortsAt midpoint then findC (midpoint + 1) e else findC b midpoint
  in convertPT (findC ib ie) term
-}
findChurchSize = convertPT 255

{-
findAllSizes :: Term2 -> (Bool, Term3)
findAllSizes = let doChild (True, x) = TTransformedGrammar $ findChurchSize x
                   doChild (_, x) = TTransformedGrammar $ convertPT 0 x
                   doChildren l = let nl = map findAllSizes l
                                  in case sum (map (fromEnum . fst) nl) of
                                       0 -> (False, map snd nl)
                                       1 -> (True, map snd nl)
                                       _ -> (False, map doChild nl)
               in \case
  TZero -> (False, TZero)
  TPair a b -> let (c, [na, nb]) = doChildren [a,b] in (c, TPair na nb)
  TVar n -> (False, TVar n)
  TApp a b -> let (c, [na, nb]) = doChildren [a,b] in (c, TApp na nb)
  TCheck a b -> let (c, [na, nb]) = doChildren [a,b] in (c, TCheck na nb)
  TITE i t e -> let (c, [ni, nt, ne]) = doChildren [i,t,e] in (c, TITE ni nt ne)
  TLeft x -> TLeft <$> findAllSizes x
  TRight x -> TRight <$> findAllSizes x
  TTrace x -> TTrace <$> findAllSizes x
  TLam lt x -> TLam lt <$> findAllSizes x
  TLimitedRecursion -> (True, TLimitedRecursion)
-}

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case eval' iexpr of
  Left err -> putStrLn . concat $ ["Failed compiling main, ", show err]
  Right peExp ->
    let mainLoop s = do
          -- result <- optimizedEval (app peExp s)
          result <- simpleEval (app peExp s)
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
