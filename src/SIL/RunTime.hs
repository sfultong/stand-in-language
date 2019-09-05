{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SIL.RunTime where

import Data.Functor.Identity
import Debug.Trace
import Control.Exception
import Control.Monad.Except
import Control.Monad.Fix
import System.IO (hPutStrLn, stderr)

import SIL
import Naturals hiding (debug, debugTrace)
import PrettyPrint
import qualified Data.Map as Map
import qualified SIL.Llvm as LLVM

debug :: Bool
debug = True

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- cPlus :: (t3 -> t2 -> t1) -> (t3 -> t -> t2) -> t3 -> t -> t1
cPlus :: ((a -> a) -> a -> a) -> ((a -> a) -> a -> a) -> (a -> a) -> a -> a
-- cPlus m n f x = m f (n f x)
cPlus m n f = m f . n f

nEval :: NExprs -> RunResult NExpr
nEval (NExprs m) =
  let eval :: NExpr -> NExpr -> RunResult NExpr
      eval env frag = let recur = eval env in case frag of
        NZero -> pure NZero
        (NPair a b) -> NPair <$> recur a <*> recur b
        NEnv -> pure env
        (NGate x) -> recur x >>= \y -> case y of
          NZero -> pure $ NLeft NEnv
          _ ->  pure $ NRight NEnv
        (NLeft x) -> recur x >>= \y -> case y of
          (NPair l _) -> pure l
          NZero -> pure NZero
          z -> error ("nleft on " ++ show z ++ " before " ++ show x)
        (NRight x) -> recur x >>= \y -> case y of
          (NPair _ r) -> pure r
          NZero -> pure NZero
          z -> error ("nright on " ++ show z)
        (NDefer ind) -> case Map.lookup ind m of
          (Just x) -> pure x
          _ -> throwError $ GenericRunTimeError ("nEval bad index for function: " ++ show ind) Zero
        (NTrace x) -> (\t -> trace (show t) t) <$> recur x
        (NAbort x) -> recur x >>= \y -> case y of
          NZero -> pure NZero
          z -> case toSIL (NExprs $ Map.insert resultIndex z m) of
            Just z' -> throwError . AbortRunTime $ z'
            Nothing -> throwError $ GenericRunTimeError ("Could not convert abort value of: " <> show z) Zero
        (NSetEnv x) -> recur x >>= \y -> case y of
          (NPair c i) -> eval i c
          z -> error ("nEval nsetenv - not pair - " ++ show z)
        (NITE i t e) -> process <$> recur i <*> recur t <*> recur e where
          process NZero _ ne = ne
          process _ nt _ = nt
        (NApp c i) -> do
          nc <- recur c
          ni <- recur i
          let appl (NPair c e) i = eval (NPair i e) c
              appl y z = error ("nEval napp appl no pair " ++ show y ++ " --- " ++ show z)
          case nc of
            p@(NPair _ _) -> appl p ni
            (NLamNum n e) -> pure $ case ni of
              (NLamNum m _) -> NPair (NPair (NNum (n ^ m)) NEnv) e
              (NPartialNum m f) -> NPair (NNum (n * m)) f
            NToNum -> pure $ NApp NToNum ni
            (NApp NToNum (NPair (NPair (NNum nn) NEnv) nenv)) ->
              let fStep 0 _ = 0
                  fStep _ NZero = 0
                  fStep x (NPair pr NZero) = 1 + fStep (x - 1) pr
                  fStep _ z = error ("napp ntonum fstep bad pair: " ++ show z)
              in pure $ NPair (NPair (NNum $ fStep nn ni) NEnv) nenv
            z -> error ("nEval napp error - non pair c - " ++ show z ++ " <<from>> " ++ show c)
        (NOldDefer x) -> pure x
        (NNum x) -> let buildF 0 = NLeft NEnv
                        buildF x = NApp (NLeft (NRight NEnv)) (buildF (x - 1))
                    in pure $ buildF x
        (NTwiddle x) -> recur x >>= \nx -> case nx of
          (NPair (NPair c e) i) -> pure $ NPair c (NPair i e)
          z -> error ("neval ntwiddle not pairpair: " ++ show z)
        z -> pure z
  in case Map.lookup (FragIndex 0) m of
    (Just f) -> eval NZero f
    _ -> throwError $ GenericRunTimeError "nEval: no root frag" Zero

iEval :: MonadError RunTimeError m => (Expr -> Expr -> m Expr) -> Expr -> Expr -> m Expr
iEval f env g = let f' = f env in case g of
  Zero -> pure Zero
  Pair a b -> Pair <$> f' a <*> f' b
  Env -> pure env
  Abort x -> f' x >>= \nx -> if nx == Zero then pure Zero else throwError $ AbortRunTime nx
  SetEnv x -> (f' x >>=) $ \nx -> case nx of
    Pair (Defer c) nenv -> f nenv c
    bx -> throwError $ SetEnvError bx -- This should never actually occur, because it should be caught by typecheck
  Defer x -> pure $ Defer x
  Gate x -> f' x >>= \g -> case g of
    Zero -> pure $ Defer (PLeft Env)
    _ -> pure $ Defer (PRight Env)
  PLeft g -> f' g >>= \g -> case g of
    (Pair a _) -> pure a
    _ -> pure Zero
  PRight g -> f' g >>= \g -> case g of
    (Pair _ x) -> pure x
    _ -> pure Zero
  Trace g -> f' g >>= \g -> pure $ trace (show g) g

toChurch :: Int -> Expr
toChurch x =
  let inner 0 = PLeft Env
      inner x = app (PLeft $ PRight Env) (inner (x - 1))
  in lam (lam (inner x))

instance AbstractRunTime Expr' where
  eval = fmap Expr' . fix iEval Zero . getExpr
  fromSIL = Expr'
  toSIL = pure . getExpr

resultIndex = FragIndex (-1)
instance AbstractRunTime NExprs where
  eval x@(NExprs m) = (\r -> NExprs $ Map.insert resultIndex r m) <$> nEval x
  fromSIL = (NExprs . fragsToNExpr) . fragmentExpr
  toSIL (NExprs m) =
    let fromNExpr x = case x of
          NZero -> pure Zero
          (NPair a b) -> Pair <$> fromNExpr a <*> fromNExpr b
          NEnv -> pure Env
          (NSetEnv x) -> SetEnv <$> fromNExpr x
          (NAbort x) -> Abort <$> fromNExpr x
          (NGate x) -> Gate <$> fromNExpr x
          (NLeft x) -> PLeft <$> fromNExpr x
          (NRight x) -> PRight <$> fromNExpr x
          (NTrace x) -> Trace <$> fromNExpr x
          (NDefer i) -> Map.lookup i m >>= (fmap Defer . fromNExpr)
          (NOldDefer x) -> Defer <$> fromNExpr x
          _ -> Nothing
    in Map.lookup resultIndex m >>= fromNExpr

evalAndConvert :: (Show a, AbstractRunTime a) => a -> RunResult Expr
evalAndConvert x = let ar = eval x in (toSIL <$> ar) >>= \r -> case r of
  Nothing -> do
    ar' <- ar
    throwError . ResultConversionError $ show ar'
  Just ir -> pure ir

simpleEval :: Expr -> IO Expr
simpleEval x = runExceptT (eval (fromSIL x :: Expr')) >>= \r -> case r of
  Left e -> fail (show e)
  Right i -> case toSIL i of
    Just r -> pure r
    Nothing -> fail "Should be impossible for conversion of Expr' to Expr to fail"

fastInterpretEval :: Expr -> IO Expr
fastInterpretEval e = do
  let traceShow x = if debug then trace ("toNExpr\n" ++ showNExprs x) x else x
      nExpr :: NExprs
      nExpr = fromSIL e
  result <- runExceptT $ evalAndConvert nExpr
  case result of
    Left e -> error ("runtime error: " ++ show e)
    Right r -> pure r

llvmEval :: NExpr -> IO LLVM.RunResult
llvmEval nexpr = do
  let lmod = LLVM.makeModule nexpr
  when debug $ do
    print $ LLVM.DebugModule lmod
    putStrLn . concat . take 100 . repeat $ "                                                                     \n"
  result <- catch (LLVM.evalJIT LLVM.defaultJITConfig lmod) $ \(e :: SomeException) -> pure . Left $ show e
  case result of
    Left s -> do
      hPutStrLn stderr . show $ nexpr
      hPutStrLn stderr $ "failed llvmEval: " ++ s
      fail s
    Right x -> pure x

optimizedEval :: Expr -> IO Expr
optimizedEval = fastInterpretEval -- TODO fix

pureEval :: Expr -> Either RunTimeError Expr
pureEval g = runIdentity . runExceptT $ fix iEval Zero g

showPass :: (Show a, MonadIO m) => m a -> m a
showPass a = a >>= (liftIO . print) >> a

tEval :: Expr -> IO Expr
tEval x = runExceptT (fix (\f e g -> showPass $ iEval f e g) Zero x) >>= \r -> case r of
  Left e -> fail (show e)
  Right i -> pure i

typedEval :: (Expr -> DataType -> Bool) -> Expr -> (Expr -> IO ()) -> IO ()
typedEval typeCheck iexpr prettyPrint = if typeCheck iexpr DataOnlyType
  then simpleEval iexpr >>= prettyPrint
  else putStrLn "failed typecheck"

debugEval :: (Expr -> DataType -> Bool) -> Expr -> IO ()
debugEval typeCheck iexpr = if typeCheck iexpr DataOnlyType
  then tEval iexpr >>= (print . PrettyExpr)
  else putStrLn "failed typecheck"

fullEval typeCheck i = typedEval typeCheck i print

prettyEval typeCheck i = typedEval typeCheck i (print . PrettyExpr)

verifyEval :: Expr -> IO (Maybe (Either RunTimeError Expr, Either RunTimeError Expr))
verifyEval expr =
  let nexpr :: NExprs
      nexpr = fromSIL expr
  in do
    iResult <- runExceptT $ evalAndConvert (Expr' expr)
    nResult <- runExceptT $ evalAndConvert nexpr
    if iResult == nResult
     then pure Nothing
     else pure $ pure (iResult, nResult)

testNEval = runExceptT . eval . (fromSIL :: Expr -> NExprs)
