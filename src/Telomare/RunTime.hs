{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.RunTime where

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Fix
import           Data.Foldable
import           Data.Functor.Foldable hiding (fold)
import           Data.Functor.Identity
import qualified Data.Map              as Map
import           Data.Set              (Set)
import qualified Data.Set              as Set
import           Debug.Trace
import           GHC.Exts              (fromList)
import           Naturals              hiding (debug, debugTrace)
import           PrettyPrint
import           System.IO
import           System.Process
import           Telomare              (AbstractRunTime (eval), DataType (..),
                                        FragIndex (FragIndex), IExpr (..),
                                        IExprF (..), PrettyIExpr (PrettyIExpr),
                                        RunResult, RunTimeError (..),
                                        TelomareLike (fromTelomare, toTelomare))
import           Text.Read             (readMaybe)

debug :: Bool
debug = False

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
        (NPair a b) -> NPair <$> recur a <*> recur b
        NEnv -> pure env
        (NLeft x) -> recur x >>= \y -> case y of
          (NPair l _) -> pure l
          NZero       -> pure NZero
          z           -> error ("nleft on " ++ show z ++ " before " ++ show x)
        (NRight x) -> recur x >>= \y -> case y of
          (NPair _ r) -> pure r
          NZero       -> pure NZero
          z           -> error ("nright on " ++ show z)
        (NDefer ind) -> case Map.lookup ind m of
          (Just x) -> pure x
          _ -> throwError $ GenericRunTimeError ("nEval bad index for function: " ++ show ind) Zero
        NTrace -> pure $ trace (show env) env
        (NSetEnv x) -> recur x >>= \y -> case y of
          (NPair c i) -> case c of
            NGate a b -> case i of
              NZero -> recur a
              _     -> recur b
            _ -> eval i c
          z -> error ("nEval nsetenv - not pair - " ++ show z)
        (NApp c i) -> do
          nc <- recur c
          ni <- recur i
          let appl (NPair c e) i = eval (NPair i e) c
              appl y z = error ("nEval napp appl no pair " ++ show y ++ " --- " ++ show z)
          case nc of
            p@(NPair _ _) -> appl p ni
            (NLamNum n e) -> pure $ case ni of
              (NLamNum m _)     -> NPair (NPair (NNum (n ^ m)) NEnv) e
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
    _        -> throwError $ GenericRunTimeError "nEval: no root frag" Zero

-- |IExpr evaluation with a given enviroment `e`
-- (as in the second element of a closure).
rEval :: (MonadError RunTimeError m)
      => IExpr -- ^ The enviroment.
      -> IExpr -- ^ IExpr to be evaluated.
      -> m IExpr
rEval e = para alg where
  alg :: (MonadError RunTimeError m)
      => (Base IExpr) (IExpr, m IExpr)
      -> m IExpr
  alg = \case
    ZeroF -> pure Zero
    EnvF -> pure e
    (DeferF (ie, _)) -> pure . Defer $ ie
    TraceF -> pure $ trace (show e) e
    (GateF (ie1, _) (ie2, _)) -> pure $ Gate ie1 ie2
    (PairF (_, l) (_, r)) -> Pair <$> l <*> r
    (PRightF (_, x)) -> x >>= \case
      (Pair _ r) -> pure r
      _          -> pure Zero
    (PLeftF (_, x)) -> x >>= \case
      (Pair l _) -> pure l
      _          -> pure Zero
    (SetEnvF (_, x)) -> x >>= \case
      Pair (Defer c) nenv  -> rEval nenv c
      Pair (Gate a _) Zero -> rEval e a
      Pair (Gate _ b) _    -> rEval e b
      -- The next case should never actually occur,
      -- because it should be caught by `typeCheck`.
      z                    -> throwError $ SetEnvError z

-- |The fix point combinator of this function (of type `IExpr -> IExpr -> m IExpr`) yields a function that
-- evaluates an `IExpr` with a given enviroment (another `IExpr`).
iEval :: MonadError RunTimeError m => (IExpr -> IExpr -> m IExpr) -> IExpr -> IExpr -> m IExpr
iEval f env g = let f' = f env in case g of
  Trace -> pure $ trace (show env) env
  Zero -> pure Zero
  -- Abort -> pure Abort
  Defer x -> pure $ Defer x
  Pair a b -> Pair <$> f' a <*> f' b
  Gate a b -> pure $ Gate a b
  Env -> pure env
  SetEnv x -> (f' x >>=) $ \case
    Pair cf nenv -> case cf of
      Defer c -> f nenv c
      -- do we change env in evaluation of a/b, or leave it same? change seems more consistent, leave more convenient
      Gate a b -> case nenv of
        Zero -> f' a
        _    -> f' b
      z -> throwError $ SetEnvError z -- This should never actually occur, because it should be caught by typecheck
    bx -> throwError $ SetEnvError bx -- This should never actually occur, because it should be caught by typecheck
  PLeft g -> f' g >>= \case
    (Pair a _) -> pure a
    _          -> pure Zero
  PRight g -> f' g >>= \case
    (Pair _ x) -> pure x
    _          -> pure Zero

instance TelomareLike IExpr where
  fromTelomare = id
  toTelomare = pure

instance AbstractRunTime IExpr where
  eval = fix iEval Zero
  -- eval = rEval Zero

resultIndex = FragIndex (-1)
instance TelomareLike NExprs where
  fromTelomare = (NExprs . fragsToNExpr) . fragmentExpr
  toTelomare (NExprs m) =
    let fromNExpr x = case x of
          NZero         -> pure Zero
          (NPair a b)   -> Pair <$> fromNExpr a <*> fromNExpr b
          NEnv          -> pure Env
          (NSetEnv x)   -> SetEnv <$> fromNExpr x
          NGate a b     -> Gate <$> fromNExpr a <*> fromNExpr b
          (NLeft x)     -> PLeft <$> fromNExpr x
          (NRight x)    -> PRight <$> fromNExpr x
          NTrace        -> pure Trace
          (NDefer i)    -> Map.lookup i m >>= (fmap Defer . fromNExpr)
          (NOldDefer x) -> Defer <$> fromNExpr x
          _             -> Nothing
    in Map.lookup resultIndex m >>= fromNExpr
instance AbstractRunTime NExprs where
  eval x@(NExprs m) = (\r -> NExprs $ Map.insert resultIndex r m) <$> nEval x

evalAndConvert :: (Show a, AbstractRunTime a) => a -> RunResult IExpr
evalAndConvert x = let ar = eval x in (toTelomare <$> ar) >>= \r -> case r of
  Nothing -> do
    ar' <- ar
    throwError . ResultConversionError $ show ar'
  Just ir -> pure ir

-- |Evaluation with hvm backend
hvmEval :: IExpr -> IO IExpr
hvmEval x = do
  (_, mhout, _, _) <- createProcess (shell ("hvm r ./hvm/backend \"(" <> show x <> ")\"")) { std_out = CreatePipe }
  case mhout of
    Just hout -> do
      hvmOutput <- hGetContents hout
      if (length . lines $ hvmOutput) > 2 then
        case (readMaybe . unlines . drop 2 . lines $ hvmOutput) :: Maybe IExpr of
          Just res -> pure res
          Nothing  -> error $ "Error: fail to read hvm output. \nhvm output:\n" <> hvmOutput
      else error $ "Error: hvm output is not what was expected. \nhvm output: " <> hvmOutput
      pure . read . unlines . drop 2 . lines $ hvmOutput
    Nothing -> error $ "Error: hvm failed to produce output. \nIExpr fed to hvm:\n" <> show x

simpleEval :: IExpr -> IO IExpr
simpleEval x = runExceptT (eval x) >>= \r -> case r of
  Left e  -> fail (show e)
  Right i -> pure i

fastInterpretEval :: IExpr -> IO IExpr
fastInterpretEval e = do
  let traceShow x = if debug then trace ("toNExpr\n" ++ showNExprs x) x else x
      nExpr :: NExprs
      nExpr = traceShow $ fromTelomare e
  result <- runExceptT $ evalAndConvert nExpr
  case result of
    Left e  -> error ("runtime error: " ++ show e)
    Right r -> pure r

{- commenting out until fixed
llvmEval :: NExpr -> IO LLVM.RunResult
llvmEval nexpr = do
  let lmod = LLVM.makeModule nexpr
  when debug $ do
    print $ LLVM.DebugModule lmod
    putStrLn . concat . replicate 100 $ "                                                                     \n"
  result <- catch (LLVM.evalJIT LLVM.defaultJITConfig lmod) $ \(e :: SomeException) -> pure . Left $ show e
  case result of
    Left s -> do
      hPrint stderr nexpr
      hPutStrLn stderr $ "failed llvmEval: " ++ s
      fail s
    Right x -> pure x
-}

optimizedEval :: IExpr -> IO IExpr
optimizedEval = fastInterpretEval

pureIEval :: IExpr -> Either RunTimeError IExpr
pureIEval g = runIdentity . runExceptT $ fix iEval Zero g -- this is the original version

pureEval :: IExpr -> Either RunTimeError IExpr
pureEval = rEval Zero

showPass :: (Show a, MonadIO m) => m a -> m a
showPass a = a >>= (liftIO . print) >> a

tEval :: IExpr -> IO IExpr
tEval x = runExceptT (fix (\f e g -> showPass $ iEval f e g) Zero x) >>= \r -> case r of
  Left e  -> fail (show e)
  Right i -> pure i

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

verifyEval :: IExpr -> IO (Maybe (Either RunTimeError IExpr, Either RunTimeError IExpr))
verifyEval expr =
  let nexpr :: NExprs
      nexpr = fromTelomare expr
  in do
    iResult <- runExceptT $ evalAndConvert expr
    nResult <- runExceptT $ evalAndConvert nexpr
    if iResult == nResult
     then pure Nothing
     else pure $ pure (iResult, nResult)

testNEval = runExceptT . eval . (fromTelomare :: IExpr -> NExprs)
