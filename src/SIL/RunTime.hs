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
import Naturals
import PrettyPrint
import qualified Data.Map as Map
import qualified SIL.Llvm as LLVM

debug :: Bool
debug = True

-- runtime expression
data RExpr
  = RZero
  | RPair !RExpr !RExpr
  | REnv
  | RAbort !RExpr
  | RGate !RExpr
  | RLeft !RExpr
  | RRight !RExpr
  | RTrace !RExpr
  | RSetEnv !RExpr
  | RDefer !RExpr
  -- machine optimized instructions
  | RITE !RExpr !RExpr !RExpr
  | RChurch !Int !(Maybe RExpr)
  deriving (Eq, Show, Ord)

instance EndoMapper RExpr where
  endoMap f RZero = f RZero
  endoMap f (RPair a b) = f $ RPair (endoMap f a) (endoMap f b)
  endoMap f REnv = f REnv
  endoMap f (RAbort x) = f . RAbort $ endoMap f x
  endoMap f (RGate x) = f . RGate $ endoMap f x
  endoMap f (RLeft x) = f . RLeft $ endoMap f x
  endoMap f (RRight x) = f . RRight $ endoMap f x
  endoMap f (RTrace x) = f . RTrace $ endoMap f x
  endoMap f (RSetEnv x) = f . RSetEnv $ endoMap f x
  endoMap f (RDefer x) = f . RDefer $ endoMap f x
  endoMap f (RITE i t e) = f $ RITE (endoMap f i) (endoMap f t) (endoMap f e)
  endoMap f r@(RChurch _ Nothing) = f r

-- cPlus :: (t3 -> t2 -> t1) -> (t3 -> t -> t2) -> t3 -> t -> t1
cPlus :: ((a -> a) -> a -> a) -> ((a -> a) -> a -> a) -> (a -> a) -> a -> a
-- cPlus m n f x = m f (n f x)
cPlus m n f = m f . n f

toRExpr :: IExpr -> RExpr
toRExpr Zero = RZero
toRExpr (Pair a b) = RPair (toRExpr a) (toRExpr b)
toRExpr Env = REnv
toRExpr (Abort x) = RAbort $ toRExpr x
toRExpr (Gate x) = RGate $ toRExpr x
toRExpr (PLeft x) = RLeft $ toRExpr x
toRExpr (PRight x) = RRight $ toRExpr x
toRExpr (Trace x) = RTrace $ toRExpr x
toRExpr (SetEnv x) = RSetEnv $ toRExpr x
toRExpr (Defer x) = RDefer $ toRExpr x

fromRExpr :: RExpr -> IExpr
fromRExpr RZero = Zero
fromRExpr (RPair a b) = Pair (fromRExpr a) (fromRExpr b)
fromRExpr REnv = Env
fromRExpr (RAbort x) = Abort $ fromRExpr x
fromRExpr (RGate x) = Gate $ fromRExpr x
fromRExpr (RLeft x) = PLeft $ fromRExpr x
fromRExpr (RRight x) = PRight $ fromRExpr x
fromRExpr (RTrace x) = Trace $ fromRExpr x
fromRExpr (RSetEnv x) = SetEnv $ fromRExpr x
fromRExpr (RDefer x) = Defer $ fromRExpr x
fromRExpr (RITE i t e) = app (Gate $ fromRExpr i) (Pair (fromRExpr e) (fromRExpr t))
fromRExpr (RChurch i Nothing) = toChurch i

data RunTimeError
  = AbortRunTime IExpr
  | SetEnvError IExpr
  | GenericRunTimeError String IExpr
  deriving (Eq, Ord)

instance Show RunTimeError where
  show (AbortRunTime a) = "Abort: " ++ (show $ g2s a)
  show (SetEnvError e) = "Can't SetEnv: " ++ show e
  show (GenericRunTimeError s i) = "Generic Runtime Error: " ++ s ++ " -- " ++ show i

rEval :: MonadError RunTimeError m => (RExpr -> RExpr -> m RExpr) -> RExpr -> RExpr -> m RExpr
rEval f env g = let f' = f env
                    rApply (RPair ng eenv) v = f (RPair v eenv) ng
                    rApply (RChurch ci Nothing) v = pure $ RChurch ci (Just v)
                    rApply (RChurch ci (Just cf)) v =
                      let step 0 cv = pure cv
                          step x cv = rApply cf cv >>= step (x - 1)
                      in step ci v
                    rApply ng _ = throwError $ GenericRunTimeError "rApply: not a closure -- " (fromRExpr ng)
                    rApply2 (RChurch ci Nothing) (RPair cf (RPair iv _)) = rApply (RChurch ci (Just cf)) iv
                    rApply2 (RChurch ci Nothing) (RPair cf _) = pure $ RChurch ci (Just cf)
                    rApply2 rc@(RChurch _ _) (RPair iv _) = rApply rc iv
                    rApply2 g nenv = f nenv g
                in case g of
  RZero -> pure RZero
  (RPair a b) -> RPair <$> f' a <*> f' b
  REnv -> pure env
  RAbort x -> f' x >>= \nx -> if nx == RZero then pure RZero
                              else throwError $ AbortRunTime (fromRExpr nx)
  RDefer x -> pure x
  -- this seems a bit hacky
  RSetEnv x -> f' x >>= \g -> case g of
    RPair c i -> rApply2 c i
    bx -> throwError $ SetEnvError (fromRExpr bx)
  RGate x -> f' x >>= \g -> case g of
    RZero -> pure $ RLeft REnv
    _ -> pure $ RRight REnv
  RLeft g -> f' g >>= \g -> case g of
    (RPair a _) -> pure a
    _ -> pure RZero
  RRight g -> f' g >>= \g -> case g of
    (RPair _ b) -> pure b
    _ -> pure RZero
  RTrace g -> f' g >>= \g -> pure $ trace (show g) g
  RITE i t e -> f' i >>= \ng -> case ng of
    RZero -> f' e
    _ -> f' t
  r@(RChurch _ _) -> pure r

nEval :: MonadError RunTimeError m => NExprs -> m NExpr
nEval (NExprs m) =
  let eval env frag = let recur = eval env in case frag of
        NZero -> pure NZero
        (NPair a b) -> NPair <$> recur a <*> recur b
        NEnv -> pure env
        (NGate x) -> recur x >>= \y -> case y of
          NZero -> pure $ NLeft NEnv
          _ ->  pure $ NRight NEnv
        (NLeft x) -> recur x >>= \y -> case y of
          (NPair l _) -> pure l
          NZero -> pure NZero
          z -> error ("nleft on " ++ show z)
        (NRight x) -> recur x >>= \y -> case y of
          (NPair _ r) -> pure r
          NZero -> pure NZero
          z -> error ("nright on " ++ show z)
        (NDefer ind) -> case Map.lookup ind m of
          (Just (x, _)) -> pure x
          _ -> throwError $ GenericRunTimeError "nEval bad index for function" Zero
        (NTrace x) -> (\t -> trace (show t) t) <$> recur x
        (NAbort x) -> recur x >>= \y -> case y of
          NZero -> pure NZero
          z -> throwError . AbortRunTime . fromNExpr $ z
        (NSetEnv x) -> recur x >>= \y -> case y of
          (NPair c i) -> eval i c
          z -> error ("nEval nsetenv - not pair - " ++ show z)
  {-
        (NSetEnv x) ->
          let se (NPair (NChurchAppOne i f) senv) = trace "making stuff" $ do
                nf <- recur f
                recur i >>= \ni -> case ni of
                  (NNum nn) -> trace ("doing the " ++ show nn) iterate (>>= appl nf) (pure senv) !! (fromIntegral nn)
                  z -> error ("nEval nSetEnv churchapp, no nnum, instead " ++ show z)
              se (NPair f nenv) = eval nenv f
              se z = throwError . SetEnvError $ fromNExpr z
              appl (NPair c e) i = trace ("evaluating appl") eval (NPair i e) c
              appl z i = error ("nEval nSetEnv error " ++ show z ++ " <-- " ++ show i)
          in trace ("setenvinginging\n" ++ show x) recur x >>= se
-}
  {-
        (NConvertSetEnv x) -> recur x >>= \y -> case y of
          (NPair (NNum i) (NPair f _)) -> pure $ NForLoop i f
          z -> throwError $ GenericRunTimeError "nEval bad convertSetEnv" (fromNExpr z)
-}
  {-
        (NAdd a b) -> process <$> recur a <*> recur b where
          process (NNum na) (NNum nb) = NNum (na + nb)
          process ea eb = error ("nEval nadd error " ++ show ea ++ " +++ " ++ show eb)
        (NMult a b) -> process <$> recur a <*> recur b where
          process (NNum na) (NNum nb) = NNum (na * nb)
          process ea eb = error ("nEval nmult error " ++ show ea ++ " +++ " ++ show eb)
-}
        -- hacks for add/mult
        (NAdd a b) -> process <$> envModRecur a <*> envModRecur b where
          envModRecur = recur -- eval (NPair NZero $ NPair NZero env)
          process (NNum na) (NNum nb) = NNum (na + nb)
          process ea eb = error ("nEval nadd error " ++ show ea ++ " +++ " ++ show eb)
  {-
        (NMult a b) -> process <$> eval (NPair NZero env) a <*> eval (NPair NZero env) b where
          process (NNum na) (NNum nb) = NNum (na * nb)
          process ea eb = error ("nEval nmult error " ++ show ea ++ " +++ " ++ show eb)
-}
        (NMult a b) -> ((,) <$> recur a <*> recur b) >>= process where
          envModRecur = eval (NPair NZero env)
          process (NNum na, NNum nb) = pure $ NNum (na * nb)
          process (NNum na, (NChurchAppOne cbn f)) = recur cbn >>= \y -> case y of
            (NNum nb) -> trace ("doing the thing " ++ show na ++ " " ++ show nb ++ " " ++ show env) pure $ NChurchAppOne (NNum (na * nb)) f
            z -> error ("nEval nmult error nchurchappone not pair " ++ show z)
          process z = error ("nEval nmult error not nums or nchurchappone " ++ show z)
        (NPow a b) -> process <$> recur a <*> recur b where
          process (NNum na) (NNum nb) = NNum (na ^ nb)
          process ea eb = error ("nEval npow error " ++ show ea ++ " +++ " ++ show eb)
        (NITE i t e) -> process <$> recur i <*> recur t <*> recur e where
          process NZero _ ne = ne
          process _ nt _ = nt
        (NApp c i) -> do
          nc <- recur c
          ni <- recur i
          let appl (NPair c e) i = eval (NPair i e) c
              appl y z = error ("nEval napp appl no pair " ++ show y ++ " --- " ++ show z)
          case nc of
            p@(NPair _ _) -> appl p ni -- eval (NPair ni ce) cc
            (NChurchAppOne cn f) -> do
              nn <- recur cn
              nf <- recur f
              case nn of
                (NNum nat) -> iterate (>>= appl nf) (pure ni) !! fromIntegral nat
                z -> error ("neval napp churchappone - no num - " ++ show cn)
            z -> error ("nEval napp error - non pair c - " ++ show z)
  {-
        (NChurchAppTwo c i) -> do
          nc <- recur c
          ni <- recur i
          case nc of
            (NChurchAppOne n f) -> do
              nn <- recur n
              nf <- recur f
              case nn of
                (NNum nat) ->
                  let appl (NPair c e) i = eval (NPair i e) c
                      appl z i = error ("nEval church stuff - appl - " ++ show z ++ " <-- " ++ show i)
                  in iterate (>>= appl nf) (pure ni) !! (fromIntegral nat)
                z -> error ("nEval napp - no num - " ++ show z)
            z -> error ("nEval napp - appone - " ++ show z)
-}
        -- NChurchApp, NNum
        z -> pure z
  in case Map.lookup (FragIndex 0) m of
    (Just (f,_)) -> eval NZero f
    _ -> throwError $ GenericRunTimeError "nEval: no root frag" Zero

iEval :: MonadError RunTimeError m => (IExpr -> IExpr -> m IExpr) -> IExpr -> IExpr -> m IExpr
iEval f env g = let f' = f env in case g of
  Zero -> pure Zero
  Pair a b -> Pair <$> f' a <*> f' b
  Env -> pure env
  Abort x -> f' x >>= \nx -> if nx == Zero then pure Zero else throwError $ AbortRunTime nx
  SetEnv x -> (f' x >>=) $ \nx -> case nx of
    Pair c nenv -> f nenv c
    bx -> throwError $ SetEnvError bx -- This should never actually occur, because it should be caught by typecheck
  Defer x -> pure x
  Gate x -> f' x >>= \g -> case g of
    Zero -> pure $ PLeft Env
    _ -> pure $ PRight Env
  PLeft g -> f' g >>= \g -> case g of
    (Pair a _) -> pure a
    _ -> pure Zero
  PRight g -> f' g >>= \g -> case g of
    (Pair _ x) -> pure x
    _ -> pure Zero
  Trace g -> f' g >>= \g -> pure $ trace (show g) g

toChurch :: Int -> IExpr
toChurch x =
  let inner 0 = PLeft Env
      inner x = app (PLeft $ PRight Env) (inner (x - 1))
  in lam (lam (inner x))

rOptimize :: RExpr -> RExpr
rOptimize =
  let modR (RSetEnv (RPair (RGate i) (RPair e t))) = RITE i t e
      modR x = x
  in endoMap modR

simpleEval :: IExpr -> IO IExpr
simpleEval x = runExceptT (fix iEval Zero x) >>= \r -> case r of
  Left e -> fail (show e)
  Right i -> pure i

fasterEval :: IExpr -> IO IExpr
fasterEval =
  let frEval x = runExceptT (fix rEval RZero x) >>= \r -> case r of
        Left e -> fail (show e)
        Right i -> pure i
  in fmap fromRExpr . frEval . rOptimize . toRExpr

fastInterpretEval :: IExpr -> IO IExpr
fastInterpretEval e = do
  let traceShow x = if debug then trace ("toNExpr\n" ++ showNExprs x) x else x
  result <- runExceptT $ fromNExpr <$> (nEval . traceShow $ toNExpr e)
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

optimizedEval :: IExpr -> IO IExpr
optimizedEval = simpleEval -- fastInterpretEval -- TODO fix

pureEval :: IExpr -> Either RunTimeError IExpr
pureEval g = runIdentity . runExceptT $ fix iEval Zero g

pureREval :: IExpr -> Either RunTimeError IExpr
pureREval = fmap fromRExpr . runIdentity . runExceptT . fix rEval RZero . rOptimize . toRExpr

showROptimized :: IExpr -> IO ()
showROptimized = putStrLn . show . rOptimize . toRExpr

pureEvalWithError :: IExpr -> Either RunTimeError IExpr
pureEvalWithError = fix iEval Zero

showPass :: (Show a, MonadIO m) => m a -> m a
showPass a = a >>= (liftIO . print) >> a

tEval :: IExpr -> IO IExpr
tEval x = runExceptT (fix (\f e g -> showPass $ iEval f e g) Zero x) >>= \r -> case r of
  Left e -> fail (show e)
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
