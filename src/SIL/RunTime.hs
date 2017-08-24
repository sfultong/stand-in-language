module SIL.RunTime where

import Data.Functor.Identity
import Debug.Trace
import Control.Monad.Fix

import SIL
import SIL.Optimizer

-- runtime expression
data RExpr
  = RZero
  | RPair !RExpr !RExpr
  | RVar
  | RCheck !RExpr !RExpr
  | RApp !RExpr !RExpr
  | RGate !RExpr
  | RLeft !RExpr
  | RRight !RExpr
  | RTrace !RExpr
  | RClosure !RExpr !RExpr
  -- machine optimized instructions
  | RITE !RExpr !RExpr !RExpr
  | RChurch !Int !(Maybe RExpr)
  deriving (Eq, Show, Ord)

instance EndoMapper RExpr where
  endoMap f RZero = f RZero
  endoMap f (RPair a b) = f $ RPair (endoMap f a) (endoMap f b)
  endoMap f RVar = f RVar
  endoMap f (RApp c i) = f $ RApp (endoMap f c) (endoMap f i)
  endoMap f (RCheck c t) = f $ RCheck (endoMap f c) (endoMap f t)
  endoMap f (RGate x) = f . RGate $ endoMap f x
  endoMap f (RLeft x) = f . RLeft $ endoMap f x
  endoMap f (RRight x) = f . RRight $ endoMap f x
  endoMap f (RTrace x) = f . RTrace $ endoMap f x
  endoMap f (RClosure c e) = f $ RClosure (endoMap f c) (endoMap f e)
  endoMap f (RITE i t e) = f $ RITE (endoMap f i) (endoMap f t) (endoMap f e)
  endoMap f r@(RChurch _ Nothing) = f r

toRExpr :: IExpr -> RExpr
toRExpr Zero = RZero
toRExpr (Pair a b) = RPair (toRExpr a) (toRExpr b)
toRExpr Var = RVar
toRExpr (Check c t) = RCheck (toRExpr c) (toRExpr t)
toRExpr (App c i) = RApp (toRExpr c) (toRExpr i)
toRExpr (Gate x) = RGate $ toRExpr x
toRExpr (PLeft x) = RLeft $ toRExpr x
toRExpr (PRight x) = RRight $ toRExpr x
toRExpr (Trace x) = RTrace $ toRExpr x
toRExpr (Closure c e) = RClosure (toRExpr c) (toRExpr e)

fromRExpr :: RExpr -> IExpr
fromRExpr RZero = Zero
fromRExpr (RPair a b) = Pair (fromRExpr a) (fromRExpr b)
fromRExpr RVar = Var
fromRExpr (RCheck c t) = Check (fromRExpr c) (fromRExpr t)
fromRExpr (RApp c i) = App (fromRExpr c) (fromRExpr i)
fromRExpr (RGate x) = Gate $ fromRExpr x
fromRExpr (RLeft x) = PLeft $ fromRExpr x
fromRExpr (RRight x) = PRight $ fromRExpr x
fromRExpr (RTrace x) = Trace $ fromRExpr x
fromRExpr (RClosure c e) = Closure (fromRExpr c) (fromRExpr e)
fromRExpr (RITE i t e) = App (Gate $ fromRExpr i) (Pair (fromRExpr e) (fromRExpr t))
fromRExpr (RChurch i Nothing) = toChurch i

rEval f env g = let f' = f env in case g of
  RZero -> pure RZero
  (RPair a b) -> RPair <$> f' a <*> f' b
  RVar -> pure env
  RCheck c t -> do
    tcResult <- f' (RApp t c)
    case tcResult of
      RZero -> f' c
      err -> fail $ concat ["failed rrefinement check for ", show c, " -- ",  show err]
  RApp g i -> let rApply (RClosure ng eenv) v = f (RPair v eenv) ng
                  rApply (RChurch ci Nothing) v = pure $ RChurch ci (Just v)
                  rApply (RChurch ci (Just cf)) v =
                    let step 0 cv = pure cv
                        step x cv = rApply cf cv >>= step (x - 1)
                    in step ci v
                  rApply ng _ = fail $ "not a closure " ++ show ng
              in do
    ng <- f' g
    ni <- f' i
    rApply ng ni
  RGate x -> f' x >>= \g -> case g of
    RZero -> pure $ RClosure (RLeft (RLeft RVar)) RZero
    _ -> pure $ RClosure (RRight (RLeft RVar)) RZero
  RLeft g -> f' g >>= \g -> case g of
    (RPair a _) -> pure a
    _ -> pure RZero
  RRight g -> f' g >>= \g -> case g of
    (RPair _ b) -> pure b
    _ -> pure RZero
  RTrace g -> f' g >>= \g -> pure $ trace (show g) g
  RClosure c RZero -> pure $ RClosure c env
  RClosure _ e -> fail $ concat ["unexpected closure with environment ", show e]
  RITE i t e -> f' i >>= \ng -> case ng of
    RZero -> f' e
    _ -> f' t
  r@(RChurch _ _) -> pure r

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
  Check c t -> do
    tc <- f' (App t c)
    case tc of
      Zero -> f' c
      x -> fail $ concat ["failed refinement check for ", show c, " -- ", show x]
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

rOptimize :: RExpr -> RExpr
rOptimize =
  let modR (RApp (RGate i) (RPair e t)) = RITE i t e
      modR c@(RClosure (RClosure apps RZero) RZero) = let appCount = countApps 0 apps in
        if appCount > 0
        then RChurch appCount Nothing
        else c
      modR x = x
      countApps x (RLeft RVar) = x
      countApps x (RApp (RLeft (RRight RVar)) ia) = countApps (x + 1) ia
      countApps _ _ = 0
  in endoMap modR

simpleEval :: IExpr -> IO IExpr
simpleEval = fix iEval Zero

fasterEval :: IExpr -> IO IExpr
fasterEval =
  let frEval = fix rEval RZero
  in fmap fromRExpr . frEval . rOptimize . toRExpr

optimizedEval :: IExpr -> IO IExpr
optimizedEval = fasterEval --simpleEval . optimize

pureEval :: IExpr -> IExpr
pureEval g = runIdentity $ fix iEval Zero g

pureREval :: IExpr -> IExpr
pureREval = fromRExpr . runIdentity . fix rEval RZero . rOptimize . toRExpr

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

evalLoop :: (Show a, Eq a) => (DataType -> IExpr -> Maybe a) -> IExpr -> IO ()
evalLoop typeCheck iexpr = if typeCheck (ArrType ZeroType ZeroType) iexpr == Nothing
  then let mainLoop s = do
             result <- fmap fromRExpr . fix rEval RZero $ RApp optIExpr (toRExpr s)
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
           optIExpr = rOptimize $ toRExpr iexpr
       in mainLoop Zero
  else putStrLn $ concat ["main's inferred type: "
                         , show $ typeCheck (ArrType ZeroType ZeroType) iexpr]
