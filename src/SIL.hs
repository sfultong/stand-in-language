{-# LANGUAGE DeriveFunctor #-}
module SIL where

import Control.Monad.Fix
import Data.Char
import Data.Functor.Identity
import Debug.Trace

data IExprF c i
  = FZero
  | FPair i i
  | FVar i
  | FApp i c
  | FAnno c i
  | FITE i i i
  | FLeft i
  | FRight i
  | FTrace i
  deriving (Eq, Show, Ord, Functor)

data CExprF i c
  = FLam c
  | FCI i
  deriving (Eq, Show, Ord, Functor)

newtype IExpr' = IExpr' (IExprF CExpr' IExpr')
newtype CExpr' = CExpr' (CExprF IExpr' CExpr')

{-
foldI :: (IExpr' -> a -> a) -> (CExpr' -> a -> a) -> a -> IExpr' -> a
foldI 
-}

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- {,}
  | Var !IExpr               -- identifier
  | App !IExpr !CExpr        -- 
  | Anno !CExpr !IExpr       -- :
  | ITE !IExpr !IExpr !IExpr -- if a then b else c
  | PLeft !IExpr             -- left
  | PRight !IExpr            -- right
  | Trace !IExpr             -- trace
  deriving (Eq, Show, Ord)

data CExpr
  = Lam !CExpr
  | CI !IExpr
  | Closure !CExpr !CExpr
  deriving (Eq, Show, Ord)

{-
data Result
  = RData !IExpr
  | Closure ![Result] !CExpr
  deriving (Eq, Show, Ord)
-}

newtype PrettyIExpr = PrettyIExpr IExpr

instance Show PrettyIExpr where
  show (PrettyIExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["{", show (PrettyIExpr a), ",", show (PrettyIExpr b), "}"]
    Zero -> "0"
    x -> show x

newtype PrettyResult = PrettyResult CExpr

instance Show PrettyResult where
  show (PrettyResult r) = case r of
    CI iexpr -> show $ PrettyIExpr iexpr
    x -> show x

g2i :: IExpr -> Int
g2i Zero = 0
g2i (Pair a b) = 1 + (g2i a) + (g2i b)
g2i x = error $ "g2i " ++ (show x)

i2g :: Int -> IExpr
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero

ints2g :: [Int] -> IExpr
ints2g = foldr (\i g -> Pair (i2g i) g) Zero

g2Ints :: IExpr -> [Int]
g2Ints Zero = []
g2Ints (Pair n g) = g2i n : g2Ints g
g2Ints x = error $ "g2Ints " ++ show x

s2g :: String -> IExpr
s2g = ints2g . map ord

g2s :: IExpr -> String
g2s = map chr . g2Ints

-- convention is numbers are left-nested pairs with zero on right
isNum :: IExpr -> Bool
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False

lookupTypeEnv :: [a] -> Int -> Maybe a
lookupTypeEnv env ind = if ind < length env then Just (env !! ind) else Nothing

-- types are give by IExpr. Zero represents Data and Pair represents Arrow
inferType :: [IExpr] -> IExpr -> Maybe IExpr
inferType _ Zero = Just Zero
inferType env (Pair a b) = do
  ta <- inferType env a
  tb <- inferType env b
  if ta == Zero && tb == Zero
    then pure Zero
    else Nothing -- can't have functions in pairs
inferType env (Var v) = lookupTypeEnv env $ g2i v
inferType env (App g i) = case inferType env g of
  Just (Pair l r) -> if checkType env i l then Just r else Nothing
  _ -> Nothing
--inferType env (Anno c t) = if checkType env c t then Just t else Nothing
inferType env (Anno c t) = case pureEval t of
  (CI g) -> if checkType env c g then Just g else Nothing
  _ -> Nothing
inferType env (ITE i t e) =
  let tt = inferType env t in if tt == inferType env e then tt else Nothing
inferType env (PLeft p) = inferType env p
inferType env (PRight p) = inferType env p
inferType env (Trace p) = inferType env p

checkType :: [IExpr] -> CExpr -> IExpr -> Bool
checkType env (Lam c) (Pair l r) = checkType (l : env) c r
checkType env (CI e) t =
  -- trace (concat [show e, " env ", show env, " expected ", show t, " inferred ", show (inferType env e)])
  Just t == inferType env e
checkType _ _ _ = False

lookupEnv :: CExpr -> Int -> Maybe CExpr
lookupEnv (Closure i _) 0 = Just i
lookupEnv (Closure _ c) n = lookupEnv c (n - 1)
lookupEnv _ _ = Nothing

{-
iEval :: Monad m => ([Result] -> IExpr -> m Result)
  -> [Result] -> IExpr -> m Result
-}
iEval f env g = let f' = f env in case g of
  Zero -> pure $ CI Zero
  Pair a b -> do
    (CI na) <- f' a
    (CI nb) <- f' b
    pure . CI $ Pair na nb
  Var v -> case lookupEnv env $ g2i v of
    Nothing -> error $ "variable not found " ++ show v
    Just var -> pure var
  Anno c t -> cEval f env c -- TODO typecheck
  App g cexp -> do
    ng <- f' g
    i <- cEval f env cexp
    apply f ng i
  ITE c t e -> f' c >>= \g -> case g of
    (CI Zero) -> f' e
    _ -> f' t
  PLeft g -> f' g >>= \g -> case g of
    (CI (Pair a _)) -> pure $ CI a
    --x -> error $ "left on " ++ show x
    _ -> pure $ CI Zero
  PRight g -> f' g >>= \g -> case g of
    (CI (Pair _ x)) -> pure $ CI x
    _ -> pure $ CI Zero
  Trace g -> f' g >>= \g -> pure $ trace (show g) g

{-
apply :: Monad m => ([Result] -> IExpr -> m Result) -> Result -> Result -> m Result
-}
apply f (Closure env (CI g)) v = f (Closure v env) g
apply _ (Closure env (Lam c)) v = pure $ Closure (Closure v env) c
apply _ g _ = error $ "not a closure " ++ show g

{-
cEval :: Monad m => ([Result] -> IExpr -> m Result) -> [Result] -> CExpr -> m Result
-}
cEval _ env (Lam c) = pure $ Closure env c
cEval f env (CI g) = f env g

toChurch :: Int -> CExpr
toChurch x =
  let inner 0 = Var Zero
      inner x = App (Var $ i2g 1) (CI $ inner (x - 1))
  in Lam (Lam (CI $ inner x))

simpleEval :: IExpr -> IO CExpr
simpleEval = fix iEval (CI Zero)

pureEval :: IExpr -> CExpr
pureEval g = runIdentity $ fix iEval (CI Zero) g

showPass :: Show a => IO a -> IO a
showPass a = a >>= print >> a

tEval :: IExpr -> IO CExpr
tEval = fix (\f e g -> showPass $ iEval f e g) (CI Zero)

typedEval :: IExpr -> (CExpr -> IO ()) -> IO ()
typedEval iexpr prettyPrint = case inferType [] iexpr of
  Nothing -> putStrLn "Failed typecheck"
  Just t -> do
    putStrLn $ "Type is: " ++ show t
    simpleEval iexpr >>= prettyPrint

debugEval :: IExpr -> IO ()
debugEval iexpr = case inferType [] iexpr of
  Nothing -> putStrLn "Failed typecheck"
  Just t -> do
    putStrLn $ "Type is: " ++ show t
    tEval iexpr >>= (print . PrettyResult)

printType :: IExpr -> IO ()
printType iexpr = case inferType [] iexpr of
  Nothing -> putStrLn "type failure"
  Just t -> print t

fullEval i = typedEval i print

prettyEval i = typedEval i (print . PrettyResult)

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case inferType [] iexpr of
  Nothing -> putStrLn "Failed typecheck"
  Just t ->
    let mainLoop s = do
          result <- simpleEval $ App iexpr s
          case result of
            CI Zero -> putStrLn "aborted"
            CI (Pair disp newState) -> do
              putStrLn . g2s $ disp
              case newState of
                Zero -> putStrLn "done"
                _ -> do
                  inp <- s2g <$> getLine
                  mainLoop . CI $ Pair inp newState
    in mainLoop (CI Zero)
