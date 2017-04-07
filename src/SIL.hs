{-# LANGUAGE DeriveFunctor #-}
module SIL where

import Control.Monad.Fix
import Data.Char
import Data.Map (Map)
import Data.Functor.Identity
import Debug.Trace
import qualified Data.Map as Map

  {-
data TExpr
  = TZero
  | TPair !TExpr !TExpr
  | TVar !TExpr
  | TApp !TExpr !TExpr
  | TLam !TExpr
  deriving (Eq, Show, Ord)
-}

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- {,}
  | Var !IExpr               -- identifier
  | App !IExpr !IExpr        --
  | Anno !IExpr !IExpr       -- :
  | ITE !IExpr !IExpr !IExpr -- if a then b else c
  | PLeft !IExpr             -- left
  | PRight !IExpr            -- right
  | Trace !IExpr             -- trace
  | Lam !IExpr
  | Closure !IExpr !IExpr
  deriving (Eq, Show, Ord)

{-
data CExpr
  = Lam !CExpr
  | CI !IExpr
  | Closure !CExpr !CExpr -- (Closure function environment)
  deriving (Eq, Show, Ord)
-}

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
inferType env (Anno g Zero) = if checkType env g Zero then Just Zero else Nothing
inferType env (Anno c t) = case pureEval (Anno t Zero) of
  (Closure _ _) -> Nothing
  g -> if checkType env c g then Just g else Nothing
inferType env (ITE i t e) =
  let tt = inferType env t in if tt == inferType env e then tt else Nothing
inferType env (PLeft p) = inferType env p
inferType env (PRight p) = inferType env p
inferType env (Trace p) = inferType env p
inferType _ _ = Nothing

checkType :: [IExpr] -> IExpr -> IExpr -> Bool
checkType env (Lam c) (Pair l r) = checkType (l : env) c r
checkType env (App g i) t = case inferType env i of
  Just x -> checkType env g (Pair x t)
  Nothing -> inferType env (App g i) == Just t
checkType env x t = inferType env x == Just t

lookupEnv :: IExpr -> Int -> Maybe IExpr
lookupEnv (Closure i _) 0 = Just i
lookupEnv (Closure _ c) n = lookupEnv c (n - 1)
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
  Var v -> case lookupEnv env $ g2i v of
    Nothing -> error $ "variable not found " ++ show v
    Just var -> pure var
  Anno c t -> f' c -- TODO typecheck
  App g cexp -> do --- given t, type {{a,t},{a,t}}
    ng <- f' g
    i <- f' cexp
    apply f ng i
  ITE c t e -> f' c >>= \g -> case g of
    Zero -> f' e
    _ -> f' t
  PLeft g -> f' g >>= \g -> case g of
    (Pair a _) -> pure a
    --x -> error $ "left on " ++ show x
    _ -> pure Zero
  PRight g -> f' g >>= \g -> case g of
    (Pair _ x) -> pure x
    _ -> pure Zero
  Trace g -> f' g >>= \g -> pure $ trace (show g) g
  Lam c -> pure $ Closure c env

{-
apply :: Monad m => ([Result] -> IExpr -> m Result) -> Result -> Result -> m Result
-}
apply _ (Closure (Lam c) env) v = pure $ Closure c (Closure v env)
apply f (Closure g env) v = f (Closure v env) g
apply _ g _ = error $ "not a closure " ++ show g

{-
cEval :: Monad m => ([Result] -> IExpr -> m Result) -> [Result] -> CExpr -> m Result
-}
{-
cEval _ env (Lam c) = pure $ Closure c env
cEval f env (CI g) = f env g
-}

toChurch :: Int -> IExpr
toChurch x =
  let inner 0 = Var Zero
      inner x = App (Var $ i2g 1) (inner (x - 1))
  in Lam (Lam (inner x))

simpleEval :: IExpr -> IO IExpr
simpleEval = fix iEval Zero

pureEval :: IExpr -> IExpr
pureEval g = runIdentity $ fix iEval Zero g

showPass :: Show a => IO a -> IO a
showPass a = a >>= print >> a

tEval :: IExpr -> IO IExpr
tEval = fix (\f e g -> showPass $ iEval f e g) Zero

typedEval :: IExpr -> (IExpr -> IO ()) -> IO ()
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
    tEval iexpr >>= (print . PrettyIExpr)

printType :: IExpr -> IO ()
printType iexpr = case inferType [] iexpr of
  Nothing -> putStrLn "type failure"
  Just t -> print t

fullEval i = typedEval i print

prettyEval i = typedEval i (print . PrettyIExpr)

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case inferType [] iexpr of
  Nothing -> putStrLn "Failed typecheck"
  Just t ->
    let mainLoop s = do
          result <- simpleEval $ App iexpr s
          case result of
            Zero -> putStrLn "aborted"
            (Pair disp newState) -> do
              putStrLn . g2s $ disp
              case newState of
                Zero -> putStrLn "done"
                _ -> do
                  inp <- s2g <$> getLine
                  mainLoop $ Pair inp newState
    in mainLoop Zero
