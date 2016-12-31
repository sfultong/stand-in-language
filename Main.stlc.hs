module Main where

import Control.Monad.Fix
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

data Type
  = Data
  | Arr Type Type
  deriving (Eq, Show, Ord)

data IExpr
  = Zero
  | Pair IExpr IExpr
  | Var IExpr
  | App IExpr CExpr
  | Anno CExpr Type
  | IfZ IExpr
  | PLeft IExpr
  | Flip IExpr
  deriving (Eq, Show, Ord)

data CExpr
  = Lam CExpr
  | CI IExpr
  deriving (Eq, Show, Ord)

data Result
  = RZero
  | RPair Result Result
  | Closure [Result] CExpr
  deriving (Eq, Show, Ord)

newtype PrettyResult = PrettyResult Result

instance Show PrettyResult where
  show (PrettyResult r) = case r of
    RZero -> "0"
    p@(RPair a b) -> if isNumR p
      then show $ r2i p
      else concat ["(", show a, ", ", show b, ")"]
    (Closure env cexpr) -> concat [show (map PrettyResult env), " expression ", show cexpr]

g2i :: IExpr -> Int
g2i Zero = 0
g2i (Pair a b) = 1 + (g2i a) + (g2i b)
g2i x = error $ "g2i " ++ (show x)

i2g :: Int -> IExpr
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero

-- convention is numbers are right-nested pairs with zero on left
isNum :: IExpr -> Bool
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False

isNumR :: Result -> Bool
isNumR RZero = True
isNumR (RPair n RZero) = isNumR n
isNumR _ = False

r2i :: Result -> Int
r2i RZero = 0
r2i (RPair a b) = 1 + r2i a + r2i b
r2i _ = error "closure in converting result to number"

lookupEnv :: [a] -> Int -> Maybe a
lookupEnv env ind = if ind < length env then Just (env !! ind) else Nothing

inferType :: [Type] -> IExpr -> Maybe Type
inferType env Zero = Just Data
inferType env (Pair a b) = do
  ta <- inferType env a
  tb <- inferType env b
  if ta == Data && tb == Data
    then pure Data
    else Nothing -- can't have functions in pairs
inferType env (Var v) = lookupEnv env $ g2i v
inferType env (App g i) = case inferType env g of
  Just (Arr l r) -> if checkType env i l then Just r else Nothing
  _ -> Nothing
inferType env (Anno c t) = if checkType env c t then Just t else Nothing

checkType :: [Type] -> CExpr -> Type -> Bool
checkType env (Lam c) (Arr l r) = checkType (l : env) c r
checkType env (CI e) t =
  -- trace (concat [show e, " env ", show env, " expected ", show t, " inferred ", show (inferType env e)])
  Just t == inferType env e
checkType _ _ _ = False

iEval :: Monad m => ([Result] -> IExpr -> m Result)
  -> [Result] -> IExpr -> m Result
iEval f env g = let f' = f env in case g of
  Zero -> pure RZero
  Pair a b -> do
    na <- f' a
    nb <- f' b
    pure $ RPair na nb
  Var v -> case lookupEnv env $ g2i v of
    Nothing -> error $ "variable not found " ++ show v
    Just var -> pure var
  Anno c t -> cEval f env c -- TODO typecheck
  App g cexp -> do
    ng <- f' g
    i <- cEval f env cexp
    apply f ng i
  IfZ g -> f' g >>= \g -> case g of
    (RPair RZero a) -> pure a
    _  -> pure RZero
  PLeft g -> f' g >>= \g -> case g of
    (RPair a _) -> pure a
    x -> error $ "left on " ++ show x
  Flip g -> f' g >>= \g -> case g of
    (RPair a b) -> pure $ RPair b a
    x -> error $ "flip on " ++ show x

apply :: Monad m => ([Result] -> IExpr -> m Result) -> Result -> Result -> m Result
apply f (Closure env (CI g)) v = f (v : env) g
apply _ (Closure env (Lam c)) v = pure $ Closure (v:env) c
apply _ g _ = error $ "not a closure" ++ show g

cEval :: Monad m => ([Result] -> IExpr -> m Result) -> [Result] -> CExpr -> m Result
cEval f env (Lam c) = pure $ Closure env c
cEval f env (CI g) = f env g

toChurch :: Int -> CExpr
toChurch x =
  let inner 0 = Var Zero
      inner x = App (Var $ i2g 1) (CI $ inner (x - 1))
  in Lam (Lam (CI $ inner x))

testG = App (Anno (Lam (CI (Pair Zero (Var Zero)))) (Arr Data Data)) (CI Zero)

simpleEval :: IExpr -> IO Result
simpleEval = fix iEval []

showPass :: Show a => IO a -> IO a
showPass a = a >>= print >> a

tEval :: IExpr -> IO Result
tEval = fix (\f e g -> showPass $ iEval f e g) []

typedEval :: IExpr -> (Result -> IO ()) -> IO ()
typedEval iexpr prettyPrint = do
  case inferType [] iexpr of
    Nothing -> putStrLn "Failed typecheck"
    Just t -> do
      putStrLn $ "Type is: " ++ show t
      simpleEval iexpr >>= prettyPrint

fullEval i = typedEval i print

prettyEval i = typedEval i (print . PrettyResult)

three_succ = App (App (Anno (toChurch 3) (Arr (Arr Data Data) (Arr Data Data)))
                  (Lam (CI (Pair (Var Zero) Zero))))
             (CI Zero)

-- m f (n f x)
-- App (App m f) (App (App n f) x)
-- App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var Zero))
three_plus_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      plus_app = App (App (Var $ i2g 3) (CI . Var $ i2g 1)) (CI $ App (App (Var $ i2g 2) (CI . Var $ i2g 1)) (CI . Var $ Zero))
      church_type = Arr (Arr Data Data) (Arr Data Data)
      plus_type = Arr church_type (Arr church_type church_type)
      plus = Lam (Lam (Lam (Lam $ CI plus_app)))
  in App (App (App (App (Anno plus plus_type) (toChurch 3)) (toChurch 2)) succ) (CI Zero)

-- (m (n f)) x
-- App (App m (App n f)) x
three_times_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      times_app = App (App (Var $ i2g 3) (CI $ App (Var $ i2g 2) (CI . Var $ i2g 1))) (CI . Var $ i2g 0)
      church_type = Arr (Arr Data Data) (Arr Data Data)
      times_type = Arr church_type (Arr church_type church_type)
      times = Lam (Lam (Lam (Lam $ CI times_app)))
  in App (App (App (App (Anno times times_type) (toChurch 3)) (toChurch 2)) succ) (CI Zero)

-- m n
-- App (App (App (m n)) f) x
three_pow_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      pow_app = App (App (App (Var $ i2g 3) (CI . Var $ i2g 2)) (CI . Var $ i2g 1)) (CI . Var $ i2g 0)
      church_type = Arr (Arr Data Data) (Arr Data Data)
      pow_type = Arr (Arr church_type church_type) (Arr church_type church_type)
      pow = Lam (Lam (Lam (Lam $ CI pow_app)))
  in App (App (App (App (Anno pow pow_type) (toChurch 2)) (toChurch 3)) succ) (CI Zero)

main = do
  -- print . inferType [] $ Anno (toChurch 0) (Arr (Arr Data Data) (Arr Data Data))
  prettyEval three_succ
  prettyEval three_plus_two
  prettyEval three_times_two
  prettyEval three_pow_two

