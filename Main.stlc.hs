module Main where

import Control.Monad.Fix
import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

data Type
  = Data
  | Arr !Type !Type
  deriving (Eq, Show, Ord)

data IExpr
  = Zero
  | Pair !IExpr !IExpr
  | Var !IExpr
  | App !IExpr !CExpr
  | Anno !CExpr !Type
  | IfZ !IExpr
  | ITE !IExpr !IExpr !IExpr
  | PLeft !IExpr
  | Flip !IExpr
  deriving (Eq, Show, Ord)

data CExpr
  = Lam !CExpr
  | CI !IExpr
  deriving (Eq, Show, Ord)

data Result
  = RData !IExpr
  | Closure ![Result] !CExpr
  deriving (Eq, Show, Ord)

newtype PrettyIExpr = PrettyIExpr IExpr

instance Show PrettyIExpr where
  show (PrettyIExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["(", show a, ", ", show b, ")"]
    x -> show x

newtype PrettyResult = PrettyResult Result

instance Show PrettyResult where
  show (PrettyResult r) = case r of
    RData iexpr -> show $ PrettyIExpr iexpr
    (Closure env cexpr) -> concat [show (map PrettyResult env), " expression ", show cexpr]

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

lookupEnv :: [a] -> Int -> Maybe a
lookupEnv env ind = if ind < length env then Just (env !! ind) else Nothing

inferType :: [Type] -> IExpr -> Maybe Type
inferType _ Zero = Just Data
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
inferType env (ITE i t e) =
  let tt = inferType env t in if tt == inferType env e then tt else Nothing
inferType env (IfZ p) = inferType env p
inferType env (PLeft p) = inferType env p
inferType env (Flip p) = inferType env p

checkType :: [Type] -> CExpr -> Type -> Bool
checkType env (Lam c) (Arr l r) = checkType (l : env) c r
checkType env (CI e) t =
  -- trace (concat [show e, " env ", show env, " expected ", show t, " inferred ", show (inferType env e)])
  Just t == inferType env e
checkType _ _ _ = False

iEval :: Monad m => ([Result] -> IExpr -> m Result)
  -> [Result] -> IExpr -> m Result
iEval f env g = let f' = f env in case g of
  Zero -> pure $ RData Zero
  Pair a b -> do
    (RData na) <- f' a
    (RData nb) <- f' b
    pure . RData $ Pair na nb
  Var v -> case lookupEnv env $ g2i v of
    Nothing -> error $ "variable not found " ++ show v
    Just var -> pure var
  Anno c t -> cEval f env c -- TODO typecheck
  App g cexp -> do
    ng <- f' g
    i <- cEval f env cexp
    apply f ng i
  IfZ g -> f' g >>= \g -> case g of
    (RData (Pair Zero a)) -> pure $ RData a
    _  -> pure $ RData Zero
  ITE c t e -> f' c >>= \g -> case g of
    (RData Zero) -> f' e
    _ -> f' t
  PLeft g -> f' g >>= \g -> case g of
    (RData (Pair a _)) -> pure $ RData a
    --x -> error $ "left on " ++ show x
    x -> pure $ RData Zero
  Flip g -> f' g >>= \g -> case g of
    (RData (Pair a b)) -> pure . RData $ Pair b a
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

fullEval i = typedEval i print

prettyEval i = typedEval i (print . PrettyResult)

evalLoop :: IExpr -> IO ()
evalLoop iexpr = case inferType [] iexpr of
  Nothing -> putStrLn "Failed typecheck"
  Just t ->
    let mainLoop s = do
          result <- simpleEval $ App iexpr s
          case result of
            RData Zero -> putStrLn "aborted"
            RData (Pair disp newState) -> do
              putStrLn . g2s $ disp
              case newState of
                Zero -> putStrLn "done"
                _ -> do
                  inp <- s2g <$> getLine
                  mainLoop . CI $ Pair inp newState
    in mainLoop (CI Zero)

just_abort = Anno (Lam (CI Zero)) (Arr Data Data)


zero_equals_one =
  let descend = Lam (Lam (CI (IfZ (Pair
                                   (IfZ (Pair (Var Zero) (i2g 1)))
                                   (App (Var (i2g 1)) (CI (PLeft (Var Zero))))
                    ))))
      church_type = Arr (Arr Data Data) (Arr Data Data)
  in App (App (Anno descend church_type)
          (Lam (CI (IfZ (Pair (Var Zero) (i2g 1)) ))  )
         )
         (CI Zero)

one_equals_one =
  let descend = Lam (Lam (CI (IfZ (Pair
                                   (IfZ (Pair (Var Zero) (i2g 1)))
                                   (App (Var (i2g 1)) (CI (PLeft (Var Zero))))
                    ))))
      church_type = Arr (Arr Data Data) (Arr Data Data)
  in App (App (Anno descend church_type)
          (Lam (CI (IfZ (Pair (Var Zero) (i2g 1)) ))  )
         )
         (CI $ i2g 1)
two_equals_one =
  let descend = Lam (Lam (CI (IfZ (Pair
                                   (IfZ (Pair (Var Zero) (i2g 1)))
                                   (App (Var (i2g 1)) (CI (PLeft (Var Zero))))
                    ))))
      church_type = Arr (Arr Data Data) (Arr Data Data)
  in App (App (Anno descend church_type)
          (Lam (CI (IfZ (Pair (Var Zero) (i2g 1)) ))  )
         )
         (CI $ i2g 2)
-- (limit (n desc)) x
one_equals_two =
  let descend = Lam (CI (IfZ (Pair
                                   (IfZ (Pair (Var Zero) (i2g 1)))
                                   (PLeft (Var Zero))
                    )))
      limit = Lam (CI (IfZ (Pair
                    (App
                     (App (Anno (toChurch 2) church_type) descend)
                     (CI . Var $ Zero)
                    )
                    (i2g 1)
                  )))
      church_type = Arr (Arr Data Data) (Arr Data Data)
      equality_type = Arr church_type (Arr Data Data)
  in App (Anno limit (Arr Data Data)) (CI $ i2g 2)

-- isTwo :: Data -> Data
--three_equals_two =
--  let descend x = IfZ (Pair (IfZ (Pair )) (PLeft x)) 

three_succ = App (App (Anno (toChurch 3) (Arr (Arr Data Data) (Arr Data Data)))
                  (Lam (CI (Pair (Var Zero) Zero))))
             (CI Zero)

church_type = Arr (Arr Data Data) (Arr Data Data)

c2d = Anno (Lam (CI (App (App (Var Zero) (Lam (CI (Pair (Var Zero) Zero)))) (CI Zero))))
  (Arr church_type Data)

h2c i =
  let layer recurf i churchf churchbase =
        if i > 0
        then churchf $ recurf (i - 1) churchf churchbase
        -- App v1 (App (App (App v3 (PLeft v2)) v1) v0)
        else churchbase
      stopf i churchf churchbase = churchbase
  in \cf cb -> layer (layer (layer (layer stopf))) i cf cb

test_h2c0 = h2c 0 (\n -> Pair n Zero) Zero
test_h2c1 = h2c 1 (\n -> Pair n Zero) Zero
test_h2c2 = h2c 2 (\n -> Pair n Zero) Zero

-- layer recurf i churchf churchbase
-- layer :: (Data -> baseType) -> Data -> (baseType -> baseType) -> baseType
--           -> baseType
-- converts plain data type number (0-255) to church numeral
d2c baseType =
  let layer = Lam (Lam (Lam (Lam (CI (ITE
                             (Var $ i2g 2)
                             (App (Var $ i2g 1)
                              (CI (App (App (App (Var $ i2g 3)
                                   (CI . PLeft . Var $ i2g 2))
                                   (CI . Var $ i2g 1))
                                   (CI . Var $ Zero)
                                  )))
                             (Var Zero)
                            )))))
      base = Lam (Lam (Lam (CI (Var Zero))))
      outer_type = Arr Data (Arr (Arr baseType baseType) (Arr baseType baseType))
      inner 0 = Var Zero
      inner x = App (Var $ i2g 1) (CI $ inner (x - 1))
      nested = Lam (Lam (CI $ inner 255))
      nested_type = Arr (Arr outer_type outer_type) (Arr outer_type outer_type)
      fixf = App (App (Anno nested nested_type) layer) base
  in Anno (Lam (CI (App fixf (CI $ Var Zero)))) outer_type

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = Anno (Lam (CI (ITE (Var Zero) (ITE (PLeft (Var Zero)) Zero (i2g 1)) Zero))) (Arr Data Data)

d_to_equality = Anno (Lam (Lam (CI (ITE (Var $ i2g 1)
                                          (App d_equals_one (CI (App (App (App (d2c Data) (CI . PLeft . Var $ i2g 1)) (Lam . CI . PLeft $ Var Zero)) (CI $ Var Zero))))
                                          (ITE (Var Zero) Zero (i2g 1))
                                         )))) (Arr Data (Arr Data Data))

plus_ x y =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      plus_app = App (App (Var $ i2g 3) (CI . Var $ i2g 1)) (CI $ App (App (Var $ i2g 2) (CI . Var $ i2g 1)) (CI . Var $ Zero))
      church_type = Arr (Arr Data Data) (Arr Data Data)
      plus_type = Arr church_type (Arr church_type church_type)
      plus = Lam (Lam (Lam (Lam $ CI plus_app)))
  in App (App (Anno plus plus_type) x) y

test_plus0 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Data) (CI Zero)))))
test_plus1 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Data) (CI $ i2g 1)))))
test_plus254 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Data) (CI $ i2g 254)))))
test_plus255 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Data) (CI $ i2g 255)))))
test_plus256 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Data) (CI $ i2g 256)))))

-- m f (n f x)
-- App (App m f) (App (App n f) x)
-- App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var Zero))
three_plus_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      plus_app = App (App (Var $ i2g 3) (CI . Var $ i2g 1)) (CI $ App (App (Var $ i2g 2) (CI . Var $ i2g 1)) (CI . Var $ Zero))
      church_type = Arr (Arr Data Data) (Arr Data Data)
      plus_type = Arr church_type (Arr church_type church_type)
      plus = Lam (Lam (Lam (Lam $ CI plus_app)))
  in App c2d (CI (App (App (Anno plus plus_type) (toChurch 3)) (toChurch 2)))

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
  prettyEval $ App (App d_to_equality (CI Zero)) (CI Zero)
  prettyEval $ App (App d_to_equality (CI Zero)) (CI $ i2g 1)
  prettyEval $ App (App d_to_equality (CI $ i2g 1)) (CI Zero)
  prettyEval $ App (App d_to_equality (CI $ i2g 1)) (CI $ i2g 1)
  prettyEval $ App (App d_to_equality (CI $ i2g 1)) (CI $ i2g 2)
  prettyEval $ App (App d_to_equality (CI $ i2g 2)) (CI $ i2g 1)
  prettyEval $ App (App d_to_equality (CI $ i2g 2)) (CI $ i2g 2)
  prettyEval $ App (App d_to_equality (CI $ i2g 2)) (CI $ i2g 3)
  {-
  prettyEval three_succ
  prettyEval three_plus_two
  prettyEval three_times_two
  prettyEval three_pow_two
  -}
  {-
  prettyEval zero_equals_one
  prettyEval one_equals_one
  prettyEval two_equals_one
  -}
  --evalLoop just_abort

