module SIL where

import Data.Char

-- if classes were categories, this would be an EndoFunctor?
class EndoMapper a where
  endoMap :: (a -> a) -> a -> a

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- {,}
  | Var                      -- identifier
  | App !IExpr !IExpr        --
  | Check !IExpr !IExpr      -- :
  | Gate !IExpr
  | PLeft !IExpr             -- left
  | PRight !IExpr            -- right
  | Trace !IExpr             -- trace
  | Closure !IExpr !IExpr
  deriving (Eq, Show, Ord)

instance EndoMapper IExpr where
  endoMap f Zero = f Zero
  endoMap f (Pair a b) = f $ Pair (endoMap f a) (endoMap f b)
  endoMap f Var = f Var
  endoMap f (App c i) = f $ App (endoMap f c) (endoMap f i)
  endoMap f (Check c t) = f $ Check (endoMap f c) (endoMap f t)
  endoMap f (Gate g) = f $ Gate (endoMap f g)
  endoMap f (PLeft x) = f $ PLeft (endoMap f x)
  endoMap f (PRight x) = f $ PRight (endoMap f x)
  endoMap f (Trace x) = f $ Trace (endoMap f x)
  endoMap f (Closure c i) = f $ Closure (endoMap f c) (endoMap f i)

lam :: IExpr -> IExpr
lam x = Closure x Zero

ite :: IExpr -> IExpr -> IExpr -> IExpr
ite i t e = App (Gate i) (Pair e t)

varN :: Int -> IExpr
varN n = PLeft (iterate PRight Var !! n)

-- hack to support old style type annotations
makeTypeCheckTest_ :: IExpr -> IExpr
makeTypeCheckTest_ Zero = Var
makeTypeCheckTest_ (Pair a b) = Closure (App (makeTypeCheckTest_ b) iapp) Zero where
  iapp = case a of
    Zero -> Zero
    x -> makeTypeCheckTest_ x
makeTypeCheckTest_ x = error $ concat ["maketct: ", show x]

makeTypeCheckTest :: IExpr -> IExpr
makeTypeCheckTest Zero = Closure (PLeft (Pair (Pair Zero Zero) (App (Gate Var) Zero))) Zero
makeTypeCheckTest x =
  Closure (PLeft (Pair (Pair Zero Zero) (App (makeTypeCheckTest_ x) Var))) Zero

anno :: IExpr -> IExpr -> IExpr
anno g tc = Check g $ makeTypeCheckTest tc

data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord)

newtype PrettyDataType = PrettyDataType DataType

showInternal at@(ArrType _ _) = concat ["(", show $ PrettyDataType at, ")"]
showInternal t = show . PrettyDataType $ t

instance Show PrettyDataType where
  show (PrettyDataType dt) = case dt of
    ZeroType -> "D"
    (ArrType a b) -> concat [showInternal a, " -> ", showInternal b]
    (PairType a b) ->
      concat ["{", show $ PrettyDataType a, ",", show $ PrettyDataType b, "}"]

packType :: DataType -> IExpr
packType ZeroType = Zero
packType (ArrType a b) = Pair (packType a) (packType b)

unpackType :: IExpr -> Maybe DataType
unpackType Zero = pure ZeroType
unpackType (Pair a b) = ArrType <$> unpackType a <*> unpackType b
unpackType _ = Nothing

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
