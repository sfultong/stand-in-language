module Main where

import Debug.Trace


import Data.Function
import Data.Char
{--
import Data.Map (Map)
import qualified Data.Map as Map
--}

data InterpretationModel
  = InterpretationModel
    { run :: Grammar -> Grammar -> Grammar
    , time :: Grammar -> Grammar
    , space :: Grammar -> Grammar
    }

data Grammar
  = Zero
  | Hole
  | Pair Grammar Grammar
  | Dup Grammar                -- probably unnecessary (MergeL, Repeat)
  | Flip Grammar
  | PLeft Grammar
  | ITE Grammar                -- probably unnecessary (If)
  | If Grammar
  | MergeL Grammar
  | MergeBarrier Grammar
  | Repeat Grammar
  | Defer Grammar
  | ConstR Grammar
  | SingleEvaluate Grammar     -- probably evil
  | Reevaluate Grammar         -- probably evil
  | Assert Grammar
  | TimeCheck Grammar
  | SpaceCheck Grammar
  deriving (Eq,Show)

getInner :: Grammar -> Grammar
getInner (Dup a) = a
getInner (Flip a) = a
getInner (PLeft a) = a
getInner (ITE a) = a
getInner (If a) = a
getInner (MergeL a) = a
getInner (MergeBarrier a) = a
getInner (Repeat a) = a
getInner (Defer a) = a
getInner (ConstR a) = a
getInner (SingleEvaluate a) = a
getInner (Reevaluate a) = a
getInner (Assert a) = a
getInner (TimeCheck a) = a
getInner (SpaceCheck a) = a

getOuter :: Grammar -> Grammar -> Grammar
getOuter (Dup a) = Dup
getOuter (Flip a) = Flip
getOuter (PLeft a) = PLeft
getOuter (ITE a) = ITE
getOuter (If a) = If
getOuter (MergeL a) = MergeL
getOuter (MergeBarrier a) = MergeBarrier
getOuter (Repeat a) = Repeat
getOuter (Defer a) = Defer
getOuter (ConstR a) = ConstR
getOuter (SingleEvaluate a) = SingleEvaluate
getOuter (Reevaluate a) = Reevaluate
getOuter (Assert a) = Assert
getOuter (TimeCheck a) = TimeCheck
getOuter (SpaceCheck a) = SpaceCheck

onlyData :: Grammar -> Bool
onlyData Zero = True
onlyData Hole = False
onlyData (Pair a b) = onlyData a && onlyData b
onlyData x = False

-- convention is numbers are right-nested pairs with zero on left
isNum :: Grammar -> Bool
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False

fancyShow :: Grammar -> String
fancyShow Zero = "0"
fancyShow Hole = "Hole"
fancyShow p@(Pair a b) = case isNum p of
  True -> show . g2i $ p
  False -> concat ["(", fancyShow a, ", ", fancyShow b, ")"]
fancyShow x =
  let s prefix = concat [prefix, " (", fancyShow . getInner $ x, ")"]
  in case x of
    (Flip a) -> s "Flip"
    (PLeft a) -> s "PLeft"
    (ITE a) -> s "ITE"
    (If a) -> s "If"
    (MergeL a) -> s "MergeL"
    (MergeBarrier a) -> s "MergeBarrier"
    (Repeat a) -> s "Repeat"
    (Defer a) -> s "Defer"
    (ConstR a) -> s "ConstR"
    (SingleEvaluate a) -> s "SingleEvaluate"
    (Reevaluate a) -> s "Reevaluate"
    _ -> error "todo"

hasHole :: Grammar -> Bool
hasHole Zero = False
hasHole Hole = True
hasHole (Pair a b) = hasHole a || hasHole b
hasHole x = hasHole $ getInner x

haskellEval :: (Grammar -> Grammar) -> Grammar -> Grammar
--haskellEval f g = trace ("-- " ++ fancyShow g) $ case g of
haskellEval f g = case g of
  Zero -> Zero
  Hole -> Hole -- error "hole"
  Pair a b -> Pair (f a) (f b)
  SingleEvaluate a -> error "singleevaluate"--haskellEval f $ haskellEval id a
  ConstR (Pair a b) -> Pair (f a) b
  Defer (Pair g d) -> f (MergeL (Pair g (f d)))
  MergeL (Pair g i) ->
    let replaceHole (Zero, c) = (Zero, c)
        replaceHole mb@(MergeBarrier g, c) = (g, c) --mb
        replaceHole (Hole, c) = case c of
          True -> (Hole, True)
          False -> (i, True)
        replaceHole (Pair a b, c) = let (na, ca) = replaceHole (a, c)
                                        (nb, cb) = replaceHole (b, ca)
                                    in (Pair na nb, cb)
        replaceHole (x_, c) = let (nx_, nc) = replaceHole (getInner x_, c)
                            in (getOuter x_ nx_, nc)
        newG = fst $ replaceHole (g, False)
    in case hasHole newG of
      --True -> newG
      True -> f newG 
      False -> f newG
      --haskellEval f . fst $ replaceHole (g, False)
  Repeat (Pair f' n) -> let newN = f n in case isNum newN of
    True -> let replaceHole (Zero, c) = (Zero, c)
                replaceHole mb@(MergeBarrier g, c) = mb
                replaceHole (Hole, c) = case c of
                  True -> (Hole, True)
                  False -> (f', True)
                replaceHole (Pair a b, c) = let (na, ca) = replaceHole (a, c)
                                                (nb, cb) = replaceHole (b, ca)
                                            in (Pair na nb, cb)
                replaceHole (x_, c) = let (nx_, nc) = replaceHole (getInner x_, c)
                                      in (getOuter x_ nx_, nc)
                repeat Zero = Hole
                repeat (Pair n _) = fst $ replaceHole (repeat n, False)
                repeat x = error $ "repeat_inner " ++ (show x)
            in repeat newN
    False -> error $ "not num repeat inner " ++ fancyShow (newN) -- Repeat (Pair f n)
  x -> let nx = getOuter x . f . getInner $ x in case nx of
    Dup a -> Pair a a
    Flip (Pair a b) -> Pair b a
    Flip x -> Flip x -- error "flip"
    PLeft (Pair a b) -> a
    PLeft x -> PLeft x -- error "left"
    ITE (Pair Zero (Pair a b)) -> b
    ITE (Pair (Pair _ _) (Pair a b)) -> a
    ITE x -> ITE x -- error "ite"
    If (Pair (Pair _ _) _) -> Zero
    If (Pair Zero a) -> a
    If x -> If x -- error "if"
    Repeat x -> Repeat x -- error "repeat"
    --m@(MergeL (Pair g i)) -> f m
    --def@(Defer (Pair g d)) -> f def
    MergeBarrier x -> MergeBarrier x
    Reevaluate x -> error "reevaluate" --haskellEval id $ x
    x -> error $ "undefined grammar " ++ (show x)

-- MergeL ((MergeL ((Hole, 0)), ((((((Hole, 0), 0), 0), 0), 0), 0)))


ints2g :: [Int] -> Grammar
ints2g = foldr (\i g -> Pair (i2g i) g) Zero

g2Ints :: Grammar -> [Int]
g2Ints Zero = []
g2Ints (Pair n g) = g2i n : g2Ints g
g2Ints x = error $ "g2ints " ++ (show x)

s2g :: String -> Grammar
s2g = ints2g . map ord

g2s :: Grammar -> String
g2s = map chr . g2Ints

haskell :: InterpretationModel
haskell =
  let evalMerged g i = fix haskellEval (MergeL (Pair g i))
  in InterpretationModel (\g -> evalMerged g)
     undefined undefined

evalLoop :: Grammar -> IO ()
evalLoop g =
  let startState = Zero
      evaluate = run haskell g
      evalOutput (Pair m s) = do
        putStrLn $ g2s s
        putStrLn . show $ g2Ints s
        pure m
      evalOutput o = error $ "unexpected output " ++ (show o)
      evalInput m = do
        i <- getLine
        pure $ Pair m (s2g i)
      mainLoop s = do
        newS <- evalOutput s
        case newS of
          Zero -> putStrLn "done"
          x -> do
            inp <- evalInput x
            mainLoop $ evaluate inp
  in mainLoop $ evaluate startState

g2i :: Grammar -> Int
g2i Zero = 0
g2i (Pair a b) = 1 + (g2i a) + (g2i b)
g2i x = error $ "g2i " ++ (fancyShow x)

i2g :: Int -> Grammar
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero

eval :: Grammar -> Grammar -> IO ()
eval d g = putStrLn . show $ run haskell g d

evalRaw :: Grammar -> IO ()
evalRaw g = putStrLn . fancyShow $ fix haskellEval g

evalRawSingle g = putStrLn . show $ haskellEval id g

evalNum :: Grammar -> Grammar -> IO ()
evalNum d g = putStrLn . show . g2i $ run haskell g d

two = Pair (Pair Zero Zero) Zero
three = Pair (Pair (Pair Zero Zero) Zero) Zero

num2Plus = Repeat (Pair (Pair Hole Zero) Hole)

plus3 = Pair (Pair (Pair Hole Zero) Zero) Zero

times3 = Defer (Pair
                (MergeL (Pair (MergeBarrier Hole) Zero))
                (Repeat (Pair (MergeBarrier plus3) Hole))
               )

powOf3 = Defer (Pair
                (MergeL (Pair (MergeBarrier Hole) (Pair Zero Zero)))
                (Repeat (Pair (MergeBarrier times3) Hole))
               )

--danger x = SingleEvaluate (Repeat (Pair x two))

danger x = Repeat (Pair x two)

danger' x = Defer (Pair (Repeat (Pair x two)) (Repeat (Pair Hole two)))

bad = danger' (danger' (danger' (Pair Hole Zero)))

bad' = (Defer (Pair
                (danger (danger (MergeL (Pair
                                 (danger (danger (danger (Pair Zero Hole))))
                                 (danger Hole)))
                        )
                )
                (danger Hole)))

testProg = Pair Zero (s2g "hey")

testProg2 = Pair (Pair Zero Zero) (s2g "never stop")

testProg3 = Pair (Pair Zero Zero) (Pair (i2g 97) (PLeft Hole))

doubleFirst = Pair (Pair Zero Zero)
  (MergeL (Flip (Pair
                 (Repeat (Pair (Pair Hole Hole) two))
                 (MergeL (Pair Hole Zero))
               )
          ))

main = do
  evalNum Zero Hole
  evalNum Zero (Pair Zero Hole)
  evalNum two plus3
  evalNum two times3
  evalNum two powOf3
  --evalRaw (Repeat (Pair times3 two))
  --evalLoop doubleFirst
  {--
  evalRaw (Repeat (Pair
                   (Repeat (Pair Hole three))
                   two))
  evalRaw (SingleEvaluate (Repeat (Pair (Pair Hole Zero) two)))
--}
  --evalNum two' thirdPow
  --evalNum three times3
  --evalRaw (Repeat (Pair times3 (Pair (Pair Zero Zero) Zero)))
  --evalNum two exp3
  --evalNum two (Merge (Pair (Merge (Pair plus3 plus3)) plus3))
  --evalRaw (Merge (Pair plus3 plus3))
  --evalNum two (Merge (Pair plus3 plus3)) 
