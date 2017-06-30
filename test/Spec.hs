module Main where

import Control.Applicative (liftA2)
import Debug.Trace
import Data.Char
import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker
import System.Exit
import qualified System.IO.Strict as Strict

three_succ = App (App (Anno (toChurch 3) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (lam (Pair (Var Zero) Zero)))
             Zero

one_succ = App (App (Anno (toChurch 1) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (lam (Pair (Var Zero) Zero)))
             Zero

two_succ = App (App (Anno (toChurch 2) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (lam (Pair (Var Zero) Zero)))
             Zero

church_type = Pair (Pair Zero Zero) (Pair Zero Zero)

c2d = Anno (lam (App (App (Var Zero) (lam (Pair (Var Zero) Zero))) Zero))
  (Pair church_type Zero)

h2c i =
  let layer recurf i churchf churchbase =
        if i > 0
        then churchf $ recurf (i - 1) churchf churchbase
        -- App v1 (App (App (App v3 (PLeft v2)) v1) v0)
        else churchbase
      stopf i churchf churchbase = churchbase
  in \cf cb -> layer (layer (layer (layer stopf))) i cf cb


{-
h_zipWith a b f =
  let layer recurf zipf a b =
        if a > 0
        then if b > 0
             then Pair (zipf (PLeft a) (PLeft b)) (recurf zipf (PRight a) (PRight b))
             else Zero
        else Zero
      stopf _ _ _ = Zero
  in layer (layer (layer (layer stopf))) a b f

foldr_h =
  let layer recurf f accum l =
        if not $ nil l
        then recurf f (f (PLeft l) accum) (PRight l)
        else accum
-}

map_ =
  -- layer recurf f l = Pair (f (PLeft l)) (recurf f (PRight l))
  let layer = lam (lam (lam
                            (ite (Var Zero)
                            (Pair
                             (App (Var $ i2g 1) (PLeft $ Var Zero))
                             (App (App (Var $ i2g 2) (Var $ i2g 1))
                              (PRight $ Var Zero)))
                            Zero
                            )))
      layerType = Pair (Pair Zero Zero) (Pair Zero Zero)
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
      base = lam (lam Zero)
  in App (App (Anno (toChurch 255) fixType) layer) base

foldr_ =
  let layer = lam (lam (lam (lam
                                 (ite (Var $ i2g 0)
                                 (App (App (App (Var $ i2g 3) (Var $ i2g 2))

                                       (App (App (Var $ i2g 2) (PLeft . Var $ i2g 0))
                                            (Var $ i2g 1)))
                                  (PRight . Var $ i2g 0))
                                 (Var $ i2g 1)
                                 )
                                 )))
      layerType = Pair (Pair Zero (Pair Zero Zero)) (Pair Zero (Pair Zero Zero))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
      base = lam (lam (lam Zero)) -- var 0?
  in App (App (Anno (toChurch 255) fixType) layer) base

zipWith_ =
  let layer = lam (lam (lam (lam
                                  (ite (Var $ i2g 1)
                                   (ite (Var $ i2g 0)
                                    (Pair
                                     (App (App (Var $ i2g 2) (PLeft . Var $ i2g 1))
                                      (PLeft . Var $ i2g 0))
                                     (App (App (App (Var $ i2g 3) (Var $ i2g 2))
                                           (PRight . Var $ i2g 1))
                                      (PRight . Var $ i2g 0))
                                    )
                                    Zero)
                                   Zero)
                                 )))
      base = lam (lam (lam Zero))
      layerType = Pair (Pair Zero (Pair Zero Zero)) (Pair Zero (Pair Zero Zero))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (Anno (toChurch 255) fixType) layer) base

-- layer recurf i churchf churchbase
-- layer :: (Zero -> baseType) -> Zero -> (baseType -> baseType) -> baseType
--           -> baseType
-- converts plain data type number (0-255) to church numeral
d2c baseType =
  let layer = lam (lam (lam (lam (ite
                             (Var $ i2g 2)
                             (App (Var $ i2g 1)
                              (App (App (App (Var $ i2g 3)
                                   (PLeft . Var $ i2g 2))
                                   (Var $ i2g 1))
                                   (Var $ Zero)
                                  ))
                             (Var Zero)
                            ))))
      base = lam (lam (lam (Var Zero)))
      layerType = Pair Zero (Pair (Pair baseType baseType) (Pair baseType baseType))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (Anno (toChurch 255) fixType) layer) base

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = Anno (lam (ite (Var Zero) (ite (PLeft (Var Zero)) Zero (i2g 1)) Zero)) (Pair Zero Zero)

d_to_equality = Anno (lam (lam (ite (Var $ i2g 1)
                                          (App d_equals_one (App (App (App (d2c Zero) (PLeft . Var $ i2g 1)) (lam . PLeft $ Var Zero)) (Var Zero)))
                                          (ite (Var Zero) Zero (i2g 1))
                                         ))) (Pair Zero (Pair Zero Zero))

list_equality =
  let pairs_equal = App (App (App zipWith_ d_to_equality) (Var Zero)) (Var $ i2g 1)
      length_equal = App (App d_to_equality (App list_length (Var $ i2g 1)))
                     (App list_length (Var Zero))
      and_ = lam (lam (ite (Var $ i2g 1) (Var Zero) Zero))
      folded = App (App (App foldr_ and_) (i2g 1)) (Pair length_equal pairs_equal)
  in Anno (lam (lam folded)) (Pair Zero (Pair Zero Zero))

list_length = Anno (lam (App (App (App foldr_ (lam (lam (Pair (Var Zero) Zero))))
                                  Zero)
  (Var $ Zero))) (Pair Zero Zero)

plus_ x y =
  let succ = lam (Pair (Var Zero) Zero)
      plus_app = App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var Zero))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = lam (lam (lam (lam plus_app)))
  in App (App (Anno plus plus_type) x) y

d_plus = Anno (lam (lam (App c2d (plus_
                                   (App (d2c Zero) (Var $ i2g 1))
                                   (App (d2c Zero) (Var Zero))
                                   )))) (Pair Zero (Pair Zero Zero))

test_plus0 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) Zero))
test_plus1 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 1)))
test_plus254 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 254)))
test_plus255 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 255)))
test_plus256 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 256)))

one_plus_one =
  let succ = lam (Pair (Var Zero) Zero)
      plus_app = App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var $ Zero))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = lam (lam (lam (lam plus_app)))
  in App c2d (App (App (Anno plus plus_type) (toChurch 1)) (toChurch 1))

-- m f (n f x)
-- App (App m f) (App (App n f) x)
-- App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var Zero))
three_plus_two =
  let succ = lam (Pair (Var Zero) Zero)
      plus_app = App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var $ Zero))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = lam (lam (lam (lam plus_app)))
  in App c2d (App (App (Anno plus plus_type) (toChurch 3)) (toChurch 2))

-- (m (n f)) x
-- App (App m (App n f)) x
three_times_two =
  let succ = lam (Pair (Var Zero) Zero)
      times_app = App (App (Var $ i2g 3) (App (Var $ i2g 2) (Var $ i2g 1))) (Var $ i2g 0)
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      times_type = Pair church_type (Pair church_type church_type)
      times = lam (lam (lam (lam times_app)))
  in App (App (App (App (Anno times times_type) (toChurch 3)) (toChurch 2)) succ) Zero

-- m n
-- App (App (App (m n)) f) x
three_pow_two =
  let succ = lam (Pair (Var Zero) Zero)
      pow_app = App (App (App (Var $ i2g 3) (Var $ i2g 2)) (Var $ i2g 1)) (Var $ i2g 0)
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      pow_type = Pair (Pair church_type church_type) (Pair church_type church_type)
      pow = lam (lam (lam (lam pow_app)))
  in App (App (App (App (Anno pow pow_type) (toChurch 2)) (toChurch 3)) succ) Zero

unitTest :: String -> String -> IExpr -> IO Bool
unitTest name expected iexpr = if fullCheck iexpr ZeroType
  then do
    result <- (show . PrettyIExpr) <$> simpleEval iexpr
    if result == expected
      then pure True
      else (putStrLn $ concat [name, ": expected ", expected, " result ", result]) >>
           pure False
  else putStrLn ( concat [name, " failed typecheck"]) >> pure False

churchType = (ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType))

unitTests_ unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  [ unitTestType "main = $1"
    (ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType)) True
  , unitTestType "main : {0,0} = \\x -> {x,0}" (ArrType ZeroType ZeroType) True
  --, unitTestType "main : {0,0} = \\x -> {x,0}" ZeroType False
  --, unitTest "church 1+1" "2" one_plus_one
  ]

unitTests unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  [ unitTestType "main : {0,0} = \\x -> {x,0}" (ArrType ZeroType ZeroType) True
  , unitTestType "main : {0,0} = \\x -> {x,0}" ZeroType False
  , unitTestType "main = succ 0" ZeroType True
  , unitTestType "main = succ 0" (ArrType ZeroType ZeroType) False
  , unitTestType "main = or 0" (ArrType ZeroType ZeroType) True
  , unitTestType "main = or 0" ZeroType False
  , unitTestType "main = or succ" (ArrType ZeroType ZeroType) False
  , unitTestType "main = 0 succ" ZeroType False
  , unitTestType "main = 0 0" ZeroType False
  , unitTestType "main : {{0,0},0} = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
    (ArrType (ArrType ZeroType ZeroType) ZeroType) False
  , unitTestType "main : 0 = (\\f -> f 0) (\\g -> {g,0})" ZeroType True
  , unitTestType "main : {{{0,0},{0,0}},{{{0,0},{0,0}},{{0,0},{0,0}}}} = \\m n f x -> m f (n f x)" (ArrType churchType (ArrType churchType churchType)) True
  , unitTest "three" "3" three_succ
  , unitTest "church 3+2" "5" three_plus_two
  , unitTest "3*2" "6" three_times_two
  , unitTest "3^2" "9" three_pow_two
  , unitTest "data 3+5" "8" $ App (App d_plus (i2g 3)) (i2g 5)
  , unitTest "foldr" "13" $ App (App (App foldr_ d_plus) (i2g 1)) (ints2g [2,4,6])
  , unitTest "listlength0" "0" $ App list_length Zero
  , unitTest "listlength3" "3" $ App list_length (ints2g [1,2,3])
  , unitTest "zipwith" "{{4,1},{{5,1},{{6,2},0}}}"
    $ App (App (App zipWith_ (lam (lam (Pair (Var $ i2g 1) (Var $ i2g 0)))))
           (ints2g [4,5,6]))
    (ints2g [1,1,2,3])
  , unitTest "listequal1" "1" $ App (App list_equality (s2g "hey")) (s2g "hey")
  , unitTest "listequal0" "0" $ App (App list_equality (s2g "hey")) (s2g "he")
  , unitTest "listequal00" "0" $ App (App list_equality (s2g "hey")) (s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
  , unitTest "map" "{2,{3,5}}" $ App (App map_ (lam (Pair (Var Zero) Zero)))
    (ints2g [1,2,3])
  , unitTest2 "main = 0" "0"
  , unitTest2 fiveApp "5"
  , unitTest2 "main = plus $3 $2 succ 0" "5"
  , unitTest2 "main = times $3 $2 succ 0" "6"
  , unitTest2 "main = pow $3 $2 succ 0" "8"
  , unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
  , unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
  , unitTest2 "main = dEqual 0 0" "1"
  , unitTest2 "main = dEqual 1 0" "0"
  , unitTest2 "main = dEqual 0 1" "0"
  , unitTest2 "main = dEqual 1 1" "1"
  , unitTest2 "main = dEqual 2 1" "0"
  , unitTest2 "main = dEqual 1 2" "0"
  , unitTest2 "main = dEqual 2 2" "1"
  , unitTest2 "main = listLength []" "0"
  , unitTest2 "main = listLength [1,2,3]" "3"
  , unitTest2 "main = listEqual \"hey\" \"hey\"" "1"
  , unitTest2 "main = listEqual \"hey\" \"he\"" "0"
  , unitTest2 "main = listEqual \"hey\" \"hel\"" "0"
  , unitTest2 "main = listPlus [1,2] [3,4]" "{1,{2,{3,5}}}"
  , unitTest2 "main = concat [\"a\",\"b\",\"c\"]" "{97,{98,100}}"
  , unitTest2 nestedNamedFunctionsIssue "2"
  , unitTest2 "main = take $0 [1,2,3]" "0"
  , unitTest2 "main = take $1 [1,2,3]" "2"
  , unitTest2 "main = take $5 [1,2,3]" "{1,{2,4}}"
  , unitTest2 "main = c2d (minus $4 $3)" "1"
  , unitTest2 "main = c2d (minus $4 $4)" "0"
  , unitTest2 "main = dMinus 4 3" "1"
  , unitTest2 "main = dMinus 4 4" "0"
  ]

testExpr = concat
  [ "main = let a = 0\n"
  , "           b = 1\n"
  , "       in {a,1}\n"
  ]

fiveApp = concat
  [ "main = let fiveApp : {{0,0},{0,0}} = $5\n"
  , "       in fiveApp (\\x -> {x,0}) 0"
  ]

nestedNamedFunctionsIssue = concat
  [ "main = let bindTest : {0,0} = \\tlb -> let f1 : {{0,0},0} = \\f -> f tlb\n"
  , "                                           f2 : {{0,0},0} = \\f -> succ (f1 f)\n"
  , "                                       in f2 succ\n"
  , "       in bindTest 0"
  ]

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    unitTestP s g = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right pg -> if pg == g
        then pure ()
        else putStrLn $ concat ["parsed oddly ", s, " ", show pg, " compared to ", show g]
    unitTest2 s r = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> fmap (show . PrettyIExpr) (simpleEval g) >>= \r2 -> if r2 == r
        then pure True
        else (putStrLn $ concat [s, " result ", r2]) >> pure False
    unitTestType s t b = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> if fullCheck g t == b
        then pure True
        else (putStrLn $ concat [s, " failed typecheck"])
             >> pure False
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
  result <- unitTests unitTest2 unitTestType
  exitWith $ if result then ExitSuccess else ExitFailure 1

  {-
  print $ parseSIL "main = 0\n"
  print $ parseSIL "main = 1\n"
  print $ parseSIL "main = {0,0}\n"
  print $ parseSIL "main = \"HI\"\n"
  print $ parseSIL "main : {0,0} = \\x -> {0,x}\n"
  print $ parseSIL "main : {0,0} = \\x y-> {x,y}\n"
  print $ parseSIL "main : {{0,0},{{0,{0,0}}, 0}} = \\f g -> (g 0) (f 0)\n"
  print $ parseSIL testExpr
  -}
