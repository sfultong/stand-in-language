module Main where

import Control.Applicative (liftA2)
import Data.Char
import SIL
import SIL.Parser
import System.Exit
import qualified System.IO.Strict as Strict

three_succ = App (App (Anno (toChurch 3) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (Lam (CI (Pair (Var Zero) Zero))))
             (CI Zero)

church_type = Pair (Pair Zero Zero) (Pair Zero Zero)

c2d = Anno (Lam (CI (App (App (Var Zero) (Lam (CI (Pair (Var Zero) Zero)))) (CI Zero))))
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
  let layer = Lam (Lam (Lam (CI
                            (ITE (Var Zero)
                            (Pair
                             (App (Var $ i2g 1) (CI . PLeft $ Var Zero))
                             (App (App (Var $ i2g 2) (CI . Var $ i2g 1))
                              (CI . PRight $ Var Zero)))
                            Zero
                            ))))
      layerType = Pair (Pair Zero Zero) (Pair Zero Zero)
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
      base = Lam (Lam (CI Zero))
  in App (App (Anno (toChurch 255) fixType) layer) base

foldr_ =
  let layer = Lam (Lam (Lam (Lam (CI
                                 (ITE (Var $ i2g 0)
                                 (App (App (App (Var $ i2g 3) (CI . Var $ i2g 2))

                                       (CI (App (App (Var $ i2g 2) (CI . PLeft . Var $ i2g 0))
                                            (CI . Var $ i2g 1))))
                                  (CI . PRight . Var $ i2g 0))
                                 (Var $ i2g 1)
                                 )
                                 ))))
      layerType = Pair (Pair Zero (Pair Zero Zero)) (Pair Zero (Pair Zero Zero))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
      base = Lam (Lam (Lam (CI Zero))) -- var 0?
  in App (App (Anno (toChurch 255) fixType) layer) base

zipWith_ =
  let layer = Lam (Lam (Lam (Lam (CI
                                  (ITE (Var $ i2g 1)
                                   (ITE (Var $ i2g 0)
                                    (Pair
                                     (App (App (Var $ i2g 2) (CI . PLeft . Var $ i2g 1))
                                      (CI . PLeft . Var $ i2g 0))
                                     (App (App (App (Var $ i2g 3) (CI . Var $ i2g 2))
                                           (CI . PRight . Var $ i2g 1))
                                      (CI . PRight . Var $ i2g 0))
                                    )
                                    Zero)
                                   Zero)
                                 ))))
      base = Lam (Lam (Lam (CI Zero)))
      layerType = Pair (Pair Zero (Pair Zero Zero)) (Pair Zero (Pair Zero Zero))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (Anno (toChurch 255) fixType) layer) base

-- layer recurf i churchf churchbase
-- layer :: (Zero -> baseType) -> Zero -> (baseType -> baseType) -> baseType
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
      layerType = Pair Zero (Pair (Pair baseType baseType) (Pair baseType baseType))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (Anno (toChurch 255) fixType) layer) base

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = Anno (Lam (CI (ITE (Var Zero) (ITE (PLeft (Var Zero)) Zero (i2g 1)) Zero))) (Pair Zero Zero)

d_to_equality = Anno (Lam (Lam (CI (ITE (Var $ i2g 1)
                                          (App d_equals_one (CI (App (App (App (d2c Zero) (CI . PLeft . Var $ i2g 1)) (Lam . CI . PLeft $ Var Zero)) (CI $ Var Zero))))
                                          (ITE (Var Zero) Zero (i2g 1))
                                         )))) (Pair Zero (Pair Zero Zero))

list_equality =
  let pairs_equal = App (App (App zipWith_ (CI d_to_equality)) (CI $ Var Zero)) (CI . Var $ i2g 1)
      length_equal = App (App d_to_equality (CI (App list_length (CI . Var $ i2g 1))))
                     (CI (App list_length (CI $ Var Zero)))
      and_ = Lam (Lam (CI (ITE (Var $ i2g 1) (Var Zero) Zero)))
      folded = App (App (App foldr_ and_) (CI $ i2g 1)) (CI $ Pair length_equal pairs_equal)
  in Anno (Lam (Lam (CI folded))) (Pair Zero (Pair Zero Zero))

list_length = Anno (Lam (CI (App (App (App foldr_ (Lam (Lam (CI $ Pair (Var Zero) Zero))))
                                  (CI Zero))
  (CI . Var $ Zero)))) (Pair Zero Zero)

plus_ x y =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      plus_app = App (App (Var $ i2g 3) (CI . Var $ i2g 1)) (CI $ App (App (Var $ i2g 2) (CI . Var $ i2g 1)) (CI . Var $ Zero))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = Lam (Lam (Lam (Lam $ CI plus_app)))
  in App (App (Anno plus plus_type) x) y

d_plus = Anno (Lam (Lam (CI (App c2d (CI (plus_
                                   (CI (App (d2c Zero) (CI . Var $ i2g 1)))
                                   (CI (App (d2c Zero) (CI $ Var Zero)))
                                   )))))) (Pair Zero (Pair Zero Zero))

test_plus0 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Zero) (CI Zero)))))
test_plus1 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Zero) (CI $ i2g 1)))))
test_plus254 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Zero) (CI $ i2g 254)))))
test_plus255 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Zero) (CI $ i2g 255)))))
test_plus256 = App c2d (CI (plus_
                         (toChurch 3)
                         (CI (App (d2c Zero) (CI $ i2g 256)))))

-- m f (n f x)
-- App (App m f) (App (App n f) x)
-- App (App (Var $ i2g 3) (Var $ i2g 1)) (App (App (Var $ i2g 2) (Var $ i2g 1)) (Var Zero))
three_plus_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      plus_app = App (App (Var $ i2g 3) (CI . Var $ i2g 1)) (CI $ App (App (Var $ i2g 2) (CI . Var $ i2g 1)) (CI . Var $ Zero))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = Lam (Lam (Lam (Lam $ CI plus_app)))
  in App c2d (CI (App (App (Anno plus plus_type) (toChurch 3)) (toChurch 2)))

-- (m (n f)) x
-- App (App m (App n f)) x
three_times_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      times_app = App (App (Var $ i2g 3) (CI $ App (Var $ i2g 2) (CI . Var $ i2g 1))) (CI . Var $ i2g 0)
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      times_type = Pair church_type (Pair church_type church_type)
      times = Lam (Lam (Lam (Lam $ CI times_app)))
  in App (App (App (App (Anno times times_type) (toChurch 3)) (toChurch 2)) succ) (CI Zero)

-- m n
-- App (App (App (m n)) f) x
three_pow_two =
  let succ = Lam (CI (Pair (Var Zero) Zero))
      pow_app = App (App (App (Var $ i2g 3) (CI . Var $ i2g 2)) (CI . Var $ i2g 1)) (CI . Var $ i2g 0)
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      pow_type = Pair (Pair church_type church_type) (Pair church_type church_type)
      pow = Lam (Lam (Lam (Lam $ CI pow_app)))
  in App (App (App (App (Anno pow pow_type) (toChurch 2)) (toChurch 3)) succ) (CI Zero)

unitTest :: String -> String -> IExpr -> IO Bool
unitTest name expected iexpr = case inferType [] iexpr of
  Nothing -> (putStrLn $ name ++ " failed typecheck") >> pure False
  Just _ -> do
    result <- (show . PrettyResult) <$> simpleEval iexpr
    if result == expected
      then pure True
      else (putStrLn $ concat [name, ": expected ", expected, " result ", result]) >>
           pure False

unitTests unitTest2 = foldl (liftA2 (&&)) (pure True)
  [ unitTest "three" "3" three_succ
  , unitTest "church 3+2" "5" three_plus_two
  , unitTest "3*2" "6" three_times_two
  , unitTest "3^2" "9" three_pow_two
  , unitTest "data 3+5" "8" $ App (App d_plus (CI $ i2g 3)) (CI $ i2g 5)
  , unitTest "foldr" "13" $ App (App (App foldr_ (CI d_plus)) (CI $ i2g 1)) (CI $ ints2g [2,4,6])
  , unitTest "listlength0" "0" $ App list_length (CI $ Zero)
  , unitTest "listlength3" "3" $ App list_length (CI $ ints2g [1,2,3])
  , unitTest "zipwith" "{{4,1},{{5,1},{{6,2},0}}}"
    $ App (App (App zipWith_ (Lam (Lam (CI (Pair (Var $ i2g 1) (Var $ i2g 0))))))
           (CI $ ints2g [4,5,6]))
    (CI $ ints2g [1,1,2,3])
  , unitTest "listequal1" "1" $ App (App list_equality (CI $ s2g "hey")) (CI $ s2g "hey")
  , unitTest "listequal0" "0" $ App (App list_equality (CI $ s2g "hey")) (CI $ s2g "he")
  , unitTest "listequal00" "0" $ App (App list_equality (CI $ s2g "hey")) (CI $ s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
  , unitTest "map" "{2,{3,5}}" $ App (App map_ (Lam (CI (Pair (Var Zero) Zero))))
    (CI $ ints2g [1,2,3])
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
      Right g -> fmap (show . PrettyResult) (simpleEval g) >>= \r2 -> if r2 == r
        then pure True
        else (putStrLn $ concat [s, " result ", r2]) >> pure False
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
  result <- unitTests unitTest2
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
