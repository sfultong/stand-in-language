module Main where

import Data.Char
import SIL


just_abort = Anno (Lam (CI Zero)) (Pair Zero Zero)

message_then_abort = Anno (Lam (CI (ITE (Var Zero) Zero (Pair (s2g "Test message") Zero)))) (Pair Zero Zero)

quit_to_exit =
  let check_input = ITE (App (App list_equality (CI . PLeft $ Var Zero)) (CI $ s2g "quit"))
                    Zero
                    (Pair (s2g "type quit to exit") (i2g 1))
  in Anno (Lam (CI check_input)) (Pair Zero Zero)

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

fixl l base layer layerType  =
  let inner 0 = Var Zero
      inner x = App (Var $ i2g 1) (CI $ inner (x - 1))
      nested = Lam (Lam (CI $ inner l))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (Anno nested fixType) layer) base

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
      base = Lam (Lam (CI Zero))
  in fixl 255 base layer layerType

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
      base = Lam (Lam (Lam (CI Zero))) -- var 0?
  in fixl 255 base layer layerType

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
  in fixl 255 base layer layerType

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
  in fixl 255 base layer layerType

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

unitTests = do
  unitTest "three" "3" three_succ
  unitTest "church 3+2" "5" three_plus_two
  unitTest "3*2" "6" three_times_two
  unitTest "3^2" "9" three_pow_two
  unitTest "data 3+5" "8" $ App (App d_plus (CI $ i2g 3)) (CI $ i2g 5)
  unitTest "foldr" "13" $ App (App (App foldr_ (CI d_plus)) (CI $ i2g 1)) (CI $ ints2g [2,4,6])
  unitTest "listlength0" "Zero" $ App list_length (CI $ Zero)
  unitTest "listlength3" "3" $ App list_length (CI $ ints2g [1,2,3])
  unitTest "zipwith" "((4, 1), ((5, 1), ((6, 2), Zero)))"
    $ App (App (App zipWith_ (Lam (Lam (CI (Pair (Var $ i2g 1) (Var $ i2g 0))))))
           (CI $ ints2g [4,5,6]))
    (CI $ ints2g [1,1,2,3])
  unitTest "listequal1" "1" $ App (App list_equality (CI $ s2g "hey")) (CI $ s2g "hey")
  unitTest "listequal0" "Zero" $ App (App list_equality (CI $ s2g "hey")) (CI $ s2g "he")
  unitTest "listequal00" "Zero" $ App (App list_equality (CI $ s2g "hey")) (CI $ s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
  unitTest "map" "(2, (3, 5))" $ App (App map_ (Lam (CI (Pair (Var Zero) Zero))))
    (CI $ ints2g [1,2,3])

-- game section
displayBoard =
  let cc c l = Pair (i2g $ ord c) l
      ch = cc '#'
      cn = cc '\n'
      row5 = Pair (Var $ i2g 2) (ch (Pair (Var $ i2g 1) (ch (Pair (Var Zero) Zero))))
      row4 = ch . ch . ch . ch . ch $ cn row5
      row3 = Pair (Var $ i2g 5) (ch (Pair (Var $ i2g 4) (ch (Pair (Var $ i2g 3) row4))))
      row2 = ch . ch . ch . ch . ch $ cn row3
      row1 = Pair (Var $ i2g 8) (ch (Pair (Var $ i2g 7) (ch (Pair (Var $ i2g 6) row2))))
      rows = Lam (Lam (Lam (Lam (Lam (Lam (Lam (Lam (Lam (CI row1)))))))))
      rowsType = Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero Zero))))))))
      repRight x = foldr (.) id $ replicate x PRight
      appl 0 = App (Anno rows rowsType) (CI . PLeft $ Var Zero)
      appl x = App (appl (x - 1)) (CI . PLeft . repRight x $ Var Zero)
  in Anno (Lam . CI $ appl 8) (Pair Zero Zero)


main = do
  unitTests
  --prettyEval $ App displayBoard (CI Zero)
  --evalLoop just_abort
  evalLoop message_then_abort
  --evalLoop quit_to_exit

