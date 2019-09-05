module PrettyPrint where

import SIL
import Naturals
import Data.Map (Map)

import qualified Data.Map as Map

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showPExpr :: Int -> Int -> Expr -> String
showPExpr _ _ Zero = "Z"
showPExpr _ _ Env = "E"
showPExpr l i (Pair a b) =
  concat ["P\n", indent i, showPExpr l (i + 1) a, "\n", indent i, showPExpr l (i + 1) b]
showPExpr l i (Abort x) = concat ["A ", showPExpr l i x]
showPExpr l i (Gate x) = concat ["G ", showPExpr l i x]
showPExpr l i (Trace x) = concat ["T ", showPExpr l i x]
showPExpr l i (Defer x) = concat ["D ", showPExpr l i x]
showPExpr l i (PLeft x) = concat ["L ", showPExpr l i x]
showPExpr l i (PRight x) = concat ["R ", showPExpr l i x]
showPExpr l i (SetEnv x) = concat ["S ", showPExpr l i x]

showPIE = showPExpr 80 1

showTPExpr :: Map Int PartialType -> Int -> Int -> Expr -> String
showTPExpr typeMap l i expr =
  let recur = showTPExpr typeMap l i
      indented x = concat [indent i, showTPExpr typeMap l (i + 1) x]
  in case expr of
    Zero -> "Z"
    Env -> "E"
    (Pair a b) -> concat ["P\n", indented a, "\n", indented b]
    Abort x -> concat ["A ", recur x]
    Gate x -> concat ["G ", recur x]
    Trace x -> concat ["T ", recur x]

showNExpr :: Map FragIndex NResult -> Int -> Int -> NExpr -> String
showNExpr nMap l i expr =
  let recur = showNExpr nMap l i
      showTwo c a b =
        concat [c, "\n", indent i, showNExpr nMap l (i + 1) a, "\n", indent i, showNExpr nMap l (i + 1) b]
  in case expr of
  NZero -> "Z"
  NEnv -> "E"
  (NPair a b) -> showTwo "P" a b
  (NAbort x) -> concat ["A ", recur x]
  (NGate x) -> concat ["G ", recur x]
  (NTrace x) -> concat ["T ", recur x]
  (NDefer ind) -> case Map.lookup ind nMap of
    (Just n) -> concat ["D ", recur n]
    _ -> "NDefer error: no function found for " ++ show ind
  (NLeft x) -> concat ["L ", recur x]
  (NRight x) -> concat ["R ", recur x]
  (NSetEnv x) -> concat ["S ", recur x]
  (NAdd a b) -> showTwo "+" a b
  (NMult a b) -> showTwo "X" a b
  (NPow a b) -> showTwo "^" a b
  (NITE f t e) -> concat ["I\n", indent i, showNExpr nMap l (i + 1) f
                         , "\n", indent i, showNExpr nMap l (i + 1) t
                         , "\n", indent i, showNExpr nMap l (i + 1) e]
  (NApp c i) -> showTwo "$" c i
  (NNum n) -> show n --concat ["()"]
  (NToChurch c i) -> showTwo "<" c i
  (NOldDefer x) -> concat ["% ", recur x]
  (NTwiddle x) -> concat ["W ", recur x]

showNIE (NExprs m) = case Map.lookup (FragIndex 0) m of
  Just f -> showNExpr m 80 1 f
  _ -> "error: no root nexpr"

showFragInds inds = let showInd (FragIndex i) = i in show (map showInd inds)

showOneNExpr :: Int -> Int -> NExpr -> String
showOneNExpr l i expr =
  let recur = showOneNExpr l i
      showTwo c a b =
        concat [c, "\n", indent i, showOneNExpr l (i + 1) a, "\n", indent i, showOneNExpr l (i + 1) b]
  in case expr of
      NZero -> "Z"
      NEnv -> "E"
      (NPair a b) -> showTwo "P" a b
      (NAbort x) -> concat ["A ", recur x]
      (NGate x) -> concat ["G ", recur x]
      (NTrace x) -> concat ["T ", recur x]
      (NDefer (FragIndex ind)) -> concat ["[", show ind, "]"]
      (NLeft x) -> concat ["L ", recur x]
      (NRight x) -> concat ["R ", recur x]
      (NSetEnv x) -> concat ["S ", recur x]
      (NAdd a b) -> showTwo "+" a b
      (NMult a b) -> showTwo "X" a b
      (NPow a b) -> showTwo "^" a b
      (NITE f n e) -> concat ["I\n", indent i, showOneNExpr l (i + 1) f
                            , "\n", indent i, showOneNExpr l (i + 1) n
                            , "\n", indent i, showOneNExpr l (i + 1) e]
      (NApp c i) -> showTwo "$" c i
      (NNum n) -> show n --concat ["()"]
      (NToChurch c i) -> showTwo "<" c i
      (NOldDefer x) -> concat ["% ", recur x]
      (NTwiddle x) -> concat ["W ", recur x]
      NToNum -> "["

showNExprs :: NExprs -> String
showNExprs (NExprs m) = concatMap
  (\((FragIndex k),(v)) -> concat [show k, " ", showOneNExpr 80 2 v, "\n"])
  $ Map.toList m
