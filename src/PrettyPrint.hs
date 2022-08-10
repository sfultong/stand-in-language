{-# LANGUAGE LambdaCase #-}

module PrettyPrint where

import           Data.Map (Map)
import           Naturals
import           Telomare hiding (indent)

import qualified Data.Map as Map

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showPIExpr :: Int -> Int -> IExpr -> String
showPIExpr _ _ Zero = "Z"
showPIExpr _ _ Env = "E"
showPIExpr l i (Pair a b) =
  concat ["P\n", indent i, showPIExpr l (i + 1) a, "\n", indent i, showPIExpr l (i + 1) b]
showPIExpr l i (Gate a b) = -- "G"
  "G\n" <> indent i <> showPIExpr l (i + 1) a <> "\n" <> indent i <> showPIExpr l (i + 1) b
showPIExpr _ _ Trace = "T"
showPIExpr l i (Defer x) = concat ["D ", showPIExpr l i x]
showPIExpr l i (PLeft x) = concat ["L ", showPIExpr l i x]
showPIExpr l i (PRight x) = concat ["R ", showPIExpr l i x]
showPIExpr l i (SetEnv x) = concat ["S ", showPIExpr l i x]

showPIE = showPIExpr 80 1

showTPIExpr :: Map Int PartialType -> Int -> Int -> IExpr -> String
showTPIExpr typeMap l i expr =
  let recur = showTPIExpr typeMap l i
      indented x = concat [indent i, showTPIExpr typeMap l (i + 1) x]
  in case expr of
    Zero       -> "Z"
    Env        -> "E"
    (Pair a b) -> concat ["P\n", indented a, "\n", indented b]
    Gate a b   -> "G\n" <> indented a <> "\n" <> indented b
    Trace      -> "T"

showNExpr :: Map FragIndex NResult -> Int -> Int -> NExpr -> String
showNExpr nMap l i expr =
  let recur = showNExpr nMap l i
      showTwo c a b =
        concat [c, "\n", indent i, showNExpr nMap l (i + 1) a, "\n", indent i, showNExpr nMap l (i + 1) b]
  in case expr of
  NZero -> "Z"
  NEnv -> "E"
  (NPair a b) -> showTwo "P" a b
  NGate a b -> showTwo "G" a b
  NTrace -> "T"
  (NDefer ind) -> case Map.lookup ind nMap of
    (Just n) -> concat ["D ", recur n]
    _        -> "NDefer error: no function found for " ++ show ind
  (NLeft x) -> concat ["L ", recur x]
  (NRight x) -> concat ["R ", recur x]
  (NSetEnv x) -> concat ["S ", recur x]
  (NAdd a b) -> showTwo "+" a b
  (NMult a b) -> showTwo "X" a b
  (NPow a b) -> showTwo "^" a b
  (NApp c i) -> showTwo "$" c i
  (NNum n) -> show n --concat ["()"]
  (NToChurch c i) -> showTwo "<" c i
  (NOldDefer x) -> concat ["% ", recur x]
  (NTwiddle x) -> concat ["W ", recur x]

showNIE (NExprs m) = case Map.lookup (FragIndex 0) m of
  Just f -> showNExpr m 80 1 f
  _      -> "error: no root nexpr"

showFragInds inds = let showInd (FragIndex i) = i in show (map showInd inds)

showOneNExpr :: Int -> Int -> NExpr -> String
showOneNExpr l i expr =
  let recur = showOneNExpr l i
      showTwo c a b =
        concat [c, "\n", indent i, showOneNExpr l (i + 1) a, "\n", indent i, showOneNExpr l (i + 1) b]
  in case expr of
      NZero                    -> "Z"
      NEnv                     -> "E"
      (NPair a b)              -> showTwo "P" a b
      NGate a b                -> showTwo "G" a b
      NTrace                   -> "T"
      (NDefer (FragIndex ind)) -> concat ["[", show ind, "]"]
      (NLeft x)                -> concat ["L ", recur x]
      (NRight x)               -> concat ["R ", recur x]
      (NSetEnv x)              -> concat ["S ", recur x]
      (NAdd a b)               -> showTwo "+" a b
      (NMult a b)              -> showTwo "X" a b
      (NPow a b)               -> showTwo "^" a b
      (NApp c i)               -> showTwo "$" c i
      (NNum n)                 -> show n --concat ["()"]
      (NToChurch c i)          -> showTwo "<" c i
      (NOldDefer x)            -> concat ["% ", recur x]
      (NTwiddle x)             -> concat ["W ", recur x]
      NToNum                   -> "["

showNExprs :: NExprs -> String
showNExprs (NExprs m) = concatMap
  (\((FragIndex k),(v)) -> concat [show k, " ", showOneNExpr 80 2 v, "\n"])
  $ Map.toList m

-- termMap, function->type lookup, root frag type
data TypeDebugInfo = TypeDebugInfo Term3 (FragIndex -> PartialType) PartialType

showTypeDebugInfo :: TypeDebugInfo -> String
showTypeDebugInfo (TypeDebugInfo (Term3 termMap) lookup rootType) =
  let showFrag (FragIndex i) ty frag = show i <> ": " <> show (PrettyPartialType ty) <> "\n" <> showExpr 80 2 frag
      showExpr l i =
        let recur = showExpr l i
            showTwo c a b =
              concat [c, "\n", indent i, showExpr l (i + 1) a, "\n", indent i, showExpr l (i + 1) b]
            showThree x a b c =
              concat [x, "\n", indent i, showExpr l (i + 1) a, "\n", indent i, showExpr l (i + 1) b, "\n", indent i, showExpr l (i + 1) c]
        in \case
          ZeroFrag                  -> "Z"
          PairFrag a b              -> showTwo "P" a b
          EnvFrag                   -> "E"
          SetEnvFrag x              -> "S " <> recur x
          DeferFrag (FragIndex ind) -> "[" <> show ind <> "]"
          AbortFrag                 -> "A"
          GateFrag l r              -> showTwo "G" l r
          LeftFrag x                -> "L " <> recur x
          RightFrag x               -> "R " <> recur x
          TraceFrag                 -> "T"
          AuxFrag (RecursionTest (FragExprUR x)) -> "?" <> recur x
          AuxFrag (NestedSetEnvs _)              -> "%"
  in showFrag (FragIndex 0) rootType (unFragExprUR $ rootFrag termMap) <> "\n"
     <> concatMap (\(k, v) -> showFrag k (lookup k) v <> "\n") (tail . Map.toAscList . Map.map unFragExprUR $ termMap)
