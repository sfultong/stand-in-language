module PrettyPrint where

import SIL
import Naturals
import Data.Map (Map)

import qualified Data.Map as Map

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showPIExpr :: Int -> Int -> IExpr -> String
showPIExpr _ _ Zero = "Z"
showPIExpr _ _ Env = "E"
showPIExpr l i (Pair a b) =
  concat ["P\n", indent i, showPIExpr l (i + 1) a, "\n", indent i, showPIExpr l (i + 1) b]
{-
showPIExpr l i p@(Pair a b) = if length (show p) > l
  then concat ["P\n", indent i, showPIExpr l (i + 1) a, "\n", indent i, showPIExpr l (i + 1) b]
  else show p
-}
showPIExpr l i (Abort x) = concat ["A ", showPIExpr l i x]
showPIExpr l i (Gate x) = concat ["G ", showPIExpr l i x]
showPIExpr l i (Trace x) = concat ["T ", showPIExpr l i x]
showPIExpr l i (Defer x) = concat ["D ", showPIExpr l i x]
showPIExpr l i (PLeft x) = concat ["L ", showPIExpr l i x]
showPIExpr l i (PRight x) = concat ["R ", showPIExpr l i x]
showPIExpr l i (SetEnv x) = concat ["S ", showPIExpr l i x]

showPIE = showPIExpr 80 1

showNExpr :: Map FragIndex (NExpr, FragType) -> Int -> Int -> NExpr -> String
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
    (Just (n, _)) -> concat ["D ", recur n]
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
  (NChurchAppOne n f) -> showTwo "C" n f -- concat ["(C ", show n, ")", recur f]
  (NChurchAppTwo n f) -> showTwo "V" n f -- concat ["(C ", show n, ")", recur f]
  (NApp c i) -> showTwo "$" c i
  (NNum n) -> show n --concat ["()"]
  (NToChurch x) -> concat ["< ", recur x]
  (NOldDefer x) -> concat ["% ", recur x]

showNIE (NExprs m) = case Map.lookup (FragIndex 0) m of
  Just (f, _) -> showNExpr m 80 1 f
  _ -> "error: no root nexpr"

showFragInds inds = let showInd (FragIndex i) = i in show (map showInd inds)

newtype PrettyFragType = PrettyFragType FragType

instance Show PrettyFragType where
  show (PrettyFragType x) = case x of
    ZeroTypeF -> "0"
    (PairTypeF a b) -> concat ["{", show (PrettyFragType a), ",", show (PrettyFragType b), "}"]
    (ArrTypeF inds _) -> showFragInds inds -- concat ["-> [", showFragInds inds, "]"]
    ChurchTypeF -> "C"
    UnknownTypeF -> "?"
    GateTypeF -> "G"
    (PartialChurchTypeF t) -> concat ["P[", show $ PrettyFragType t, "]"]

showEnvPart :: FragType -> NExpr -> Maybe String
showEnvPart ft expr =
  let showInternal expr showF = case expr of
        (NLeft x) -> ("L " ++) <$> showInternal x (\t -> typeLeft t >>= showF)
        (NRight x) -> ("R " ++) <$> showInternal x (\t -> typeRight t >>= showF)
        NEnv -> (\it -> "E -- " ++ show (PrettyFragType it)) <$> showF ft
        _ -> Nothing
      typeLeft (PairTypeF t _) = Just t
      typeLeft _ = Nothing
      typeRight (PairTypeF _ t) = Just t
      typeRight _ = Nothing
  in showInternal expr pure

showOneNExpr :: Int -> Int -> FragType -> NExpr -> String
showOneNExpr l i t expr =
  let recur = showOneNExpr l i t
      showTwo c a b =
        concat [c, "\n", indent i, showOneNExpr l (i + 1) t a, "\n", indent i, showOneNExpr l (i + 1) t b]
  in case showEnvPart t expr of
    Just s -> s
    _ -> case expr of
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
      (NITE f n e) -> concat ["I\n", indent i, showOneNExpr l (i + 1) t f
                            , "\n", indent i, showOneNExpr l (i + 1) t n
                            , "\n", indent i, showOneNExpr l (i + 1) t e]
      (NChurchAppOne n f) -> showTwo "C" n f -- concat ["(C ", show n, ")", recur f]
      (NChurchAppTwo n f) -> showTwo "V" n f -- concat ["(C ", show n, ")", recur f]
      (NApp c i) -> showTwo "$" c i
      (NNum n) -> show n --concat ["()"]
      (NToChurch x) -> concat ["< ", recur x]
      (NOldDefer x) -> concat ["% ", recur x]
      NToNum -> "["

showNExprs :: NExprs -> String
{-
showNExprs (NExprs m) = concatMap (\((FragIndex k),(v,t)) -> concat [show k, " ", showOneNExpr 80 2 t v, "\n"])
  $ Map.toList m
-}
showNExprs (NExprs m) = concatMap
  (\((FragIndex k),(v,t)) -> concat
    [show k, " ", show (PrettyFragType t), "\n", showOneNExpr 80 2 t v, "\n"])
  $ Map.toList m
