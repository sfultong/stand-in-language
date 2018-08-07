module PrettyPrint where

import SIL

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
