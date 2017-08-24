module Main where

import Data.Char
import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker (weakCheck, inferType)
import SIL.Optimizer
import qualified System.IO.Strict as Strict

just_abort = anno (lam Zero) (Pair Zero Zero)

message_then_abort = anno (lam (ite (varN 0) Zero (Pair (s2g "Test message") Zero))) (Pair Zero Zero)

{- TODO implement listEquality in Prelude
quit_to_exit =
  let check_input = ITE (App (App list_equality (CI . PLeft $ Var Zero)) (CI $ s2g "quit"))
                    Zero
                    (Pair (s2g "type quit to exit") (i2g 1))
  in anno (Lam (CI check_input)) (Pair Zero Zero)
-}

-- game section
displayBoard =
  let cc c l = Pair (i2g $ ord c) l
      ch = cc '#'
      cn = cc '\n'
      row5 = Pair (varN 2) (ch (Pair (varN 1) (ch (Pair (varN 0) Zero))))
      row4 = ch . ch . ch . ch . ch $ cn row5
      row3 = Pair (varN 5) (ch (Pair (varN 4) (ch (Pair (varN 3) row4))))
      row2 = ch . ch . ch . ch . ch $ cn row3
      row1 = Pair (varN 8) (ch (Pair (varN 7) (ch (Pair (varN 6) row2))))
      rows = lam (lam (lam (lam (lam (lam (lam (lam (lam row1))))))))
      rowsType = Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero Zero))))))))
      repRight x = foldr (.) id $ replicate x PRight
      appl 0 = App (anno rows rowsType) (PLeft $ varN 0)
      appl x = App (appl (x - 1)) (PLeft . repRight x $ varN 0)
  in anno (lam $ appl 8) (Pair Zero Zero)

main = do
  --unitTests
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    testMethod n s = case resolveBinding n <$> parseWithPrelude prelude s of
      Right (Just iexpr) -> simpleEval iexpr >>= \r -> print (PrettyIExpr r)
      x -> print x
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
    runMain s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> evalLoop weakCheck g
    showParsed s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> print . PrettyIExpr $ g
    showOptimized s = case optimize <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> print . PrettyIExpr $ g
    testTCT = print . inferType . makeTypeCheckTest
    testTCT2 t e = print . inferType $ App (makeTypeCheckTest t) e

  printBindingTypes prelude
  Strict.readFile "tictactoe.sil" >>= runMain
  --Strict.readFile "tictactoe.sil" >>= testMethod "test3"
  --evalLoop just_abort
  -- evalLoop message_then_abort
  --evalLoop quit_to_exit

