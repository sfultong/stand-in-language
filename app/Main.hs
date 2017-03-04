module Main where

import Data.Char
import qualified Data.Map as Map
import SIL
import SIL.Parser
import qualified System.IO.Strict as Strict

just_abort = Anno (Lam (CI Zero)) (Pair Zero Zero)

message_then_abort = Anno (Lam (CI (ITE (Var Zero) Zero (Pair (s2g "Test message") Zero)))) (Pair Zero Zero)

{- TODO implement listEquality in Prelude
quit_to_exit =
  let check_input = ITE (App (App list_equality (CI . PLeft $ Var Zero)) (CI $ s2g "quit"))
                    Zero
                    (Pair (s2g "type quit to exit") (i2g 1))
  in Anno (Lam (CI check_input)) (Pair Zero Zero)
-}

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
  --unitTests
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
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> fmap (show . PrettyResult) (simpleEval g) >>= \r2 -> if r2 == r
        then pure ()
        else putStrLn $ concat [s, " result ", r2]
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
    runMain s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> evalLoop g
    displayType s = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right g -> printType g
    showHeader (s, Left x) = concat [s, " untyped"]
    showHeader (s, Right x) = concat [s, ": ", show $ inferType [] x]
    showTypeError (s, Right g) = case inferType [] g of
      Nothing -> putStrLn $ concat [s, " has bad type signature"]
      _ -> pure ()
    showTypeError _ = pure ()

  mapM_ showTypeError $ Map.toList prelude
  Strict.readFile "tictactoe.sil" >>= runMain
  --evalLoop just_abort
  -- evalLoop message_then_abort
  --evalLoop quit_to_exit

