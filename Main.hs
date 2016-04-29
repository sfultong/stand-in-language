module Main where

data BuiltinType = Nat | Pair BuiltinType BuiltinType

data Restriction = Restriction { check :: CompAtom -> CompAtom } | NoRestriction

data Metadata = Metadata
                    { time :: CompAtom
                    , space :: CompAtom
                    , builtin :: BuiltinType
                    }

data Operation
  = Zero
--  | Succ CompAtom
  | Succ Operation
--  | TypeCheck CompAtom
  | Eq Operation Operation

data CompAtom = CompAtom
                { meta :: Metadata
                , restrictions :: Restriction
                , operation :: Operation
                }

{--
typeCheck :: BuiltinType -> CompAtom -> CompAtom
typeCheck t (CompAtom (Metadata _ _ t2) _ _) =
  CompAtom
  (Metadata one one Nat)
  NoRestriction
--}

zero :: CompAtom
zero = CompAtom
  undefined --(Metadata zero zero Nat)
  NoRestriction
  Zero

succ' :: CompAtom -> CompAtom
succ' prev@(CompAtom meta restrictions operation) = case operation of
  Zero ->
    let oneComp = CompAtom undefined NoRestriction (Succ Zero)
    in CompAtom
       (Metadata oneComp oneComp Nat)
       undefined --TODO
       (Succ Zero)
  _ -> CompAtom
    (Metadata (succ' prev) (succ' prev) Nat)
    undefined --TODO
    (Succ operation)

one :: CompAtom
one = succ' zero

fromInt :: Int -> CompAtom
fromInt 0 = zero
fromInt n = succ' (fromInt (n - 1))

toInt :: CompAtom -> Int
toInt (CompAtom _ _ Zero) = 0
toInt (CompAtom _ _ (Succ n)) = 1 + toInt (CompAtom undefined undefined n)
toInt _ = undefined

evaluate :: CompAtom -> String
evaluate a@(CompAtom _ _ Zero) = show . toInt $ a
evaluate a@(CompAtom _ _ (Succ n)) = show . toInt $ a
evaluate _ = "error"

main = do
  putStrLn $ evaluate zero
  putStrLn $ evaluate one
  putStrLn $ evaluate (fromInt 11)
