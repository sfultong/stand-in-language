{-# LANGUAGE LambdaCase #-}

module Telomare.Decompiler where

import           Control.Monad       (foldM, liftM2)
import qualified Control.Monad.State as State
import           Data.List           (intercalate)
import qualified Data.Map            as Map
import           Data.Semigroup      (Max (..))
import           Telomare            (FragExpr (..), FragIndex (FragIndex),
                                      IExpr (..), LamType (..), ParserTerm (..),
                                      Term1, Term2, Term3 (Term3),
                                      Term4 (Term4), buildFragMap, deferF,
                                      rootFrag, unFragExprUR)
import           Telomare.Parser     (UnprocessedParsedTerm (..))

decompileUPT :: UnprocessedParsedTerm -> String
decompileUPT =
  let lineLimit = 120
      -- "hello"
      showS :: String -> State.State Int String
      showS s = let indent = length s in State.modify (+ indent) >> pure s
      drawIndent = State.get >>= (\n -> pure $ replicate n ' ')
      drawList = fmap mconcat . sequence
      needsParens = \case -- will need parens if on right side of application
        AppUP _ _   -> True
        LamUP _ _   -> True
        LeftUP _    -> True
        RightUP _   -> True
        TraceUP _   -> True
        LetUP _ _   -> True
        ITEUP _ _ _ -> True
        _           -> False
      needsFirstParens = \case
        LamUP _ _   -> True
        LetUP _ _   -> True
        ITEUP _ _ _ -> True
        _           -> False
      drawParens x = if needsParens x
        then drawList [showS " (", draw x, showS ")"]
        else drawList [showS " ", draw x]
      drawFirstParens x = if needsFirstParens x
        then drawList [showS "(", draw x, showS ")"]
        else draw x
      draw :: UnprocessedParsedTerm -> State.State Int String
      draw = \case
          VarUP s -> showS s
          ITEUP i t e -> drawList [showS "if ", draw i, showS " then ", draw t, showS " else ", draw e]
          LetUP ((firstName, firstDef):bindingsXS) in_ -> if null bindingsXS
            then drawList [showS "let ", showS firstName, showS " = ", draw firstDef, showS " in ", draw in_]
            else do
            startIn <- State.get
            l <- showS "let "
            startBind <- State.get
            fb <- drawList [showS firstName, showS " = ", draw firstDef, pure "\n"]
            let drawOne (name, upt) = do
                  State.put startBind
                  drawList [drawIndent, showS name, showS " = ", draw upt, pure "\n"]
            displayedBindings <- mconcat <$> traverse drawOne bindingsXS
            State.put startIn
            mconcat <$> sequence [pure l, pure fb, pure displayedBindings, drawIndent, showS "in ", draw in_]
          ListUP l -> let insertCommas []     = []
                          insertCommas [x]    = [x]
                          insertCommas (x:xs) = x : showS "," : insertCommas xs
                      in drawList [showS "[", fmap concat . sequence . insertCommas $ fmap draw l, showS "]" ]
          IntUP x -> showS $ show x
          StringUP s -> drawList [showS "\"", showS s, showS "\""]
          PairUP a b -> drawList [showS "(", draw a, showS ",", draw b, showS ")"]
          AppUP f x -> drawList [drawFirstParens f, drawParens x]
          -- TODO flatten nested lambdas
          LamUP n x -> drawList [showS "\\", showS n, showS " -> ", draw x]
          ChurchUP n -> drawList [showS "$", showS $ show n]
          UnsizedRecursionUP t r b -> drawList [showS "{", draw t, showS ",", draw r, showS ",", draw b, showS "}"]
          LeftUP x -> drawList [showS "left ", drawParens x]
          RightUP x -> drawList [showS "right ", drawParens x]
          TraceUP x -> drawList [showS "trace ", drawParens x]
          CheckUP c x -> drawList [draw x, showS " : ", draw c]

  in \x -> State.evalState (draw x) 0
  {-
      safeTail s = if null s then [] else tail s
      showMem s = do
        let indent = length . last . takeWhile (not . null) . iterate (safeTail . dropWhile (/= '\n')) $ s
        if elem '\n' s
          then State.put indent
          else State.modify (+ indent)
        pure s
      draw oneLine =
        let showTwo a b = undefined --let long =
            showLine l = do
              indent <- State.get
              let long = intercalate " " l
                         in if length long > lineLimit
                            then

-}
              {-m
          drawLineOr x y = if not oneLine && draw
-}

decompileTerm1 :: Term1 -> UnprocessedParsedTerm
decompileTerm1 = \case
  TZero -> IntUP 0
  TPair a b -> PairUP (decompileTerm1 a) (decompileTerm1 b)
  TVar n -> VarUP n
  TApp f x -> AppUP (decompileTerm1 f) (decompileTerm1 x)
  TCheck c x -> CheckUP (decompileTerm1 c) (decompileTerm1 x)
  TITE i t e ->ITEUP (decompileTerm1 i) (decompileTerm1 t) (decompileTerm1 e)
  TLeft x -> LeftUP (decompileTerm1 x)
  TRight x -> RightUP (decompileTerm1 x)
  TTrace x -> TraceUP (decompileTerm1 x)
  TLam (Open n) x -> LamUP n (decompileTerm1 x)
  TLam (Closed n) x -> LamUP n (decompileTerm1 x) -- not strictly equivalent
  TLimitedRecursion t r b -> UnsizedRecursionUP (decompileTerm1 t) (decompileTerm1 r) (decompileTerm1 b)

decompileTerm2 :: Term2 -> Term1
decompileTerm2 =
  let nameSupply = map (:[]) ['a'..'z'] ++ [x <> y | x <- nameSupply, y <- nameSupply]
      getName n = if n < 0
        then nameSupply !! 0
        else nameSupply !! n
      go = \case
        TZero -> pure TZero
        TPair a b -> TPair <$> go a <*> go b
        TVar n ->  (Max n, TVar (getName n))
        TApp f x -> TApp <$> go f <*> go x
        TCheck c x -> TCheck <$> go c <*> go x
        TITE i t e -> TITE <$> go i <*> go t <*> go e
        TLeft x -> TLeft <$> go x
        TRight x -> TRight <$> go x
        TTrace x -> TTrace <$> go x
        TLam (Open ()) x -> (\(Max n, r) -> (Max n, (TLam (Open (getName n)) r))) $ go x -- warning, untested
        TLam (Closed ()) x -> (\(Max n, r) -> (Max 0, (TLam (Closed (getName n)) r))) $ go x
        TLimitedRecursion t r b -> TLimitedRecursion <$> go t <*> go r <*> go b
  in snd . go

decompileFragMap :: Map.Map FragIndex (FragExpr a) -> Term2
decompileFragMap tm =
  let decomp = let recur = decomp in \case
        ZeroFrag -> TZero
        PairFrag a b -> TPair (recur a) (recur b)
        EnvFrag -> TVar 0
        SetEnvFrag x -> TApp (TLam (Closed ()) (TApp (TLeft (TVar 0)) (TRight (TVar 0)))) $ recur x
        DeferFrag ind -> TLam (Closed ()) . recur $ tm Map.! ind
        AbortFrag -> TLam (Closed ()) . TLam (Open ())
          $ TCheck (TLam (Closed ()) (TVar 1)) (TVar 0)
        GateFrag l r -> TLam (Closed ()) $ TITE (TVar 0) (recur r) (recur l)
        LeftFrag x -> TLeft $ recur x
        RightFrag x -> TRight $ recur x
        TraceFrag -> TLam (Closed ()) $ TTrace (TVar 0)
        AuxFrag _ -> error "decompileFragMap: TODO AuxFrag" -- TLimitedRecursion
  in decomp $ rootFrag tm

decompileTerm4 :: Term4 -> Term2
decompileTerm4 (Term4 tm) = decompileFragMap tm

decompileTerm3 :: Term3 -> Term2
decompileTerm3 (Term3 tm) = decompileFragMap $ Map.map unFragExprUR tm

decompileIExpr :: IExpr -> Term4
decompileIExpr x = let build = \case
                         Zero     -> pure ZeroFrag
                         Pair a b -> PairFrag <$> build a <*> build b
                         Env      -> pure EnvFrag
                         SetEnv x -> SetEnvFrag <$> build x
                         Gate l r -> GateFrag <$> build l <*> build r
                         PLeft x  -> LeftFrag <$> build x
                         PRight x -> RightFrag <$> build x
                         Trace    -> pure TraceFrag
                         Defer x  -> deferF $ build x
                   in Term4 . buildFragMap $ build x
