{-# LANGUAGE LambdaCase #-}

module Telomare.Decompiler where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (foldM, liftM2)
import qualified Control.Monad.State as State
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Semigroup (Max (..))
import Telomare (FragExpr (..), FragExprF (..), FragIndex (FragIndex),
                 IExpr (..), LamType (..), ParserTerm (..), ParserTermF (..),
                 Term1, Term2, Term3 (Term3), Term4 (Term4), buildFragMap,
                 deferF, rootFrag, tag, unFragExprUR)
import Telomare.Parser (UnprocessedParsedTerm (..))

decompileUPT :: UnprocessedParsedTerm -> String
decompileUPT =
  let lineLimit = 120
      -- "hello"
      showS :: String -> State.State Int String
      showS s = let indent = length s in State.modify (+ indent) >> pure s
      drawIndent = State.get >>= (\n -> pure $ replicate n ' ')
      drawList = fmap mconcat . sequence
      needsParens = \case -- will need parens if on right side of application
        AppUP _ _ -> True
        LamUP _ _ -> True
        LeftUP _  -> True
        RightUP _ -> True
        TraceUP _ -> True
        LetUP _ _ -> True
        ITEUP {}  -> True
        _         -> False
      needsFirstParens = \case
        LamUP _ _ -> True
        LetUP _ _ -> True
        ITEUP {}  -> True
        _         -> False
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
  _ :< TZeroF -> IntUP 0
  _ :< TPairF a b -> PairUP (decompileTerm1 a) (decompileTerm1 b)
  _ :< TVarF n -> VarUP n
  _ :< TAppF f x -> AppUP (decompileTerm1 f) (decompileTerm1 x)
  _ :< TCheckF c x -> CheckUP (decompileTerm1 c) (decompileTerm1 x)
  _ :< TITEF i t e ->ITEUP (decompileTerm1 i) (decompileTerm1 t) (decompileTerm1 e)
  _ :< TLeftF x -> LeftUP (decompileTerm1 x)
  _ :< TRightF x -> RightUP (decompileTerm1 x)
  _ :< TTraceF x -> TraceUP (decompileTerm1 x)
  _ :< TLamF (Open n) x -> LamUP n (decompileTerm1 x)
  _ :< TLamF (Closed n) x -> LamUP n (decompileTerm1 x) -- not strictly equivalent
  _ :< TLimitedRecursionF t r b -> UnsizedRecursionUP (decompileTerm1 t) (decompileTerm1 r) (decompileTerm1 b)

decompileTerm2 :: Term2 -> Term1
decompileTerm2 =
  let nameSupply = (fmap (:[]) ['a'..'z'] <> ([x <> y | x <- nameSupply, y <- nameSupply]))
      getName n = if n < 0
        then head nameSupply
        else nameSupply !! n
      go :: Term2
         -> (Max Int, Term1)
      go = \case
        anno :< TZeroF -> pure $ anno :< TZeroF
        anno :< TPairF a b -> (\x y -> anno :< TPairF x y) <$> go a <*> go b
        anno :< TVarF n ->  (Max n, anno :< TVarF (getName n))
        anno :< TAppF f x -> (\y z -> anno :< TAppF y z) <$> go f <*> go x
        anno :< TCheckF c x -> (\y z -> anno :< TCheckF y z) <$> go c <*> go x
        anno :< TITEF i t e -> (\x y z -> anno :< TITEF x y z) <$> go i <*> go t <*> go e
        anno :< TLeftF x -> (anno :<) . TLeftF <$> go x
        anno :< TRightF x -> (anno :<) . TRightF <$> go x
        anno :< TTraceF x -> (anno :<) . TTraceF <$> go x
        anno :< TLamF (Open ()) x -> (\(Max n, r) -> (Max n, (anno :<) $ TLamF (Open (getName n)) r)) $ go x -- warning, untested
        anno :< TLamF (Closed ()) x -> (\(Max n, r) -> (Max 0, (anno :<) $ TLamF (Closed (getName n)) r)) $ go x
        anno :< TLimitedRecursionF t r b -> (\x y z -> anno :< TLimitedRecursionF x y z) <$> go t <*> go r <*> go b
  in snd . go

decompileFragMap :: Map.Map FragIndex (Cofree (FragExprF a) (Int, Int)) -> Term2
decompileFragMap tm =
  let decomp :: Cofree (FragExprF a) (Int, Int)
             -> Term2
      decomp = let recur = decomp in \case
        anno :< ZeroFragF -> anno :< TZeroF
        anno :< PairFragF a b -> anno :< TPairF (recur a) (recur b)
        anno :< EnvFragF -> anno :< TVarF 0
        anno :< SetEnvFragF x -> anno :< TAppF (anno :< TLamF (Closed ()) (anno :< TAppF (anno :< TLeftF (anno :< TVarF 0))
                                                                                         (anno :< TRightF (anno :< TVarF 0))))
                                               (recur x)
        anno :< DeferFragF ind -> anno :< (TLamF (Closed ()) . recur $ tm Map.! ind)
        anno :< AbortFragF -> anno :< TLamF (Closed ()) (anno :< (TLamF (Open ()) $
                                            (anno :< TCheckF (anno :< TLamF (Closed ()) (anno :< TVarF 1))
                                                             (anno :< TVarF 0))))
        anno :< GateFragF l r -> anno :< TLamF (Closed ()) (anno :< TITEF (anno :< TVarF 0) (recur r) (recur l))
        anno :< LeftFragF x -> anno :< TLeftF (recur x)
        anno :< RightFragF x -> anno :< TRightF (recur x)
        anno :< TraceFragF -> anno :< TLamF (Closed ()) (anno :< TTraceF (anno :< TVarF 0))
        anno :< AuxFragF _ -> error "decompileFragMap: TODO AuxFrag" -- TLimitedRecursion
  in decomp $ rootFrag tm

decompileTerm4 :: Term4 -> Term2
decompileTerm4 (Term4 tm) = decompileFragMap tm

decompileTerm3 :: Term3 -> Term2
decompileTerm3 (Term3 tm) = decompileFragMap $ Map.map unFragExprUR tm

decompileIExpr :: IExpr -> Term4
decompileIExpr x = let build = \case
                         Zero     -> pure . tag (0,0) $ ZeroFrag
                         Pair a b -> (\x y -> (0,0) :< PairFragF x y) <$> build a <*> build b
                         Env      -> pure . tag (0,0) $ EnvFrag
                         SetEnv x -> ((0,0) :<) . SetEnvFragF <$> build x
                         Gate l r -> (\x y -> (0,0) :< GateFragF x y) <$> build l <*> build r
                         PLeft x  -> ((0,0) :<) . LeftFragF <$> build x
                         PRight x -> ((0,0) :<) . RightFragF <$> build x
                         Trace    -> pure . tag (0,0) $ TraceFrag
                         Defer x  -> deferF $ build x
                   in Term4 . buildFragMap $ build x
