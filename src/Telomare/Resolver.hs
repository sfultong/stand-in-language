{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.Resolver where

import Codec.Binary.UTF8.String (encode)
import Control.Comonad
import Control.Comonad.Cofree (Cofree (..))
import Control.Comonad.Trans.Cofree (CofreeF)
import qualified Control.Comonad.Trans.Cofree as C
import Control.Lens.Combinators (transform)
import Control.Monad ((<=<))
import qualified Control.Monad.State as State
import Crypto.Hash (Digest, SHA256, hash)
import Data.Bifunctor (Bifunctor (first), bimap)
import qualified Data.ByteArray as BA
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (ord)
import qualified Data.Foldable as F
import Data.Functor.Foldable (Base, Corecursive (ana, apo), Recursive (cata))
import Data.List (delete, elem, elemIndex, zip4)
import qualified Data.Map as Map
import Data.Map.Strict (Map, fromList, keys)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Debug.Trace (trace, traceShow, traceShowId)
import PrettyPrint (TypeDebugInfo (..), showTypeDebugInfo)
import Telomare (BreakState', DataType (..), FragExpr (..), FragExprF (..),
                 FragExprUR (..), FragIndex (..), IExpr (..), IExprF (..),
                 LamType (..), ParserTerm (..), ParserTermF (..),
                 PartialType (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..), Term1 (..), Term2 (..),
                 Term3 (..), UnsizedRecursionToken, appF, clamF, deferF, forget,
                 forgetAnnotationFragExprUR, gateF, lamF, nextBreakToken, pairF,
                 setEnvF, showRunBreakState', tag, unsizedRecursionWrapper,
                 varNF)
import Telomare.Parser (AnnotatedUPT, Pattern (..), PatternF (..),
                        PrettyUPT (..), TelomareParser (..),
                        UnprocessedParsedTerm (..), UnprocessedParsedTermF (..),
                        parseWithPrelude)
import Text.Megaparsec (errorBundlePretty, runParser)

type VarList = [String]

-- |Int to ParserTerm
i2t :: (Int, Int) -> Int -> Cofree (ParserTermF l v) (Int, Int)
i2t anno = ana coalg where
  coalg :: Int -> CofreeF (ParserTermF l v) (Int, Int) Int
  coalg 0 = anno C.:< TZeroF
  coalg n = anno C.:< TPairF (n-1) 0

-- |List of Int's to ParserTerm
ints2t :: (Int, Int) ->  [Int] -> Cofree (ParserTermF l v) (Int, Int)
ints2t anno = foldr ((\x y -> anno :< TPairF x y) . i2t anno) (anno :< TZeroF)

-- |String to ParserTerm
s2t :: (Int, Int) -> String -> Cofree (ParserTermF l v) (Int, Int)
s2t anno = ints2t anno . fmap ord

-- |Int to Church encoding
i2c :: (Int, Int) -> Int -> Term1
i2c anno x = anno :< TLamF (Closed "f") (anno :< TLamF (Open "x") (inner x))
  where inner :: Int -> Term1
        inner = apo coalg
        coalg :: Int -> Base Term1 (Either Term1 Int)
        coalg 0 = anno C.:< TVarF "x"
        coalg n = anno C.:< TAppF (Left . (anno :<) . TVarF $ "f") (Right $ n - 1)

instance MonadFail (Either String) where
  fail = Left

-- | Finds all PatternInt leaves returning "directions" to these leaves through pairs
-- in the form of a combination of RightUP and LeftUP from the root
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) (PatternVar "y"))
--      will return [LeftUP . RightUP]
findInts :: (Int, Int) -> Pattern -> [AnnotatedUPT -> AnnotatedUPT]
findInts anno = cata alg where
  alg :: Base Pattern [AnnotatedUPT -> AnnotatedUPT]
      -> [AnnotatedUPT -> AnnotatedUPT]
  alg = \case
    PatternPairF x y -> ((. (anno :< ) . LeftUPF) <$> x) <> ((. (anno :< ) . RightUPF) <$> y)
    PatternIntF x    -> [id]
    _                -> []

-- | Finds all PatternString leaves returning "directions" to these leaves through pairs
-- in the form of a combination of RightUP and LeftUP from the root
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternString "Hello, world!") (PatternVar "y"))
--      will return [LeftUP . RightUP]
findStrings :: (Int, Int) -> Pattern -> [AnnotatedUPT -> AnnotatedUPT]
findStrings anno = cata alg where
  alg :: Base Pattern [AnnotatedUPT -> AnnotatedUPT]
      -> [AnnotatedUPT -> AnnotatedUPT]
  alg = \case
    PatternPairF x y -> ((. (anno :< ) . LeftUPF) <$> x) <> ((. (anno :< ) . RightUPF) <$> y)
    PatternStringF x -> [id]
    _                -> []


-- TODO: Does using that `anno` make sense?
fitPatternVarsToCasedUPT :: Pattern -> AnnotatedUPT -> AnnotatedUPT
fitPatternVarsToCasedUPT p aupt@(anno :< _) = applyVars2UPT varsOnUPT $ pattern2UPT anno p where
  varsOnUPT :: Map String AnnotatedUPT
  varsOnUPT = ($ aupt) <$> findPatternVars anno p
  applyVars2UPT :: Map String AnnotatedUPT
                -> AnnotatedUPT
                -> AnnotatedUPT
  applyVars2UPT m = \case
    anno :< LamUPF str x ->
      case Map.lookup str m of
        Just a  -> anno :< AppUPF (anno :< LamUPF str (applyVars2UPT m x)) a
        Nothing -> anno :< LamUPF str x
    x -> x

-- |Collect all free variable names in a `AnnotatedUPT` expresion
varsUPT :: UnprocessedParsedTerm -> Set String
varsUPT = cata alg where
  alg :: Base UnprocessedParsedTerm (Set String) -> Set String
  alg (VarUPF n)     = Set.singleton n
  alg (LamUPF str x) = del str x
  alg e              = F.fold e
  del :: String -> Set String -> Set String
  del n x = if Set.member n x then Set.delete n x else x

-- TODO: there has to be a more elegant way of doing this
forgetAUPTAnnotation :: AnnotatedUPT -> UnprocessedParsedTerm
forgetAUPTAnnotation = \case
  _ :< VarUPF str -> VarUP str
  _ :< IntUPF i -> IntUP i
  _ :< StringUPF str -> StringUP str
  _ :< ChurchUPF i -> ChurchUP i
  _ :< LeftUPF x -> LeftUP $ forgetAUPTAnnotation x
  _ :< RightUPF x -> RightUP $ forgetAUPTAnnotation x
  _ :< TraceUPF x -> TraceUP $ forgetAUPTAnnotation x
  _ :< HashUPF x -> HashUP $ forgetAUPTAnnotation x
  _ :< PairUPF x y -> PairUP (forgetAUPTAnnotation x)
                             (forgetAUPTAnnotation y)
  _ :< AppUPF x y -> AppUP (forgetAUPTAnnotation x)
                           (forgetAUPTAnnotation y)
  _ :< CheckUPF x y -> CheckUP (forgetAUPTAnnotation x)
                               (forgetAUPTAnnotation y)
  _ :< UnsizedRecursionUPF x y z ->
         UnsizedRecursionUP (forgetAUPTAnnotation x)
                            (forgetAUPTAnnotation y)
                            (forgetAUPTAnnotation z)
  _ :< ITEUPF x y z -> ITEUP (forgetAUPTAnnotation x)
                             (forgetAUPTAnnotation y)
                             (forgetAUPTAnnotation z)
  _ :< LamUPF str x -> LamUP str $ forgetAUPTAnnotation x
  _ :< ListUPF l -> ListUP $ forgetAUPTAnnotation <$> l
  _ :< CaseUPF x l -> CaseUP (forgetAUPTAnnotation x)
                             ((fmap . fmap) forgetAUPTAnnotation l)
  _ :< LetUPF l x -> LetUP ((fmap . fmap) forgetAUPTAnnotation l)
                           (forgetAUPTAnnotation x)

-- TODO: there has to be a more elegant way of doing this
annotateUPTwith :: (Int,Int) -> UnprocessedParsedTerm -> AnnotatedUPT
annotateUPTwith anno = \case
  VarUP str -> anno :< VarUPF str
  IntUP i -> anno :< IntUPF i
  StringUP str -> anno :< StringUPF str
  ChurchUP i -> anno :< ChurchUPF i
  LeftUP x -> anno :< LeftUPF (annotateUPTwith anno x)
  RightUP x -> anno :< RightUPF (annotateUPTwith anno x)
  TraceUP x -> anno :< TraceUPF (annotateUPTwith anno x)
  HashUP x -> anno :< HashUPF (annotateUPTwith anno x)
  PairUP x y -> anno :< PairUPF (annotateUPTwith anno x)
                                (annotateUPTwith anno y)
  AppUP x y -> anno :< AppUPF (annotateUPTwith anno x)
                              (annotateUPTwith anno y)
  CheckUP x y -> anno :< CheckUPF (annotateUPTwith anno x)
                                  (annotateUPTwith anno y)
  UnsizedRecursionUP x y z -> anno :<
    UnsizedRecursionUPF (annotateUPTwith anno x)
                        (annotateUPTwith anno y)
                        (annotateUPTwith anno z)
  ITEUP x y z -> anno :< ITEUPF (annotateUPTwith anno x)
                                (annotateUPTwith anno y)
                                (annotateUPTwith anno z)
  LamUP str x -> anno :< LamUPF str (annotateUPTwith anno x)
  ListUP l -> anno :< ListUPF (annotateUPTwith anno <$> l)
  CaseUP x l -> anno :< CaseUPF (annotateUPTwith anno x)
                               ((fmap . fmap) (annotateUPTwith anno) l)
  LetUP l x -> anno :< LetUPF ((fmap . fmap) (annotateUPTwith anno) l)
                              (annotateUPTwith anno x)

mkLambda4FreeVarUPs :: AnnotatedUPT -> AnnotatedUPT
mkLambda4FreeVarUPs aupt@(anno :< _) = annotateUPTwith anno $ go upt freeVars where
  upt = forgetAUPTAnnotation aupt
  freeVars = Set.toList . varsUPT $ upt
  go :: UnprocessedParsedTerm -> [String] -> UnprocessedParsedTerm
  go x = \case
    []     -> x
    (y:ys) -> LamUP y $ go x ys

findPatternVars ::(Int, Int) ->  Pattern -> Map String (AnnotatedUPT -> AnnotatedUPT)
findPatternVars anno = cata alg where
  alg :: Base Pattern (Map String (AnnotatedUPT -> AnnotatedUPT))
      -> Map String (AnnotatedUPT -> AnnotatedUPT)
  alg = \case
    PatternPairF x y -> ((. (anno :< ). LeftUPF) <$> x) <> ((. (anno :< ). RightUPF) <$> y)
    PatternVarF str  -> Map.singleton str id
    _                -> Map.empty

-- TODO: Annotate without so much fuzz
pairStructureCheck :: (Int, Int) -> Pattern -> AnnotatedUPT -> AnnotatedUPT
pairStructureCheck anno p aupt = annotateUPTwith anno $
  AppUP (AppUP (AppUP (VarUP "foldl")
                      (VarUP "and"))
               (IntUP 1))
        (ListUP $ ($ upt) <$> pairRoute2Dirs p)
    where upt = forgetAUPTAnnotation aupt

pairRoute2Dirs :: Pattern -> [UnprocessedParsedTerm -> UnprocessedParsedTerm]
pairRoute2Dirs = cata alg where
  alg :: Base Pattern [UnprocessedParsedTerm -> UnprocessedParsedTerm]
      -> [UnprocessedParsedTerm -> UnprocessedParsedTerm]
  alg = \case
    PatternPairF x y -> [id] <> ((. LeftUP) <$> x) <> ((. RightUP) <$> y)
    _                -> []

pattern2UPT :: (Int, Int) -> Pattern -> AnnotatedUPT
pattern2UPT anno = annotateUPTwith anno . cata alg where
  alg :: Base Pattern UnprocessedParsedTerm -> UnprocessedParsedTerm
  alg = \case
    PatternPairF x y   -> PairUP x y
    PatternIntF i      -> IntUP i
    PatternStringF str -> StringUP str
    PatternVarF str    -> IntUP 0
    PatternIgnoreF     -> IntUP 0
      -- Note that "__ignore" is a special variable name and not accessible to users because
      -- parsing of VarUPs doesn't allow variable names to start with `_`

mkCaseAlternative :: AnnotatedUPT -- ^ UPT to be cased
                  -> AnnotatedUPT -- ^ Case result to be made lambda and applied
                  -> Pattern -- ^ Pattern
                  -> AnnotatedUPT -- ^ case result as a lambda applied to the appropirate part of the UPT to be cased
mkCaseAlternative casedUPT@(anno :< _) caseResult p = appVars2ResultLambdaAlts patternVarsOnUPT . makeLambdas caseResult . keys $ patternVarsOnUPT where
  patternVarsOnUPT :: Map String AnnotatedUPT
  patternVarsOnUPT = ($ casedUPT) <$> findPatternVars anno p
  appVars2ResultLambdaAlts :: Map String AnnotatedUPT
                           -> AnnotatedUPT -- ^ case result as lambda
                           -> AnnotatedUPT
  appVars2ResultLambdaAlts m = \case
    lam@(_ :< LamUPF varName upt) ->
      case Map.lookup varName m of
        Nothing -> lam
        Just x -> anno :< AppUPF (anno :< LamUPF varName (appVars2ResultLambdaAlts (Map.delete varName m) upt)) x
    x -> x
  makeLambdas :: AnnotatedUPT
              -> [String]
              -> AnnotatedUPT
  makeLambdas aupt@(anno' :< _) = \case
    []     -> aupt
    (x:xs) -> anno' :< LamUPF x (makeLambdas aupt xs)

-- Cofree f a
-- (:<) :: a :< f (Cofree f a)


-- liftAnnotation :: (Int, Int)
--                -> (UnprocessedParsedTerm -> UnprocessedParsedTerm)
--                -> AnnotatedUPT -> AnnotatedUPT
-- liftAnnotation anno = undefined

-- CaseUP AUPT
--        [(Pattern, AUPT)]

-- TODO: make annotations without fuzz maybe
case2annidatedIfs :: AnnotatedUPT -- ^ Term to be pattern matched
                  -> [Pattern] -- ^ All patterns in a case expression
                  -> [AnnotatedUPT] -- ^ Int leaves as ListUPs on UPT
                  -> [AnnotatedUPT] -- ^ Int leaves as ListUPs on pattern
                  -> [AnnotatedUPT] -- ^ String leaves as ListUPs on UPT
                  -> [AnnotatedUPT] -- ^ String leaves as ListUPs on pattern
                  -> [AnnotatedUPT] -- ^ Case's alternatives
                  -> AnnotatedUPT
case2annidatedIfs (anno :< _) [] [] [] [] [] [] = annotateUPTwith anno $
  ITEUP (IntUP 1)
        (AppUP (VarUP "abort") $ StringUP "Non-exhaustive patterns in case")
        (IntUP 0)
case2annidatedIfs x (aPattern:as) ((_ :< ListUPF []) : bs) ((_ :< ListUPF []) :cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
  annotateUPTwith anno $
    ITEUP (AppUP (AppUP (VarUP "and")
                        (AppUP (AppUP (VarUP "listEqual") (forgetAUPTAnnotation dirs2StringOnUPT)) (forgetAUPTAnnotation dirs2StringOnPattern)))
                 (forgetAUPTAnnotation $ pairStructureCheck anno aPattern x))
          (forgetAUPTAnnotation $ mkCaseAlternative x resultAlternative aPattern)
          (forgetAUPTAnnotation $ case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) ((_ :< ListUPF []) : ds) ((_ :< ListUPF []) : es) (resultAlternative@(anno :< _):fs) =
  annotateUPTwith anno $
    ITEUP (AppUP (AppUP (VarUP "and")
                        (AppUP (AppUP (VarUP "listEqual") (forgetAUPTAnnotation dirs2IntOnUPT)) (forgetAUPTAnnotation dirs2IntOnPattern)))
                 (forgetAUPTAnnotation $ pairStructureCheck anno aPattern x))
          (forgetAUPTAnnotation $ mkCaseAlternative x resultAlternative aPattern)
          (forgetAUPTAnnotation $ case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
  annotateUPTwith anno $
    ITEUP (AppUP (AppUP (AppUP (VarUP "foldl")
                                (VarUP "and"))
                        (IntUP 1))
                 (ListUP [ AppUP (AppUP (VarUP "listEqual") (forgetAUPTAnnotation dirs2IntOnUPT)) (forgetAUPTAnnotation dirs2IntOnPattern)
                         , AppUP (AppUP (VarUP "listEqual") (forgetAUPTAnnotation dirs2StringOnUPT)) (forgetAUPTAnnotation dirs2StringOnPattern)
                         , forgetAUPTAnnotation $ pairStructureCheck anno aPattern x
                         ]))
          (forgetAUPTAnnotation $ mkCaseAlternative x resultAlternative aPattern)
          (forgetAUPTAnnotation $ case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs _ _ _ _ _ _ _ = error "case2annidatedIfs: lists don't match in size"

removeCaseUPs :: AnnotatedUPT -> AnnotatedUPT
removeCaseUPs = transform go where
  go :: AnnotatedUPT -> AnnotatedUPT
  go = \case
    anno :< CaseUPF x ls ->
      let duplicate x = (x,x)
          pairApplyList :: ([a -> a], a) -> [a]
          pairApplyList x = ($ snd x) <$> fst x
          patterns = fst <$> ls
          resultCaseAlts = snd <$> ls
          dirs2LeavesOnUPT :: (Pattern -> [AnnotatedUPT -> AnnotatedUPT])
                           -> [AnnotatedUPT]
          dirs2LeavesOnUPT f = fmap (\y -> anno :< ListUPF y) $ (($ x) <$>) . f <$> patterns
          dirs2LeavesOnPattern :: (Pattern -> [AnnotatedUPT -> AnnotatedUPT])
                               -> [AnnotatedUPT]
          dirs2LeavesOnPattern f = (\a -> anno :< ListUPF a) <$> (pairApplyList <$> (bimap f (pattern2UPT anno) . duplicate <$> patterns))
      in case2annidatedIfs x
                           patterns
                           (dirs2LeavesOnUPT (findInts anno))
                           (dirs2LeavesOnPattern $ findInts anno)
                           (dirs2LeavesOnUPT $ findStrings anno)
                           (dirs2LeavesOnPattern $ findStrings anno)
                           resultCaseAlts
    x -> x

debruijinize :: MonadFail m => VarList -> Term1 -> m Term2
debruijinize vl = \case
  all@(anno :< TZeroF) -> pure $ anno :< TZeroF
  (anno :< TPairF a b) -> (\x y -> anno :< TPairF x y) <$> debruijinize vl a <*> debruijinize vl b
  (anno :< TVarF n) -> case elemIndex n vl of
               Just i  -> pure $ anno :< TVarF i
               Nothing -> fail ("undefined identifier " <> n)
  (anno :< TAppF i c) -> (\x y -> anno :< TAppF x y) <$> debruijinize vl i <*> debruijinize vl c
  (anno :< TCheckF c tc) -> (\x y -> anno :< TCheckF x y) <$> debruijinize vl c <*> debruijinize vl tc
  (anno :< TITEF i t e) -> (\x y z -> anno :< TITEF x y z) <$> debruijinize vl i
                                                           <*> debruijinize vl t
                                                           <*> debruijinize vl e
  (anno :< TLeftF x) -> (\y -> anno :< TLeftF y) <$> debruijinize vl x
  (anno :< TRightF x) -> (\y -> anno :< TRightF y) <$> debruijinize vl x
  (anno :< TTraceF x) -> (\y -> anno :< TTraceF y) <$> debruijinize vl x
  (anno :< THashF x) -> (\y -> anno :< THashF y) <$> debruijinize vl x
  (anno :< TLamF (Open n) x) -> (\y -> anno :< TLamF (Open ()) y) <$> debruijinize (n : vl) x
  (anno :< TLamF (Closed n) x) -> (\y -> anno :< TLamF (Closed ()) y) <$> debruijinize (n : vl) x
  (anno :< TLimitedRecursionF t r b) -> (\x y z -> anno :< TLimitedRecursionF x y z) <$> debruijinize vl t <*> debruijinize vl r <*> debruijinize vl b
--    $ trace ("trace statement:\n" <> show (forget term1 :: ParserTerm String String)) term1

rewriteOuterTag :: anno -> Cofree a anno -> Cofree a anno
rewriteOuterTag anno (_ :< x) = anno :< x

y :: ParserTerm () Int
y =
                (TApp
                  (TVar 3)
                  -- (TLeft
                    (TVar 2))
                     -- )
yy :: FragExpr RecursionPieceFrag
yy = forget $ State.evalState (splitExpr' $ tag (0,0) y) (toEnum 0, FragIndex 1, Map.empty)

-- xx  :: FragExpr RecursionPieceFrag
-- xx = forget $ State.evalState (splitExpr' $ tag (0,0) x) (toEnum 0, FragIndex 1, Map.empty)

-- x :: ParserTerm () Int
-- x =
--           -- TApp
--           --   (TVar 1)
--             -- (TApp
--               (TApp
--                 (TApp
--                   (TVar 3)
--                   (--TLeft
--                     (TVar 2)))
--                 (TVar 1))
--               -- (TVar 0))
-- z = 1

-- foo = putStrLn . showRunBreakState' $
--         appF (appF v v) v
--           where
--             v :: BreakState' RecursionPieceFrag UnsizedRecursionToken
--             v = pure . tag (0,0) $ LeftFrag EnvFrag

aux =
  -- TApp
  --   (TApp
  --     (TApp
        (TLimitedRecursion
          (TLam (Closed ())
            (TVar 0))
          (TLam (Closed ())
            (TVar 0))
          (TLam (Closed ())
            (TVar 0))
          -- (TLam (Closed ())
          --   (TLam (Open ())
          --     (TLam (Open ())
          --       (TLam (Open ())
          --         (TApp
          --           (TVar 1)
          --           (TApp
          --             (TApp
          --               (TApp
          --                 (TVar 3)
          --                 (TLeft
          --                   (TVar 2)))
          --               (TVar 12))
          --             (TVar 0)))))))
          -- (TLam (Closed ())
          --   (TLam (Closed ())
          --     (TLam (Closed ())
          --       (TVar 0))))
        )
    --     TZero)
    --   (TLam (Closed ())
    --     (TPair
    --       (TVar 0)
    --       TZero)))
    -- TZero

-- auxx  :: FragExpr RecursionPieceFrag
-- auxx :: (Cofree (FragExprF RecursionPieceFrag) (Int, Int),
 -- (UnsizedRecursionToken, FragIndex,
 --  Map FragIndex (Cofree (FragExprF RecursionPieceFrag) (Int, Int))))
auxx  :: (FragExpr RecursionPieceFrag, (UnsizedRecursionToken, FragIndex,
                            Map FragIndex (FragExpr RecursionPieceFrag)))
auxx = bimap forget (fmap . fmap $ forget) $ State.runState (splitExpr' $ tag (0,0) aux) (toEnum 0, FragIndex 1, Map.empty)

splitExpr' :: Term2 -> BreakState' RecursionPieceFrag UnsizedRecursionToken
splitExpr' term2 = (\case
  (anno :< TZeroF) -> pure (anno :< ZeroFragF)
  (anno :< TPairF a b) -> rewriteOuterTag anno <$> pairF (splitExpr' a) (splitExpr' b)
  (anno :< TVarF n) -> pure . tag anno $ varNF n
  (anno :< TAppF c i) ->
                         -- trace (  "\n<<<<splitExpr'TAppF:\n\n"
                         --       <> showRunBreakState' (splitExpr' c) <> "\n"
                         --       <> showRunBreakState' (splitExpr' i) <> "\n\n"
                         --       <> showRunBreakState' (appF (splitExpr' c) (splitExpr' i)) <> "\n"
                         --       <> "\nsplitExpr'TAppF>>>>\n"
                         --       )
    rewriteOuterTag anno <$> appF (splitExpr' c) (splitExpr' i)
  (anno :< TCheckF tc c) ->
    let performTC = deferF ((\ia -> setEnvF (pairF (setEnvF (pairF (pure $ tag anno AbortFrag) ia))
                                                   (pure . tag anno $ RightFrag EnvFrag))) $ appF (pure . tag anno $ LeftFrag EnvFrag)
                                                                                                  (pure . tag anno $ RightFrag EnvFrag))
    in rewriteOuterTag anno <$> setEnvF (pairF performTC (pairF (splitExpr' tc) (splitExpr' c)))
  (anno :< TITEF i t e) -> rewriteOuterTag anno <$> setEnvF (pairF (gateF (splitExpr' e) (splitExpr' t)) (splitExpr' i))
  (anno :< TLeftF x) -> (anno :<) . LeftFragF <$> splitExpr' x
  (anno :< TRightF x) -> (anno :<) . RightFragF <$> splitExpr' x
  (anno :< TTraceF x) -> rewriteOuterTag anno <$> setEnvF (pairF (deferF (pure . tag anno $ TraceFrag)) (splitExpr' x))
  (anno :< TLamF (Open ()) x) -> rewriteOuterTag anno <$> lamF (splitExpr' x)
  (anno :< TLamF (Closed ()) x) -> rewriteOuterTag anno <$> clamF (splitExpr' x)
  (anno :< TLimitedRecursionF t r b) ->
    rewriteOuterTag anno <$> (nextBreakToken >>=
      (\x -> -- trace ("trace statment: \n" <> show ((forget $ State.evalState (unsizedRecursionWrapper x (splitExpr' t) (splitExpr' r) (splitExpr' b)) (toEnum 0, FragIndex 1, Map.empty)) :: FragExpr RecursionPieceFrag))
        -- (_, fi, _) <- State.get
        -- trace ("<<<<trace statment:\n" <>
        --         (show fi
        --           -- <> "\n" <> (show (forget t :: ParserTerm () Int)) <> "\n"
        --           -- <> (show $ ((forget $ State.evalState (splitExpr' t) (toEnum 0, FragIndex 1, Map.empty)) :: FragExpr RecursionPieceFrag))
        --           -- <> "\n" <> (show (forget r :: ParserTerm () Int)) <> "\n"
        --           -- <> (show $ ((forget $ State.evalState (splitExpr' r) (toEnum 0, FragIndex 1, Map.empty)) :: FragExpr RecursionPieceFrag))
        --           -- <> "\n" <> (show (forget b :: ParserTerm () Int)) <> "\n"
        --           -- <> (show $ ((forget $ State.evalState (splitExpr' b) (toEnum 0, FragIndex 1, Map.empty)) :: FragExpr RecursionPieceFrag))
        --         ) <> "\ntrace statment>>>>\n")
              -- (_,fi,_) <- State.get
              -- trace (show fi) $
                unsizedRecursionWrapper x (splitExpr' t) (splitExpr' r) (splitExpr' b)))) term2
                --  $ trace ("\ntrace statement term2:\n" <> show (forget term2 :: ParserTerm () Int) <> "\n}}}}}}End\n") term2

-- newtype FragExprUR =
--   FragExprUR { unFragExprUR :: Cofree (FragExprF (RecursionSimulationPieces FragExprUR))
--                                       (Int,Int)
--              }
--   deriving (Eq, Show)

-- newtype Fix f = Fix { unFix :: f (Fix f) }

-- -- | Change base functor in 'Fix'.
-- hoistFix :: Functor f => (forall a. f a -> g a) -> Fix f -> Fix g
-- hoistFix nt = go where go (Fix f) = Fix (nt (fmap go f))

-- -- | Like 'hoistFix' but 'fmap'ping over @g@.
-- hoistFix' :: Functor g => (forall a. f a -> g a) -> Fix f -> Fix g
-- hoistFix' nt = go where go (Fix f) = Fix (fmap go (nt f))


newtype FragExprUR' =
  FragExprUR' { unFragExprUR' :: FragExpr (RecursionSimulationPieces FragExprUR')
              }
  deriving (Eq, Show)

newtype Term3' = Term3' (Map FragIndex FragExprUR') deriving (Eq, Show)


-- forgetFragExprUR :: FragExprUR -> FragExprUR'
-- forgetFragExprUR :: FragExprUR -> FragExpr (RecursionSimulationPieces (FragExpr (RecursionSimulationPieces FragExprUR)))
-- forgetFragExprUR :: FragExprUR -> FragExpr (RecursionSimulationPieces (Cofree (FragExprF (RecursionSimulationPieces FragExprUR)) (Int, Int)))
-- forgetFragExprUR :: FragExprUR -> FragExpr (RecursionSimulationPieces FragExprUR)
-- forgetFragExprUR x = (fmap . fmap) (forget . unFragExprUR) (forget . unFragExprUR $ x)
-- forgetFragExprUR = go where go (FragExprUR x) = FragExprUR' (forget x)

forgetFragmap :: Term3 -> Term3'
forgetFragmap (Term3 map) = Term3' undefined


splitExpr :: Term2 -> Term3
splitExpr t = -- let (bf, (_,_,m)) = State.runState (splitExpr' $ trace (show (forget t :: ParserTerm () Int)) t) (toEnum 0, FragIndex 1, Map.empty)
              let (bf, (_,_,m)) = State.runState (splitExpr' t) (toEnum 0, FragIndex 1, Map.empty)
                  aux = Term3 . Map.map FragExprUR $ Map.insert (FragIndex 0) bf m
              -- in trace ("trace statement:\n" <> show (aux)) aux
              in aux

-- auxWrapper :: Term3 -> TypeDebugInfo
-- auxWrapper t3 = TypeDebugInfo t3 (\x -> ZeroTypeP) ZeroTypeP

-- aux =
--   LetUP [("zero",IntUP 0),("left",LamUP "x" (LeftUP (VarUP "x"))),("right",LamUP "x" (RightUP (VarUP "x"))),("trace",LamUP "x" (TraceUP (VarUP "x"))),("pair",LamUP "x" (LamUP "y" (PairUP (VarUP "x") (VarUP "y")))),("app",LamUP "x" (LamUP "y" (AppUP (VarUP "x") (VarUP "y"))))]
--    (LetUP [("id",LamUP "x" (VarUP "x")),("and",LamUP "a" (LamUP "b" (ITEUP (VarUP "a") (VarUP "b") (IntUP 0)))),("or",LamUP "a" (LamUP "b" (ITEUP (VarUP "a") (IntUP 1) (VarUP "b")))),("not",LamUP "x" (ITEUP (VarUP "x") (IntUP 0) (IntUP 1))),("succ",LamUP "x" (PairUP (VarUP "x") (IntUP 0))),("d2c",UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "i" (LamUP "f" (LamUP "b" (AppUP (VarUP "f") (AppUP (AppUP (AppUP (VarUP "recur") (AppUP (VarUP "left") (VarUP "i"))) (VarUP "f")) (VarUP "b"))))))) (LamUP "i" (LamUP "f" (LamUP "b" (VarUP "b"))))),("c2d",LamUP "c" (AppUP (AppUP (VarUP "c") (VarUP "succ")) (IntUP 0))),("plus",LamUP "m" (LamUP "n" (LamUP "f" (LamUP "x" (AppUP (AppUP (VarUP "m") (VarUP "f")) (AppUP (AppUP (VarUP "n") (VarUP "f")) (VarUP "x"))))))),("times",LamUP "m" (LamUP "n" (LamUP "f" (AppUP (VarUP "m") (AppUP (VarUP "n") (VarUP "f")))))),("pow",LamUP "m" (LamUP "n" (AppUP (VarUP "n") (VarUP "m")))),("dMinus",LamUP "a" (LamUP "b" (AppUP (AppUP (AppUP (VarUP "d2c") (VarUP "b")) (LamUP "x" (AppUP (VarUP "left") (VarUP "x")))) (VarUP "a")))),("minus",LamUP "a" (LamUP "b" (AppUP (VarUP "d2c") (AppUP (AppUP (VarUP "b") (LamUP "x" (AppUP (VarUP "left") (VarUP "x")))) (AppUP (VarUP "c2d") (VarUP "a")))))),("range",LamUP "a" (LamUP "b" (AppUP (UnsizedRecursionUP (LamUP "i" (AppUP (AppUP (VarUP "dMinus") (VarUP "b")) (VarUP "i"))) (LamUP "recur" (LamUP "i" (PairUP (VarUP "i") (AppUP (VarUP "recur") (PairUP (VarUP "i") (IntUP 0)))))) (LamUP "i" (IntUP 0))) (VarUP "a")))),("map",LamUP "f" (UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "l" (PairUP (AppUP (VarUP "f") (AppUP (VarUP "left") (VarUP "l"))) (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "l")))))) (LamUP "l" (IntUP 0)))),("foldr",LamUP "f" (LamUP "b" (LamUP "ta" (LetUP [("fixed",UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "l" (LamUP "accum" (AppUP (AppUP (VarUP "f") (AppUP (VarUP "left") (VarUP "l"))) (AppUP (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "l"))) (VarUP "accum")))))) (LamUP "l" (LamUP "accum" (VarUP "accum"))))] (AppUP (AppUP (VarUP "fixed") (VarUP "ta")) (VarUP "b")))))),("foldl",LamUP "f" (LamUP "b" (LamUP "ta" (LetUP [("fixed",UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "l" (LamUP "accum" (AppUP (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "l"))) (AppUP (AppUP (VarUP "f") (VarUP "accum")) (AppUP (VarUP "left") (VarUP "l"))))))) (LamUP "l" (LamUP "accum" (VarUP "accum"))))] (AppUP (AppUP (VarUP "fixed") (VarUP "ta")) (VarUP "b")))))),("zipWith",LamUP "f" (LamUP "a" (LamUP "b" (LetUP [("fixed",UnsizedRecursionUP (LamUP "ab" (AppUP (AppUP (VarUP "and") (AppUP (VarUP "left") (VarUP "ab"))) (AppUP (VarUP "right") (VarUP "ab")))) (LamUP "recur" (LamUP "ab" (PairUP (AppUP (AppUP (VarUP "f") (AppUP (VarUP "left") (AppUP (VarUP "left") (VarUP "ab")))) (AppUP (VarUP "left") (AppUP (VarUP "right") (VarUP "ab")))) (AppUP (VarUP "recur") (PairUP (AppUP (VarUP "right") (AppUP (VarUP "left") (VarUP "ab"))) (AppUP (VarUP "right") (AppUP (VarUP "right") (VarUP "ab")))))))) (LamUP "ab" (IntUP 0)))] (AppUP (VarUP "fixed") (PairUP (VarUP "a") (VarUP "b"))))))),("filter",LamUP "f" (AppUP (AppUP (VarUP "foldr") (LamUP "a" (LamUP "b" (ITEUP (AppUP (VarUP "f") (VarUP "a")) (PairUP (VarUP "a") (VarUP "b")) (VarUP "b"))))) (IntUP 0))),("dEqual",LamUP "a" (LamUP "b" (LetUP [("equalsOne",LamUP "x" (ITEUP (VarUP "x") (AppUP (VarUP "not") (AppUP (VarUP "left") (VarUP "x"))) (IntUP 0)))] (ITEUP (VarUP "a") (AppUP (VarUP "equalsOne") (AppUP (AppUP (AppUP (VarUP "d2c") (AppUP (VarUP "left") (VarUP "a"))) (LamUP "x" (AppUP (VarUP "left") (VarUP "x")))) (VarUP "b"))) (AppUP (VarUP "not") (VarUP "b")))))),("listLength",AppUP (AppUP (VarUP "foldr") (LamUP "a" (LamUP "b" (AppUP (VarUP "succ") (VarUP "b"))))) (IntUP 0)),("listEqual",LamUP "a" (LamUP "b" (LetUP [("pairsEqual",AppUP (AppUP (AppUP (VarUP "zipWith") (VarUP "dEqual")) (VarUP "a")) (VarUP "b")),("lengthEqual",AppUP (AppUP (VarUP "dEqual") (AppUP (VarUP "listLength") (VarUP "a"))) (AppUP (VarUP "listLength") (VarUP "b")))] (AppUP (AppUP (AppUP (VarUP "foldr") (VarUP "and")) (IntUP 1)) (PairUP (VarUP "lengthEqual") (VarUP "pairsEqual")))))),("listPlus",LamUP "a" (LamUP "b" (AppUP (AppUP (AppUP (VarUP "foldr") (LamUP "x" (LamUP "l" (PairUP (VarUP "x") (VarUP "l"))))) (VarUP "b")) (VarUP "a")))),("concat",AppUP (AppUP (VarUP "foldr") (VarUP "listPlus")) (IntUP 0)),("drop",LamUP "n" (LamUP "l" (AppUP (AppUP (VarUP "n") (LamUP "x" (AppUP (VarUP "right") (VarUP "x")))) (VarUP "l")))),("take",LamUP "n" (LamUP "l" (LetUP [("lengthed",AppUP (AppUP (VarUP "n") (LamUP "x" (PairUP (IntUP 0) (VarUP "x")))) (IntUP 0))] (AppUP (AppUP (AppUP (VarUP "zipWith") (LamUP "a" (LamUP "b" (VarUP "a")))) (VarUP "l")) (VarUP "lengthed"))))),("factorial",LamUP "n" (AppUP (AppUP (AppUP (VarUP "foldr") (LamUP "a" (LamUP "b" (AppUP (AppUP (VarUP "times") (AppUP (VarUP "d2c") (VarUP "a"))) (VarUP "b"))))) (ChurchUP 1)) (AppUP (AppUP (VarUP "range") (IntUP 1)) (PairUP (VarUP "n") (IntUP 0))))),("quicksort",UnsizedRecursionUP (LamUP "l" (AppUP (VarUP "right") (VarUP "l"))) (LamUP "recur" (LamUP "l" (LetUP [("t",AppUP (VarUP "left") (VarUP "l")),("test",LamUP "x" (AppUP (AppUP (VarUP "dMinus") (VarUP "x")) (VarUP "t"))),("p1",AppUP (AppUP (VarUP "filter") (VarUP "test")) (AppUP (VarUP "right") (VarUP "l"))),("p2",AppUP (AppUP (VarUP "filter") (LamUP "x" (AppUP (VarUP "not") (AppUP (VarUP "test") (VarUP "x"))))) (AppUP (VarUP "right") (VarUP "l")))] (AppUP (AppUP (VarUP "listPlus") (AppUP (VarUP "recur") (VarUP "p2"))) (PairUP (VarUP "t") (AppUP (VarUP "recur") (VarUP "p1"))))))) (VarUP "id")),("abort",LamUP "str" (LetUP [("x",CheckUP (LamUP "y" (AppUP (AppUP (VarUP "listPlus") (StringUP "abort: ")) (VarUP "str"))) (IntUP 1))] (VarUP "x"))),("assert",LamUP "t" (LamUP "s" (ITEUP (AppUP (VarUP "not") (VarUP "t")) (PairUP (IntUP 1) (VarUP "s")) (IntUP 0)))),("truncate",LamUP "n" (LetUP [("layer",LamUP "recur" (LamUP "current" (ITEUP (VarUP "current") (PairUP (AppUP (VarUP "recur") (AppUP (VarUP "left") (VarUP "current"))) (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "current")))) (IntUP 0))))] (AppUP (AppUP (VarUP "n") (VarUP "layer")) (LamUP "x" (IntUP 0))))),("main",AppUP (AppUP (AppUP (VarUP "d2c") (IntUP 0)) (VarUP "succ")) (IntUP 0))] (AppUP (AppUP (AppUP (VarUP "d2c") (IntUP 0)) (VarUP "succ")) (IntUP 0)))

-- LetUP [("zero",IntUP 0),("left",LamUP "x" (LeftUP (VarUP "x"))),("right",LamUP "x" (RightUP (VarUP "x"))),("trace",LamUP "x" (TraceUP (VarUP "x"))),("pair",LamUP "x" (LamUP "y" (PairUP (VarUP "x") (VarUP "y")))),("app",LamUP "x" (LamUP "y" (AppUP (VarUP "x") (VarUP "y"))))] (LetUP [("id",LamUP "x" (VarUP "x")),("and",LamUP "a" (LamUP "b" (ITEUP (VarUP "a") (VarUP "b") (IntUP 0)))),("or",LamUP "a" (LamUP "b" (ITEUP (VarUP "a") (IntUP 1) (VarUP "b")))),("not",LamUP "x" (ITEUP (VarUP "x") (IntUP 0) (IntUP 1))),("succ",LamUP "x" (PairUP (VarUP "x") (IntUP 0))),("d2c",UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "i" (LamUP "f" (LamUP "b" (AppUP (VarUP "f") (AppUP (AppUP (AppUP (VarUP "recur") (AppUP (VarUP "left") (VarUP "i"))) (VarUP "f")) (VarUP "b"))))))) (LamUP "i" (LamUP "f" (LamUP "b" (VarUP "b"))))),("c2d",LamUP "c" (AppUP (AppUP (VarUP "c") (VarUP "succ")) (IntUP 0))),("plus",LamUP "m" (LamUP "n" (LamUP "f" (LamUP "x" (AppUP (AppUP (VarUP "m") (VarUP "f")) (AppUP (AppUP (VarUP "n") (VarUP "f")) (VarUP "x"))))))),("times",LamUP "m" (LamUP "n" (LamUP "f" (AppUP (VarUP "m") (AppUP (VarUP "n") (VarUP "f")))))),("pow",LamUP "m" (LamUP "n" (AppUP (VarUP "n") (VarUP "m")))),("dMinus",LamUP "a" (LamUP "b" (AppUP (AppUP (AppUP (VarUP "d2c") (VarUP "b")) (LamUP "x" (AppUP (VarUP "left") (VarUP "x")))) (VarUP "a")))),("minus",LamUP "a" (LamUP "b" (AppUP (VarUP "d2c") (AppUP (AppUP (VarUP "b") (LamUP "x" (AppUP (VarUP "left") (VarUP "x")))) (AppUP (VarUP "c2d") (VarUP "a")))))),("range",LamUP "a" (LamUP "b" (AppUP (UnsizedRecursionUP (LamUP "i" (AppUP (AppUP (VarUP "dMinus") (VarUP "b")) (VarUP "i"))) (LamUP "recur" (LamUP "i" (PairUP (VarUP "i") (AppUP (VarUP "recur") (PairUP (VarUP "i") (IntUP 0)))))) (LamUP "i" (IntUP 0))) (VarUP "a")))),("map",LamUP "f" (UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "l" (PairUP (AppUP (VarUP "f") (AppUP (VarUP "left") (VarUP "l"))) (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "l")))))) (LamUP "l" (IntUP 0)))),("foldr",LamUP "f" (LamUP "b" (LamUP "ta" (LetUP [("fixed",UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "l" (LamUP "accum" (AppUP (AppUP (VarUP "f") (AppUP (VarUP "left") (VarUP "l"))) (AppUP (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "l"))) (VarUP "accum")))))) (LamUP "l" (LamUP "accum" (VarUP "accum"))))] (AppUP (AppUP (VarUP "fixed") (VarUP "ta")) (VarUP "b")))))),("foldl",LamUP "f" (LamUP "b" (LamUP "ta" (LetUP [("fixed",UnsizedRecursionUP (VarUP "id") (LamUP "recur" (LamUP "l" (LamUP "accum" (AppUP (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "l"))) (AppUP (AppUP (VarUP "f") (VarUP "accum")) (AppUP (VarUP "left") (VarUP "l"))))))) (LamUP "l" (LamUP "accum" (VarUP "accum"))))] (AppUP (AppUP (VarUP "fixed") (VarUP "ta")) (VarUP "b")))))),("zipWith",LamUP "f" (LamUP "a" (LamUP "b" (LetUP [("fixed",UnsizedRecursionUP (LamUP "ab" (AppUP (AppUP (VarUP "and") (AppUP (VarUP "left") (VarUP "ab"))) (AppUP (VarUP "right") (VarUP "ab")))) (LamUP "recur" (LamUP "ab" (PairUP (AppUP (AppUP (VarUP "f") (AppUP (VarUP "left") (AppUP (VarUP "left") (VarUP "ab")))) (AppUP (VarUP "left") (AppUP (VarUP "right") (VarUP "ab")))) (AppUP (VarUP "recur") (PairUP (AppUP (VarUP "right") (AppUP (VarUP "left") (VarUP "ab"))) (AppUP (VarUP "right") (AppUP (VarUP "right") (VarUP "ab")))))))) (LamUP "ab" (IntUP 0)))] (AppUP (VarUP "fixed") (PairUP (VarUP "a") (VarUP "b"))))))),("filter",LamUP "f" (AppUP (AppUP (VarUP "foldr") (LamUP "a" (LamUP "b" (ITEUP (AppUP (VarUP "f") (VarUP "a")) (PairUP (VarUP "a") (VarUP "b")) (VarUP "b"))))) (IntUP 0))),("dEqual",LamUP "a" (LamUP "b" (LetUP [("equalsOne",LamUP "x" (ITEUP (VarUP "x") (AppUP (VarUP "not") (AppUP (VarUP "left") (VarUP "x"))) (IntUP 0)))] (ITEUP (VarUP "a") (AppUP (VarUP "equalsOne") (AppUP (AppUP (AppUP (VarUP "d2c") (AppUP (VarUP "left") (VarUP "a"))) (LamUP "x" (AppUP (VarUP "left") (VarUP "x")))) (VarUP "b"))) (AppUP (VarUP "not") (VarUP "b")))))),("listLength",AppUP (AppUP (VarUP "foldr") (LamUP "a" (LamUP "b" (AppUP (VarUP "succ") (VarUP "b"))))) (IntUP 0)),("listEqual",LamUP "a" (LamUP "b" (LetUP [("pairsEqual",AppUP (AppUP (AppUP (VarUP "zipWith") (VarUP "dEqual")) (VarUP "a")) (VarUP "b")),("lengthEqual",AppUP (AppUP (VarUP "dEqual") (AppUP (VarUP "listLength") (VarUP "a"))) (AppUP (VarUP "listLength") (VarUP "b")))] (AppUP (AppUP (AppUP (VarUP "foldr") (VarUP "and")) (IntUP 1)) (PairUP (VarUP "lengthEqual") (VarUP "pairsEqual")))))),("listPlus",LamUP "a" (LamUP "b" (AppUP (AppUP (AppUP (VarUP "foldr") (LamUP "x" (LamUP "l" (PairUP (VarUP "x") (VarUP "l"))))) (VarUP "b")) (VarUP "a")))),("concat",AppUP (AppUP (VarUP "foldr") (VarUP "listPlus")) (IntUP 0)),("drop",LamUP "n" (LamUP "l" (AppUP (AppUP (VarUP "n") (LamUP "x" (AppUP (VarUP "right") (VarUP "x")))) (VarUP "l")))),("take",LamUP "n" (LamUP "l" (LetUP [("lengthed",AppUP (AppUP (VarUP "n") (LamUP "x" (PairUP (IntUP 0) (VarUP "x")))) (IntUP 0))] (AppUP (AppUP (AppUP (VarUP "zipWith") (LamUP "a" (LamUP "b" (VarUP "a")))) (VarUP "l")) (VarUP "lengthed"))))),("factorial",LamUP "n" (AppUP (AppUP (AppUP (VarUP "foldr") (LamUP "a" (LamUP "b" (AppUP (AppUP (VarUP "times") (AppUP (VarUP "d2c") (VarUP "a"))) (VarUP "b"))))) (ChurchUP 1)) (AppUP (AppUP (VarUP "range") (IntUP 1)) (PairUP (VarUP "n") (IntUP 0))))),("quicksort",UnsizedRecursionUP (LamUP "l" (AppUP (VarUP "right") (VarUP "l"))) (LamUP "recur" (LamUP "l" (LetUP [("t",AppUP (VarUP "left") (VarUP "l")),("test",LamUP "x" (AppUP (AppUP (VarUP "dMinus") (VarUP "x")) (VarUP "t"))),("p1",AppUP (AppUP (VarUP "filter") (VarUP "test")) (AppUP (VarUP "right") (VarUP "l"))),("p2",AppUP (AppUP (VarUP "filter") (LamUP "x" (AppUP (VarUP "not") (AppUP (VarUP "test") (VarUP "x"))))) (AppUP (VarUP "right") (VarUP "l")))] (AppUP (AppUP (VarUP "listPlus") (AppUP (VarUP "recur") (VarUP "p2"))) (PairUP (VarUP "t") (AppUP (VarUP "recur") (VarUP "p1"))))))) (VarUP "id")),("abort",LamUP "str" (LetUP [("x",CheckUP (LamUP "y" (AppUP (AppUP (VarUP "listPlus") (StringUP "abort: ")) (VarUP "str"))) (IntUP 1))] (VarUP "x"))),("assert",LamUP "t" (LamUP "s" (ITEUP (AppUP (VarUP "not") (VarUP "t")) (PairUP (IntUP 1) (VarUP "s")) (IntUP 0)))),("truncate",LamUP "n" (LetUP [("layer",LamUP "recur" (LamUP "current" (ITEUP (VarUP "current") (PairUP (AppUP (VarUP "recur") (AppUP (VarUP "left") (VarUP "current"))) (AppUP (VarUP "recur") (AppUP (VarUP "right") (VarUP "current")))) (IntUP 0))))] (AppUP (AppUP (VarUP "n") (VarUP "layer")) (LamUP "x" (IntUP 0))))),("main",AppUP (AppUP (AppUP (VarUP "d2c") (IntUP 0)) (VarUP "succ")) (IntUP 0))] (AppUP (AppUP (AppUP (VarUP "d2c") (IntUP 0)) (VarUP "succ")) (IntUP 0)))

-- aux1 =
--   SetEnvF
--     PairF
--       DeferF FragIndex {unFragIndex = 158}
--       PairF
--         PairF
--           DeferF FragIndex {unFragIndex = 165}
--           ZeroF
--         PairF
--           PairF
--             DeferF FragIndex {unFragIndex = 308}
--             ZeroF
--           PairF
--             PairF
--               AuxF RecursionTest
--                    (FragExprUR {unFragExprUR = (1,1) :< DeferFragF (FragIndex {unFragIndex = 309})})
--               ZeroF
--             ZeroF




-- SetEnvF
--   PairF
--     DeferF FragIndex {unFragIndex = 15}
--     PairF
--       PairF
--         DeferF FragIndex {unFragIndex = 18}
--         ZeroF
--       PairF
--         PairF
--           DeferF FragIndex {unFragIndex = 28}
--           ZeroF
--         PairF
--           PairF
--             AuxF RecursionTest (FragExprUR {unFragExprUR = DeferF FragIndex {unFragIndex = 29}})
--             ZeroF
--           ZeroF








-- |`makeLambda ps vl t1` makes a `TLam` around `t1` with `vl` as arguments.
-- Automatic recognition of Close or Open type of `TLam`.
makeLambda :: [(String, AnnotatedUPT)] -- ^Bindings
           -> String                            -- ^Variable name
           -> Term1                             -- ^Lambda body
           -> Term1
makeLambda bindings str term1@(anno :< _) =
  if unbound == Set.empty then anno :< TLamF (Closed str) term1 else anno :< TLamF (Open str) term1
  where bindings' = Set.fromList $ fst <$> bindings
        v = varsTerm1 term1
        unbound = (v \\ bindings') \\ Set.singleton str

-- |Transformation from `AnnotatedUPT` to `Term1` validating and inlining `VarUP`s
validateVariables :: [(String, AnnotatedUPT)] -- ^ Prelude
                  -> AnnotatedUPT
                  -> Either String Term1
validateVariables prelude term =
  let validateWithEnvironment :: AnnotatedUPT
                              -> State.StateT (Map String Term1) (Either String) Term1
      validateWithEnvironment = \case
        anno :< LamUPF v x -> do
          oldState <- State.get
          State.modify (Map.insert v (anno :< TVarF v))
          result <- validateWithEnvironment x
          State.put oldState
          pure $ makeLambda prelude v result
        anno :< VarUPF n -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _      -> State.lift . Left  $ "No definition found for " <> n
        anno :< LetUPF preludeMap inner -> do
          oldPrelude <- State.get
          let addBinding (k,v) = do
                newTerm <- validateWithEnvironment v
                State.modify (Map.insert k newTerm)
          mapM_ addBinding preludeMap
          result <- validateWithEnvironment inner
          State.put oldPrelude
          pure result
        anno :< ITEUPF i t e -> (\a b c -> anno :< TITEF a b c) <$> validateWithEnvironment i
                                                                <*> validateWithEnvironment t
                                                                <*> validateWithEnvironment e
        anno :< IntUPF x -> pure $ i2t anno x
        anno :< StringUPF s -> pure $ s2t anno s
        anno :< PairUPF a b -> (\x y -> anno :< TPairF x y) <$> validateWithEnvironment a
                                                            <*> validateWithEnvironment b
        anno :< ListUPF l -> foldr (\x y -> anno :< TPairF x y) (anno :< TZeroF) <$> mapM validateWithEnvironment l
        anno :< AppUPF f x -> (\a b -> anno :< TAppF a b) <$> validateWithEnvironment f
                                                          <*> validateWithEnvironment x
        anno :< UnsizedRecursionUPF t r b ->
          (\x y z -> anno :< TLimitedRecursionF x y z) <$> validateWithEnvironment t
                                                       <*> validateWithEnvironment r
                                                       <*> validateWithEnvironment b
        anno :< ChurchUPF n -> pure $ i2c anno n
        anno :< LeftUPF x -> (\y -> anno :< TLeftF y) <$> validateWithEnvironment x
        anno :< RightUPF x -> (\y -> anno :< TRightF y) <$> validateWithEnvironment x
        anno :< TraceUPF x -> (\y -> anno :< TTraceF y) <$> validateWithEnvironment x
        anno :< CheckUPF cf x -> (\y y'-> anno :< TCheckF y y') <$> validateWithEnvironment cf <*> validateWithEnvironment x
        anno :< HashUPF x -> (\y -> anno :< THashF y) <$> validateWithEnvironment x
  -- in State.evalStateT (validateWithEnvironment (traceShow (forget term :: UnprocessedParsedTerm) term)) Map.empty
  in State.evalStateT (validateWithEnvironment term) Map.empty

-- |Collect all free variable names in a `Term1` expresion
varsTerm1 :: Term1 -> Set String
varsTerm1 = cata alg where
  alg :: CofreeF (ParserTermF String String) a (Set String) -> Set String
  alg (_ C.:< (TVarF n))          = Set.singleton n
  alg (_ C.:< TLamF (Open n) x)   = del n x
  alg (_ C.:< TLamF (Closed n) x) = del n x
  alg e                           = F.fold e
  del :: String -> Set String -> Set String
  del n x = if Set.member n x then Set.delete n x else x

-- (0,0) :<  AppUPF ((1,27) :< VarUPF "a") ((1,33) :< AppUPF ((1,34) :< VarUPF "left") ((1,39) :< VarUPF "i"))

optimizeBuiltinFunctions :: AnnotatedUPT -> AnnotatedUPT
optimizeBuiltinFunctions = transform optimize where
  optimize = \case
    twoApp@(anno0 :< AppUPF (_ :< AppUPF (_ :< f) x) y) ->
      case f of
        VarUPF "pair" -> anno0 :< PairUPF x y
        VarUPF "app"  -> anno0 :< AppUPF x y
        _             -> twoApp
    oneApp@(anno0 :< AppUPF (anno1 :< f) x) ->
      case f of
        VarUPF "left"  -> anno0 :< LeftUPF x
        VarUPF "right" -> anno0 :< RightUPF x
        VarUPF "trace" -> anno0 :< TraceUPF x
        VarUPF "pair"  -> anno0 :< LamUPF "y" (anno1 :< PairUPF x (anno1 :< VarUPF "y"))
        VarUPF "app"   -> anno0 :< LamUPF "y" (anno1 :< AppUPF x (anno1 :< VarUPF "y"))
        _             -> oneApp
        -- VarUP "check" TODO
    x -> x

-- |Process an `Term2` to have all `HashUP` replaced by a unique number.
-- The unique number is constructed by doing a SHA1 hash of the Term2 and
-- adding one for all consecutive HashUP's.
generateAllHashes :: Term2 -> Term2
generateAllHashes x@(anno :< _) = transform interm x where
  hash' :: ByteString -> Digest SHA256
  hash' = hash
  term2Hash :: Term2 -> ByteString
  term2Hash = BS.pack . BA.unpack . hash' . BS.pack . encode . show
  bs2Term2 :: ByteString -> Term2
  bs2Term2 bs = ints2t anno . drop 24 $ fromInteger . toInteger <$> BS.unpack bs
  interm :: Term2 -> Term2
  interm = \case
    (anno :< THashF term1) -> bs2Term2 . term2Hash $ term1
    x                      -> x

-- data Annotation = Dummy
--                 | Pos Int Int

addBuiltins :: AnnotatedUPT -> AnnotatedUPT
addBuiltins aupt = (0,0) :< LetUPF
  [ ("zero", (0,0) :< IntUPF 0)
  , ("left", (0,0) :< LamUPF "x" ((0,0) :< LeftUPF ((0,0) :< VarUPF "x")))
  , ("right", (0,0) :< LamUPF "x" ((0,0) :< RightUPF ((0,0) :< VarUPF "x")))
  , ("trace", (0,0) :< LamUPF "x" ((0,0) :< TraceUPF ((0,0) :< VarUPF "x")))
  , ("pair", (0,0) :< LamUPF "x" ((0,0) :< LamUPF "y" ((0,0) :< PairUPF ((0,0) :< VarUPF "x") ((0,0) :< VarUPF "y"))))
  , ("app", (0,0) :< LamUPF "x" ((0,0) :< LamUPF "y" ((0,0) :< AppUPF ((0,0) :< VarUPF "x") ((0,0) :< VarUPF "y"))))
  ]
  aupt

-- forgetTerm3 :: Term3 -> Map FragIndex Telomare.FragExprURSansAnnotation
forgetTerm3 t3@(Term3 x) = forgetAnnotationFragExprUR <$> x

-- |Process an `AnnotatedUPT` to a `Term3` with failing capability.
process :: [(String, AnnotatedUPT)] -- ^Prelude
        -> AnnotatedUPT
        -> Either String Term3
process prelude upt = let aux = splitExpr <$> process2Term2 prelude upt
                      in aux -- trace (show $ forgetTerm3 <$> aux) aux

process2Term2 :: [(String, AnnotatedUPT)] -- ^Prelude
              -> AnnotatedUPT
              -> Either String Term2
process2Term2 prelude = fmap generateAllHashes
                      . debruijinize [] <=< validateVariables prelude
                      . removeCaseUPs
                      . optimizeBuiltinFunctions
                      -- . (\x -> traceShow (forget x :: UnprocessedParsedTerm) x)
                      . addBuiltins

-- |Helper function to compile to Term2
runTelomareParser2Term2 :: TelomareParser AnnotatedUPT -- ^Parser to run
                        -> [(String, AnnotatedUPT)]    -- ^Prelude
                        -> String                               -- ^Raw string to be parsed
                        -> Either String Term2                  -- ^Error on Left
runTelomareParser2Term2 parser prelude str =
  first errorBundlePretty (runParser parser "" str) >>= process2Term2 prelude

parseMain :: [(String, AnnotatedUPT)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either String Term3               -- ^Error on Left.
parseMain prelude s = parseWithPrelude prelude s >>= process prelude

-- (FragIndex {unFragIndex = 7},
-- SetEnvFrag
--   PairFrag
--     GateFrag
--       SetEnvFrag
--         SetEnvFrag
--           PairFrag
--             DeferFrag FragIndex {unFragIndex = 3}
--             PairFrag
--               LeftFrag
--                 EnvFrag
--               LeftFrag
--                 RightFrag
--                   RightFrag
--                     RightFrag
--                       RightFrag
--                         EnvFrag
--       SetEnvFrag
--         SetEnvFrag
--           PairFrag
--             DeferFrag FragIndex {unFragIndex = 4}
--             PairFrag
--               LeftFrag
--                 EnvFrag
--               SetEnvFrag
--                 SetEnvFrag
--                   PairFrag
--                     DeferFrag FragIndex {unFragIndex = 5}
--                     PairFrag
--                       LeftFrag
--                         RightFrag
--                           EnvFrag
--                       LeftFrag
--                         RightFrag
--                           RightFrag
--                             RightFrag
--                               EnvFrag
--     SetEnvFrag
--       SetEnvFrag
--         PairFrag
--           DeferFrag FragIndex {unFragIndex = 6}
--           PairFrag
--             LeftFrag
--               EnvFrag
--             LeftFrag
--               RightFrag
--                 RightFrag
--                   EnvFrag)


-- foo =
--   (FragIndex {unFragIndex = 7},SetEnvFrag
--   PairFrag
--     GateFrag
--       SetEnvFrag
--         SetEnvFrag
--           PairFrag
--             DeferFrag FragIndex {unFragIndex = 3}
--             PairFrag
--               LeftFrag
--                 EnvFrag
--               LeftFrag
--                 RightFrag
--                   RightFrag
--                     RightFrag
--                       RightFrag
--                         EnvFrag
--       SetEnvFrag
--         SetEnvFrag
--           PairFrag
--             DeferFrag FragIndex {unFragIndex = 4}
--             PairFrag
--               LeftFrag
--                 EnvFrag
--               SetEnvFrag
--                 SetEnvFrag
--                   PairFrag
--                     DeferFrag FragIndex {unFragIndex = 5}
--                     PairFrag
--                       LeftFrag
--                         RightFrag
--                           EnvFrag
--                       LeftFrag
--                         RightFrag
--                           RightFrag
--                             RightFrag
--                               EnvFrag
--     SetEnvFrag
--       SetEnvFrag
--         PairFrag
--           DeferFrag FragIndex {unFragIndex = 6}
--           PairFrag
--             LeftFrag
--               EnvFrag
--             LeftFrag
--               RightFrag
--                 RightFrag
--                   EnvFrag)
