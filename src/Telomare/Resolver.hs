{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.Resolver where

import Codec.Binary.UTF8.String (encode)
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
import PrettyPrint (TypeDebugInfo (..), showTypeDebugInfo, prettyPrint)
import Telomare (BreakState', DataType (..), FragExpr (..), FragExprF (..),
                 FragExprUR (..), FragIndex (..), IExpr (..), IExprF (..),
                 LamType (..), LocTag (..), ParserTerm (..), ParserTermF (..),
                 PartialType (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..), Term1 (..), Term2 (..),
                 Term3 (..), UnsizedRecursionToken, appF, clamF, deferF, forget,
                 forgetAnnotationFragExprUR, gateF, i2cF, lamF, nextBreakToken, pairF,
                 setEnvF, showRunBreakState', tag, unsizedRecursionWrapper,
                 varNF)
import Telomare.Parser (AnnotatedUPT, Pattern (..), PatternF (..),
                        PrettyUPT (..), TelomareParser (..),
                        UnprocessedParsedTerm (..), UnprocessedParsedTermF (..),
                        parseWithPrelude)
import Text.Megaparsec (errorBundlePretty, runParser)

debug :: Bool
debug = True

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

type VarList = [String]

-- |Int to ParserTerm
i2t :: LocTag -> Int -> Cofree (ParserTermF l v) LocTag
i2t anno = ana coalg where
  coalg :: Int -> CofreeF (ParserTermF l v) LocTag Int
  coalg 0 = anno C.:< TZeroF
  coalg n = anno C.:< TPairF (n-1) 0

-- |List of Int's to ParserTerm
ints2t :: LocTag ->  [Int] -> Cofree (ParserTermF l v) LocTag
ints2t anno = foldr ((\x y -> anno :< TPairF x y) . i2t anno) (anno :< TZeroF)

-- |String to ParserTerm
s2t :: LocTag -> String -> Cofree (ParserTermF l v) LocTag
s2t anno = ints2t anno . fmap ord

-- |Int to Church encoding
{-
i2c :: LocTag -> Int -> Term1
i2c anno x = anno :< TLamF (Closed "f") (anno :< TLamF (Open "x") (inner x))
  where inner :: Int -> Term1
        inner = apo coalg
        coalg :: Int -> Base Term1 (Either Term1 Int)
        coalg 0 = anno C.:< TVarF "x"
        coalg n = anno C.:< TAppF (Left . (anno :<) . TVarF $ "f") (Right $ n - 1)
-}

instance MonadFail (Either String) where
  fail = Left

-- | Finds all PatternInt leaves returning "directions" to these leaves through pairs
-- in the form of a combination of RightUP and LeftUP from the root
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) (PatternVar "y"))
--      will return [LeftUP . RightUP]
findInts :: LocTag -> Pattern -> [AnnotatedUPT -> AnnotatedUPT]
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
findStrings :: LocTag -> Pattern -> [AnnotatedUPT -> AnnotatedUPT]
findStrings anno = cata alg where
  alg :: Base Pattern [AnnotatedUPT -> AnnotatedUPT]
      -> [AnnotatedUPT -> AnnotatedUPT]
  alg = \case
    PatternPairF x y -> ((. (anno :< ) . LeftUPF) <$> x) <> ((. (anno :< ) . RightUPF) <$> y)
    PatternStringF x -> [id]
    _                -> []

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

mkLambda4FreeVarUPs :: AnnotatedUPT -> AnnotatedUPT
mkLambda4FreeVarUPs aupt@(anno :< _) = tag anno $ go upt freeVars where
  upt = forget aupt
  freeVars = Set.toList . varsUPT $ upt
  go :: UnprocessedParsedTerm -> [String] -> UnprocessedParsedTerm
  go x = \case
    []     -> x
    (y:ys) -> LamUP y $ go x ys

findPatternVars :: LocTag -> Pattern -> Map String (AnnotatedUPT -> AnnotatedUPT)
findPatternVars anno = cata alg where
  alg :: Base Pattern (Map String (AnnotatedUPT -> AnnotatedUPT))
      -> Map String (AnnotatedUPT -> AnnotatedUPT)
  alg = \case
    PatternPairF x y -> ((. (anno :< ). LeftUPF) <$> x) <> ((. (anno :< ). RightUPF) <$> y)
    PatternVarF str  -> Map.singleton str id
    _                -> Map.empty

-- TODO: Annotate without so much fuzz
pairStructureCheck :: Pattern -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pairStructureCheck p upt =
  AppUP (AppUP (AppUP (VarUP "foldl")
                      (VarUP "and"))
               (IntUP 1))
        (ListUP $ ($ upt) <$> pairRoute2Dirs p)

pairRoute2Dirs :: Pattern -> [UnprocessedParsedTerm -> UnprocessedParsedTerm]
pairRoute2Dirs = cata alg where
  alg :: Base Pattern [UnprocessedParsedTerm -> UnprocessedParsedTerm]
      -> [UnprocessedParsedTerm -> UnprocessedParsedTerm]
  alg = \case
    PatternPairF x y -> [id] <> ((. LeftUP) <$> x) <> ((. RightUP) <$> y)
    _                -> []

pattern2UPT :: LocTag -> Pattern -> AnnotatedUPT
pattern2UPT anno = tag anno . cata alg where
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

case2annidatedIfs :: AnnotatedUPT -- ^ Term to be pattern matched
                  -> [Pattern] -- ^ All patterns in a case expression
                  -> [AnnotatedUPT] -- ^ Int leaves as ListUPs on UPT
                  -> [AnnotatedUPT] -- ^ Int leaves as ListUPs on pattern
                  -> [AnnotatedUPT] -- ^ String leaves as ListUPs on UPT
                  -> [AnnotatedUPT] -- ^ String leaves as ListUPs on pattern
                  -> [AnnotatedUPT] -- ^ Case's alternatives
                  -> AnnotatedUPT
case2annidatedIfs (anno :< _) [] [] [] [] [] [] = tag anno $
  ITEUP (IntUP 1)
        (AppUP (VarUP "abort") $ StringUP "Non-exhaustive patterns in case")
        (IntUP 0)
case2annidatedIfs x (aPattern:as) ((_ :< ListUPF []) : bs) ((_ :< ListUPF []) :cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
  tag anno $
    ITEUP (AppUP (AppUP (VarUP "and")
                        (AppUP (AppUP (VarUP "listEqual") (forget dirs2StringOnUPT)) (forget dirs2StringOnPattern)))
                 (pairStructureCheck aPattern (forget x)))
          (forget $ mkCaseAlternative x resultAlternative aPattern)
          (forget $ case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) ((_ :< ListUPF []) : ds) ((_ :< ListUPF []) : es) (resultAlternative@(anno :< _):fs) =
  tag anno $
    ITEUP (AppUP (AppUP (VarUP "and")
                        (AppUP (AppUP (VarUP "listEqual") (forget dirs2IntOnUPT)) (forget dirs2IntOnPattern)))
                 (pairStructureCheck aPattern (forget x)))
          (forget $ mkCaseAlternative x resultAlternative aPattern)
          (forget $ case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
  tag anno $
    ITEUP (AppUP (AppUP (AppUP (VarUP "foldl")
                                (VarUP "and"))
                        (IntUP 1))
                 (ListUP [ AppUP (AppUP (VarUP "listEqual") (forget dirs2IntOnUPT)) (forget dirs2IntOnPattern)
                         , AppUP (AppUP (VarUP "listEqual") (forget dirs2StringOnUPT)) (forget dirs2StringOnPattern)
                         , pairStructureCheck aPattern (forget x)
                         ]))
          (forget $ mkCaseAlternative x resultAlternative aPattern)
          (forget $ case2annidatedIfs x as bs cs ds es fs)
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
  (anno :< TChurchF n) -> pure $ anno :< TChurchF n
  (anno :< TLimitedRecursionF t r b) -> (\x y z -> anno :< TLimitedRecursionF x y z) <$> debruijinize vl t <*> debruijinize vl r <*> debruijinize vl b

rewriteOuterTag :: anno -> Cofree a anno -> Cofree a anno
rewriteOuterTag anno (_ :< x) = anno :< x

splitExpr' :: Term2 -> BreakState' RecursionPieceFrag UnsizedRecursionToken
splitExpr' = \case
  (anno :< TZeroF) -> pure (anno :< ZeroFragF)
  (anno :< TPairF a b) -> rewriteOuterTag anno <$> pairF (splitExpr' a) (splitExpr' b)
  (anno :< TVarF n) -> pure . tag anno $ varNF n
  (anno :< TAppF c i) ->
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
  (anno :< TChurchF n) -> i2cF anno n
  (anno :< TLimitedRecursionF t r b) ->
    rewriteOuterTag anno <$> (nextBreakToken >>=
      (\x -> unsizedRecursionWrapper x (splitExpr' t) (splitExpr' r) (splitExpr' b)))

newtype FragExprUR' =
  FragExprUR' { unFragExprUR' :: FragExpr (RecursionSimulationPieces FragExprUR')
              }
  deriving (Eq, Show)

newtype Term3' = Term3' (Map FragIndex FragExprUR') deriving (Eq, Show)

splitExpr :: Term2 -> Term3
splitExpr t = let (bf, (_,_,m)) = State.runState (splitExpr' t) (toEnum 0, FragIndex 1, Map.empty)
              in Term3 . Map.map FragExprUR $ Map.insert (FragIndex 0) bf m


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
        -- anno :< ChurchUPF n -> pure $ i2c anno n
        anno :< ChurchUPF n -> pure $ anno :< TChurchF n
        anno :< LeftUPF x -> (\y -> anno :< TLeftF y) <$> validateWithEnvironment x
        anno :< RightUPF x -> (\y -> anno :< TRightF y) <$> validateWithEnvironment x
        anno :< TraceUPF x -> (\y -> anno :< TTraceF y) <$> validateWithEnvironment x
        anno :< CheckUPF cf x -> (\y y'-> anno :< TCheckF y y') <$> validateWithEnvironment cf <*> validateWithEnvironment x
        anno :< HashUPF x -> (\y -> anno :< THashF y) <$> validateWithEnvironment x
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
  term2Hash = BS.pack . BA.unpack . hash' . BS.pack . encode . show . (forget :: Cofree (ParserTermF () Int) LocTag -> ParserTerm () Int)
  bs2Term2 :: ByteString -> Term2
  bs2Term2 bs = ints2t anno . drop 24 $ fromInteger . toInteger <$> BS.unpack bs
  interm :: Term2 -> Term2
  interm = \case
    (anno :< THashF term1) -> bs2Term2 . term2Hash $ term1
    x                      -> x

addBuiltins :: AnnotatedUPT -> AnnotatedUPT
addBuiltins aupt = DummyLoc :< LetUPF
  [ ("zero", DummyLoc :< IntUPF 0)
  , ("left", DummyLoc :< LamUPF "x" (DummyLoc :< LeftUPF (DummyLoc :< VarUPF "x")))
  , ("right", DummyLoc :< LamUPF "x" (DummyLoc :< RightUPF (DummyLoc :< VarUPF "x")))
  , ("trace", DummyLoc :< LamUPF "x" (DummyLoc :< TraceUPF (DummyLoc :< VarUPF "x")))
  , ("pair", DummyLoc :< LamUPF "x" (DummyLoc :< LamUPF "y" (DummyLoc :< PairUPF (DummyLoc :< VarUPF "x") (DummyLoc :< VarUPF "y"))))
  , ("app", DummyLoc :< LamUPF "x" (DummyLoc :< LamUPF "y" (DummyLoc :< AppUPF (DummyLoc :< VarUPF "x") (DummyLoc :< VarUPF "y"))))
  ]
  aupt

-- |Process an `AnnotatedUPT` to a `Term3` with failing capability.
process :: [(String, AnnotatedUPT)] -- ^Prelude
        -> AnnotatedUPT
        -> Either String Term3
process prelude upt = (\dt -> debugTrace ("Resolver process term:\n" <> prettyPrint dt) dt) . splitExpr <$> process2Term2 prelude upt

process2Term2 :: [(String, AnnotatedUPT)] -- ^Prelude
              -> AnnotatedUPT
              -> Either String Term2
process2Term2 prelude = fmap generateAllHashes
                      . debruijinize [] <=< validateVariables prelude
                      . removeCaseUPs
                      . optimizeBuiltinFunctions
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
