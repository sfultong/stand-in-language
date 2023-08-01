{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

-- |

module Telomare.Resolver where

import Codec.Binary.UTF8.String (encode)
import Control.Lens.Combinators (transform)
import Control.Monad ((<=<))
import qualified Control.Monad.State as State
import Crypto.Hash (Digest, SHA256, hash)
import Data.Bifunctor (Bifunctor (first))
import qualified Data.ByteArray as BA
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (ord)
import qualified Data.Foldable as F
import Data.Functor.Foldable (Base, Corecursive (ana, apo), Recursive (cata))
import Data.List (delete, elem, elemIndex)
import Data.Map (Map, fromList, toList)
import qualified Data.Map as Map
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Telomare (BreakState', FragExpr (..), FragExprUR (..), FragIndex (..),
                 IExpr (..), LamType (..), ParserTerm (..), ParserTermF (..),
                 RecursionPieceFrag, RecursionSimulationPieces (..), Term1 (..),
                 Term2 (..), Term3 (..), UnsizedRecursionToken, appF, clamF,
                 deferF, lamF, nextBreakToken, unsizedRecursionWrapper, varNF)
import Telomare.Parser (TelomareParser (..), UnprocessedParsedTerm (..),
                        parseWithPrelude)
import Text.Megaparsec (errorBundlePretty, runParser)


type VarList = [String]

-- |Int to ParserTerm
i2t :: Int -> ParserTerm l v
i2t = ana coalg where
  coalg :: Int -> Base (ParserTerm l v) Int
  coalg 0 = TZeroF
  coalg n = TPairF (n-1) 0

-- |List of Int's to ParserTerm
ints2t :: [Int] -> ParserTerm l v
ints2t = foldr (TPair . i2t) TZero

-- |String to ParserTerm
s2t :: String -> ParserTerm l v
s2t = ints2t . fmap ord

-- |Int to Church encoding
i2c :: Int -> Term1
i2c x = TLam (Closed "f") (TLam (Open "x") (inner x))
  where inner :: Int -> Term1
        inner = apo coalg
        coalg :: Int -> Base Term1 (Either Term1 Int)
        coalg 0 = TVarF "x"
        coalg n = TAppF (Left . TVar $ "f") (Right $ n - 1)

instance MonadFail (Either String) where
  fail = Left

debruijinize :: MonadFail m => VarList -> Term1 -> m Term2
debruijinize _ TZero = pure TZero
debruijinize vl (TPair a b) = TPair <$> debruijinize vl a <*> debruijinize vl b
debruijinize vl (TVar n) = case elemIndex n vl of
                             Just i  -> pure $ TVar i
                             Nothing -> fail ("undefined identifier " <> n)
debruijinize vl (TApp i c) = TApp <$> debruijinize vl i <*> debruijinize vl c
debruijinize vl (TCheck c tc) = TCheck <$> debruijinize vl c <*> debruijinize vl tc
debruijinize vl (TITE i t e) = TITE <$> debruijinize vl i
                                    <*> debruijinize vl t
                                    <*> debruijinize vl e
debruijinize vl (TLeft x) = TLeft <$> debruijinize vl x
debruijinize vl (TRight x) = TRight <$> debruijinize vl x
debruijinize vl (TTrace x) = TTrace <$> debruijinize vl x
debruijinize vl (THash x) = THash <$> debruijinize vl x
debruijinize vl (TLam (Open n) x) = TLam (Open ()) <$> debruijinize (n : vl) x
debruijinize vl (TLam (Closed n) x) = TLam (Closed ()) <$> debruijinize (n : vl) x
debruijinize vl (TLimitedRecursion t r b) = TLimitedRecursion <$> debruijinize vl t <*> debruijinize vl r <*> debruijinize vl b

splitExpr' :: Term2 -> BreakState' RecursionPieceFrag UnsizedRecursionToken
splitExpr' = \case
  TZero -> pure ZeroFrag
  TPair a b -> PairFrag <$> splitExpr' a <*> splitExpr' b
  TVar n -> pure $ varNF n
  TApp c i -> appF (splitExpr' c) (splitExpr' i)
  TCheck tc c ->
    let performTC = deferF ((\ia -> SetEnvFrag (PairFrag (SetEnvFrag (PairFrag AbortFrag ia)) (RightFrag EnvFrag))) <$> appF (pure $ LeftFrag EnvFrag) (pure $ RightFrag EnvFrag))
    in (\ptc nc ntc -> SetEnvFrag (PairFrag ptc (PairFrag ntc nc))) <$> performTC <*> splitExpr' c <*> splitExpr' tc
  TITE i t e -> (\ni nt ne -> SetEnvFrag (PairFrag (GateFrag ne nt) ni)) <$> splitExpr' i <*> splitExpr' t <*> splitExpr' e
  TLeft x -> LeftFrag <$> splitExpr' x
  TRight x -> RightFrag <$> splitExpr' x
  TTrace x -> (\tf nx -> SetEnvFrag (PairFrag tf nx)) <$> deferF (pure TraceFrag) <*> splitExpr' x
  TLam (Open ()) x -> lamF $ splitExpr' x
  TLam (Closed ()) x -> clamF $ splitExpr' x
  TLimitedRecursion t r b -> nextBreakToken >>= (\x -> unsizedRecursionWrapper x (splitExpr' t) (splitExpr' r) (splitExpr' b))

splitExpr :: Term2 -> Term3
splitExpr t = let (bf, (_,_,m)) = State.runState (splitExpr' t) (toEnum 0, FragIndex 1, Map.empty)
              in Term3 . Map.map FragExprUR $ Map.insert (FragIndex 0) bf m

-- |`makeLambda ps vl t1` makes a `TLam` around `t1` with `vl` as arguments.
-- Automatic recognition of Close or Open type of `TLam`.
makeLambda :: [(String, UnprocessedParsedTerm)] -- ^Bindings
           -> String                            -- ^Variable name
           -> Term1                             -- ^Lambda body
           -> Term1
makeLambda bindings str term1 =
  if unbound == Set.empty then TLam (Closed str) term1 else TLam (Open str) term1
  where bindings' = Set.fromList $ fst <$> bindings
        v = vars term1
        unbound = (v \\ bindings') \\ Set.singleton str

-- |Transformation from `UnprocessedParsedTerm` to `Term1` validating and inlining `VarUP`s
validateVariables :: [(String, UnprocessedParsedTerm)] -- ^ Prelude
                  -> UnprocessedParsedTerm
                  -> Either String Term1
validateVariables prelude term =
  let validateWithEnvironment :: UnprocessedParsedTerm
                              -> State.StateT (Map String Term1) (Either String) Term1
      validateWithEnvironment = \case
        LamUP v x -> do
          oldState <- State.get
          State.modify (Map.insert v (TVar v))
          result <- validateWithEnvironment x
          State.put oldState
          pure $ makeLambda prelude v result
        VarUP n -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _      -> State.lift . Left  $ "No definition found for " <> n
        LetUP preludeMap inner -> do
          oldPrelude <- State.get
          let addBinding (k,v) = do
                newTerm <- validateWithEnvironment v
                State.modify (Map.insert k newTerm)
          mapM_ addBinding preludeMap
          result <- validateWithEnvironment inner
          State.put oldPrelude
          pure result
        ITEUP i t e -> TITE <$> validateWithEnvironment i
                            <*> validateWithEnvironment t
                            <*> validateWithEnvironment e
        IntUP x -> pure $ i2t x
        StringUP s -> pure $ s2t s
        PairUP a b -> TPair <$> validateWithEnvironment a
                            <*> validateWithEnvironment b
        ListUP l -> foldr TPair TZero <$> mapM validateWithEnvironment l
        AppUP f x -> TApp <$> validateWithEnvironment f
                          <*> validateWithEnvironment x
        UnsizedRecursionUP t r b -> TLimitedRecursion <$> validateWithEnvironment t
          <*> validateWithEnvironment r <*> validateWithEnvironment b
        ChurchUP n -> pure $ i2c n
        LeftUP x -> TLeft <$> validateWithEnvironment x
        RightUP x -> TRight <$> validateWithEnvironment x
        TraceUP x -> TTrace <$> validateWithEnvironment x
        CheckUP cf x -> TCheck <$> validateWithEnvironment cf <*> validateWithEnvironment x
        HashUP x -> THash <$> validateWithEnvironment x
  in State.evalStateT (validateWithEnvironment term) Map.empty

-- |Collect all variable names in a `Term1` expresion excluding terms binded
--  to lambda args
vars :: Term1 -> Set String
vars = cata alg where
  alg :: Base Term1 (Set String) -> Set String
  alg (TVarF n)            = Set.singleton n
  alg (TLamF (Open n) x)   = del n x
  alg (TLamF (Closed n) x) = del n x
  alg e                    = F.fold e
  del :: String -> Set String -> Set String
  del n x = if Set.member n x then Set.delete n x else x

optimizeBuiltinFunctions :: UnprocessedParsedTerm -> UnprocessedParsedTerm
optimizeBuiltinFunctions = transform optimize where
  optimize = \case
    twoApp@(AppUP (AppUP f x) y) ->
      case f of
        VarUP "pair" -> PairUP x y
        VarUP "app"  -> AppUP x y
        _            -> twoApp
    oneApp@(AppUP f x) ->
      case f of
        VarUP "left"  -> LeftUP x
        VarUP "right" -> RightUP x
        VarUP "trace" -> TraceUP x
        VarUP "pair"  -> LamUP "y" (PairUP x . VarUP $ "y")
        VarUP "app"   -> LamUP "y" (AppUP x . VarUP $ "y")
        _             -> oneApp
        -- VarUP "check" TODO
    x -> x

-- |Process an `Term2` to have all `HashUP` replaced by a unique number.
-- The unique number is constructed by doing a SHA1 hash of the Term2 and
-- adding one for all consecutive HashUP's.
generateAllHashes :: Term2 -> Term2
generateAllHashes = transform interm where
  hash' :: ByteString -> Digest SHA256
  hash' = hash
  term2Hash :: Term2 -> ByteString
  term2Hash = BS.pack . BA.unpack . hash' . BS.pack . encode . show
  bs2Term2 :: ByteString -> Term2
  bs2Term2 bs = ints2t . drop 24 $ fromInteger . toInteger <$> BS.unpack bs
  interm :: Term2 -> Term2
  interm = \case
    THash term1 -> bs2Term2 . term2Hash $ term1
    x           -> x

addBuiltins :: UnprocessedParsedTerm -> UnprocessedParsedTerm
addBuiltins = LetUP
  [ ("zero", IntUP 0)
  , ("left", LamUP "x" (LeftUP (VarUP "x")))
  , ("right", LamUP "x" (RightUP (VarUP "x")))
  , ("trace", LamUP "x" (TraceUP (VarUP "x")))
  , ("pair", LamUP "x" (LamUP "y" (PairUP (VarUP "x") (VarUP "y"))))
  , ("app", LamUP "x" (LamUP "y" (AppUP (VarUP "x") (VarUP "y"))))
  ]

-- |Process an `UnprocessedParsedTerm` to a `Term3` with failing capability.
process :: [(String, UnprocessedParsedTerm)] -- ^Prelude
        -> UnprocessedParsedTerm
        -> Either String Term3
process prelude upt = splitExpr <$> process2Term2 prelude upt

process2Term2 :: [(String, UnprocessedParsedTerm)] -- ^Prelude
              -> UnprocessedParsedTerm
              -> Either String Term2
process2Term2 prelude = fmap generateAllHashes
                      . debruijinize [] <=< validateVariables prelude
                      . optimizeBuiltinFunctions
                      . addBuiltins

-- |Helper function to compile to Term2
runTelomareParser2Term2 :: TelomareParser UnprocessedParsedTerm -- ^Parser to run
                        -> [(String, UnprocessedParsedTerm)]    -- ^Prelude
                        -> String                               -- ^Raw string to be parsed
                        -> Either String Term2                  -- ^Error on Left
runTelomareParser2Term2 parser prelude str =
  first errorBundlePretty (runParser parser "" str) >>= process2Term2 prelude

parseMain :: [(String, UnprocessedParsedTerm)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either String Term3               -- ^Error on Left.
parseMain prelude s = parseWithPrelude prelude s >>= process prelude
