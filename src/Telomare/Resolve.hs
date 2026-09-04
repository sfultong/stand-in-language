{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |Name resolution and core lowering: imports are resolved
-- ('resolveMain'), names are scope-checked, lambdas get de Bruijn indices
-- ('debruijinize'), @HashF@ nodes are folded to constants
-- ('generateAllHashes'), and the result is lowered to core
-- ('splitExpr': 'Term2' -> 'Term3').
--
-- == The dual pipeline
--
-- Two resolution pipelines coexist, with different semantics, and
-- 'Telomare.Driver.compileMainReporting' runs BOTH on every compile:
--
-- * 'process' (via 'validateVariables' + 'debruijinize'): scope-checks
--   and inlines let bindings. Its 'Term3' is what the type checker sees -
--   and is then discarded.
-- * 'processWlet' (via 'letsToApps' + 'debruijinizeApp'): converts let
--   bindings to lambda applications and threads @TUnsizedRepeaterF@
--   applications for recursive references. Its 'Term3' is what the sizing
--   pass consumes and what actually runs.
--
-- The typechecked term is therefore NOT the executed term. Do not unify
-- the two paths casually: sizing depends on the shape 'letsToApps'
-- produces, and the regression constants in the sizing tests depend on
-- it too.
module Telomare.Resolve where

import Codec.Binary.UTF8.String (encode)
import Control.Comonad.Cofree (Cofree (..), unwrap)
import qualified Control.Comonad.Trans.Cofree as C
import Control.Lens.Combinators (transform)
import Control.Monad (forM_, (<=<))
import Control.Monad.Identity (Identity (..))
import Control.Monad.Reader (MonadReader (ask), runReaderT)
import Control.Monad.State (StateT, evalStateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader (local)
import Control.Monad.Trans.Writer.Strict (WriterT (..), writer)
import Crypto.Hash (Digest, SHA256, hash)
import Data.Bifunctor (Bifunctor (first, second))
import qualified Data.ByteArray as BA
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (ord)
import Data.Fix (Fix (..))
import qualified Data.Foldable as F
import Data.Functor.Foldable (Corecursive (ana, embed), Recursive (..))
import Data.List (find)
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (absurd)
import Data.Functor.Classes (Eq1 (..), Show1 (liftShowsPrec))
import Debug.Trace (trace)
import GHC.Generics (Generic1, Generically1 (..))
import Telomare.Desugar (desugarTerm, rewriteOuterTag)
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.PrettyPrint (prettyPrint)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- |Int to ParserTerm
i2t :: a -> Int -> Cofree (ParserTermF l v) a
i2t anno = ana coalg where
  coalg 0 = anno C.:< ParserTermB ZeroSF
  coalg n = anno C.:< ParserTermB (PairSF (n-1) 0)

-- |List of Int's to ParserTerm
ints2t :: Foldable t => a -> t Int -> Cofree (ParserTermF l v) a
ints2t anno = foldr ((\x y -> anno :< ParserTermB (PairSF x y)) . i2t anno) (anno :< ParserTermB ZeroSF)

-- |String to ParserTerm
s2t :: (Foldable t, Functor t) => a -> t Char -> Cofree (ParserTermF l v) a
s2t anno = ints2t anno . fmap ord

-- |Collect all free variable names, also descending into 'Pattern' type annotations so that
-- names referenced via @: T@ patterns (e.g. UDT validators) are included.
freeVarsDeep :: ExpandedSurfaceTerm -> Set String
freeVarsDeep = cata alg where
  alg (VarAFP _ n)           = Set.singleton n
  alg (LamAFP _ n body)      = Set.delete (locatedNameText n) body
  alg (_ C.:< CaseUPF scrut alts) = scrut <> foldMap (\(p, body) -> patternRefs p <> body) alts <> caseRefs
    where
      caseRefs = Set.fromList ["and", "listEqual", "foldl", "abort"]
  alg e                    = F.fold e

  patternRefs :: PatternA -> Set String
  patternRefs = cata palg where
    palg :: PatternF AnnotatedEST (Set String) -> Set String
    palg (PatternAnnotatedF inner ty) = inner <> freeVarsDeep (unAnnotatedEST ty)
    palg e                            = F.fold e

-- |Keep only bindings transitively reachable from @root@. Unreachable
-- bindings are skipped by 'process' and 'compile', giving large speedups
-- when a snippet only uses a small slice of a large Prelude+UDT environment.
--
-- 'freeVarsDeep' also accounts for names that 'desugarTerm' injects into
-- case alternatives before 'process': @and@, @listEqual@,
-- @foldl@, @abort@. Without these the pruned LetUPF would fail with
-- MissingDefinitions after case expansion.
pruneBindings :: ExpandedSurfaceTerm
              -> [(String, ExpandedSurfaceTerm)]
              -> [(String, ExpandedSurfaceTerm)]
pruneBindings root bs = filter ((`Set.member` reachable) . fst) bs
  where
    seed      = freeVarsDeep root
    bmap      = Map.fromList $ fmap (second freeVarsDeep) bs
    expand r  = r <> F.fold (Map.restrictKeys bmap r)
    reachable = until (\s -> expand s == s) expand seed

type VarList = [String]

debruijinize :: forall m. (Monad m, MonadFail m) => Term1 -> m Term2
debruijinize = flip (runReaderT . cata f) [] where
  f = \case
    LamAFP a lt x -> embed . LamAFP a (convLam lt) <$> local (lt:) x
    VarAFP a n -> ask >>= \vl -> lift $ findElem a n vl
    AppAFP a fn i -> fmap embed . sequence $ AppAFP a fn i
    x           -> fmap embed . sequence $ liftC conv x
  liftC g (a C.:< x) = a C.:< g x
  conv = \case
    ParserTermB x -> ParserTermB x
    ParserTermH x -> ParserTermH x
    TUnsizedRepeaterF -> TUnsizedRepeaterF
    ParserTermL _ -> error "Telomare.Resolve.debruijinize: unexpected ParserTermL"
  convLam = \case
    Open _ -> Open ()
    Closed _ -> Closed ()
    LetBinding _ _ -> Open ()
  findElem :: LocTag -> String -> [LamType String] -> m Term2
  findElem _anno n vl = case find (ff n) (zip [0..] vl) of
    Just (i, _) -> pure $ VarP i
    _           -> fail $ "undefined identifier " <> n
  ff n = \case
    (_, Open n') | n' == n -> True
    (_, Closed n') | n' == n -> True
    (_, LetBinding _ n') | n' == n -> True
    _ -> False

-- | Close all naked open lambdas
closeLams :: Term2 -> Term2
closeLams = runIdentity . flip (runReaderT . cata f) True where
  f = \case
    anno C.:< x -> case x of
      ParserTermL (LamF lt ix) -> ask >>= \naked -> if naked
        then LamP (Closed ()) <$> local (const False) ix
        else LamP lt <$> local (const False) ix
      x' -> (anno :<) <$> sequence x'

debruijinizeApp :: forall m. (Monad m, MonadFail m) => Term1 -> m Term2
debruijinizeApp = fmap closeLams . flip (runReaderT . cata f) [] where
  f = \case
    LamAFP a lt x -> embed . LamAFP a (convLam lt) <$> local (lt:) x
    VarAFP a n -> ask >>= \vl -> lift $ findElem a n vl
    AppAFP a fn i -> fmap embed . sequence $ AppAFP a fn i
    x           -> fmap embed . sequence $ liftC conv x
  liftC g (a C.:< x) = a C.:< g x
  conv = \case
    ParserTermB x -> ParserTermB x
    ParserTermH x -> ParserTermH x
    TUnsizedRepeaterF -> TUnsizedRepeaterF
    ParserTermL _ -> error "Telomare.Resolve.debruijinizeApp: unexpected ParserTermL"
  convLam = \case
    Open _ -> Open ()
    Closed _ -> Closed ()
    LetBinding _ _ -> Open ()
  findElem :: LocTag -> String -> [LamType String] -> m Term2
  findElem anno n vl = case find (ff n) (zip [0..] vl) of
    Just (i, LetBinding c _) -> pure $ iterate (\ix -> AppP ix (anno :< TUnsizedRepeaterF)) (VarP i) !! c
    Just (i, _) -> pure $ VarP i
    _ -> fail $ "undefined identifier " <> n
  ff n = \case
    (_, Open n') | n' == n -> True
    (_, Closed n') | n' == n -> True
    (_, LetBinding _ n') | n' == n -> True
    _ -> False

-- | Compile Term2 to Term3 with trimmed lambda captures — lambda lifting
-- in Telomare's env-machine sense. A lambda's closure used to capture the
-- entire ambient env (@Pair (Defer body) Env@); it now captures a fresh
-- tuple of exactly the outer variables the body uses, and the body's
-- variable references are reindexed against that layout. Free-variable
-- abstraction is already done by the language design (defer bodies are
-- Env-closed), so this one representation change is the whole
-- transformation: dead environment stops flowing through closures, a
-- closure with no free variables becomes fully closed (freely copyable
-- code under the IC runtime's table), and — the EAL payoff — closure
-- creation is disjoint path projections instead of a whole-env use, so
-- contraction is charged per genuinely-duplicated variable rather than
-- forcing a box on the entire environment.
--
-- The cata carrier pairs each subterm's free de Bruijn indices with a
-- builder parameterized by the enclosing frame's renaming.
splitExpr :: Term2 -> Term3
splitExpr t2 = flip State.evalState (toEnum 0, toEnum 0) $
  snd (cata f t2) unboundVar where
  unboundVar :: Int -> Int
  unboundVar n = error $ "splitExpr: unbound variable index " <> show n
  f :: C.CofreeF (ParserTermF (LamType ()) Int) LocTag
       (Set Int, (Int -> Int) -> Term3Builder Term3)
    -> (Set Int, (Int -> Int) -> Term3Builder Term3)
  f (anno C.:< g) =
    let tagged (frees, mk) = (frees, fmap (rewriteOuterTag anno) . mk)
        closed mk = (Set.empty, const mk)
        one (frees, mk) wrap = (frees, fmap wrap . mk)
        combine2 (fa, ma) (fb, mb) wrap =
          (fa <> fb, \ren -> wrap (ma ren) (mb ren))
        combine3 (fa, ma) (fb, mb) (fc, mc) wrap =
          (fa <> fb <> fc, \ren -> wrap (ma ren) (mb ren) (mc ren))
    in tagged $ case g of
      ParserTermB ZeroSF -> closed $ pure ZeroB
      ParserTermB (PairSF a b) -> combine2 a b pairS
      ParserTermL x -> case x of
        VarF n -> (Set.singleton n, \ren -> pure . varB $ ren n)
        AppF c i -> combine2 c i appS
        LamF (Open ()) (bodyFrees, mkBody) ->
          -- outer variables the body needs, in ascending order; inside the
          -- new closure the env is (arg, (v_1, (v_2, ... (v_k, 0)))), so
          -- outer variable o at tuple position j is reached as varB j
          let outer = Set.toAscList . Set.map (subtract 1)
                    $ Set.filter (>= 1) bodyFrees
              positions = Map.fromList $ zip outer [1 ..]
              bodyRen n
                | n == 0 = 0
                | otherwise = Map.findWithDefault
                    (error $ "splitExpr: lambda body lost variable " <> show n)
                    (n - 1) positions
              capture :: (Int -> Int) -> Term3Builder Term3
              capture ren = foldr (pairS . pure . varB . ren)
                                  (pure ZeroB) outer
          in ( Set.fromList outer
             , pairS (mkBody bodyRen >>= deferS) . capture )
        LamF (Closed ()) (_, mkBody) -> closed $ clamS (mkBody id)
        LamF (LetBinding _ _) _ -> error "Telomare.Resolve.splitExpr: unexpected LetBinding"
      ParserTermH h -> case h of
        CheckF tc c -> combine2 tc c $ \tc' c' ->
          (\tc'' c'' -> anno :< Term3CheckingWrapper anno tc'' c'') <$> tc' <*> c'
        ITEF i t e -> combine3 i t e $ \i' t' e' -> iteB_ <$> i' <*> t' <*> e'
        HLeftF x -> one x LeftB
        HRightF x -> one x RightB
        HTraceF x -> one x id -- TODO add trace back in, or rethink
        ChurchF n -> closed $ i2CB anno n
        RecursionF t r b -> combine3 t r b (unsizedRecursionWrapper anno)
        HashF _ -> error "Telomare.Resolve.splitExpr: unexpected HashF"
      TUnsizedRepeaterF -> closed $ do
        urt <- State.gets snd
        State.modify (\(fi, _) -> (fi, succ urt))
        unsizedRecursionOracle anno urt

openLambda :: String -> Term1 -> Term1
openLambda name body@(_anno :< _) = LamP (Open name) body

-- |Transform a case-free surface term to 'Term1', validating and inlining
-- variables.
-- |Order let-binding names so that each name comes after everything it
-- depends on (dependencies first). Fails with 'DefinitionCycle' when the
-- dependency graph is cyclic.
topologicalSort :: [String] -> Map String (Set String) -> Either ResolverError [String]
topologicalSort names deps = go [] names
  where
    go result [] = Right (reverse result)
    go result remaining@(firstRemaining : _) =
      case find (canProcess remaining) remaining of
        Nothing ->
          -- Must be a cycle - find it for error message
          let findCycleFrom start = go' start Set.empty
                where go' curr visited
                        | curr `Set.member` visited = [curr]
                        | otherwise =
                            case find (`elem` remaining) (Set.toList $ Map.findWithDefault Set.empty curr deps) of
                              Nothing   -> []
                              Just next -> curr : go' next (Set.insert curr visited)
          in Left $ DefinitionCycle (findCycleFrom firstRemaining)
        Just name -> go (name : result) (delete name remaining)

    canProcess rn name =
      all (`notElem` rn) (Set.toList $ Map.findWithDefault Set.empty name deps)

    delete x = filter (/= x)

validateVariables :: DesugaredSurfaceTerm
                  -> Either ResolverError Term1
validateVariables term =
  let validateWithEnvironment :: DesugaredSurfaceTerm
                              -> StateT (Map String Term1) (Either ResolverError) Term1
      validateWithEnvironment = \case
        _anno :< LetUPF preludeMap inner -> do
          oldPrelude <- State.get

          -- Build dependency graph
          let dependencies :: Map String (Set String)
              dependencies = Map.fromList
                [(locatedNameText name, Set.fromList $ getDirectDeps def) | (name, def) <- preludeMap]

              -- Get direct variable dependencies (only those defined in this let block)
              -- Uses Set to properly handle lambda-bound variable shadowing
              letBindingNames = Set.fromList (letBindingName <$> preludeMap)
              getDirectDeps = Set.toList . cata alg where
                alg = \case
                    (VarFP n) -> if Set.member n letBindingNames then Set.singleton n else Set.empty
                    (LamAFP _ v body) -> Set.delete (locatedNameText v) body
                    (_ C.:< LetUPF binds body) ->
                      let boundNames = Set.fromList (letBindingName <$> binds)
                          bindDeps = foldMap letBindingValue binds
                      in Set.union (bindDeps Set.\\ boundNames) (body Set.\\ boundNames)
                    (ITEAFP _ i t e) -> i <> t <> e
                    (PairAFP _ a b) -> a <> b
                    (_ C.:< ListUPF l) -> F.fold l
                    (AppAFP _ f x) -> f <> x
                    (_ C.:< UnprocessedParsedTermH (RecursionF t r b)) -> t <> r <> b
                    (_ C.:< UnprocessedParsedTermH (HLeftF x)) -> x
                    (_ C.:< UnprocessedParsedTermH (HRightF x)) -> x
                    (_ C.:< UnprocessedParsedTermH (HTraceF x)) -> x
                    (_ C.:< UnprocessedParsedTermH (CheckF cf x)) -> cf <> x
                    (_ C.:< UnprocessedParsedTermH (HashF x)) -> x
                    _ -> Set.empty

          -- Check if original order works (no forward references)
          let originalOrder = letBindingName <$> preludeMap
              hasForwardRef = any (\(i, name) ->
                let deps = Map.findWithDefault Set.empty name dependencies
                    laterNames = Set.fromList $ drop (i + 1) originalOrder
                in not . Set.null $ deps `Set.intersection` laterNames
                ) (zip [0..] originalOrder)

          -- Only reorder if necessary
          sortedBindings <- if hasForwardRef
            then case topologicalSort originalOrder dependencies of
              Left defCycle -> State.lift . Left $ defCycle
              Right sortedNames ->
                pure [(name, def) | name <- sortedNames,
                      (name', def) <- preludeMap, name == locatedNameText name']
            else pure $ first locatedNameText <$> preludeMap  -- Keep original order

          -- Process bindings in order
          forM_ sortedBindings $ \(name, def) -> do
            validatedDef <- validateWithEnvironment def
            State.modify (Map.insert name validatedDef)

          result <- validateWithEnvironment inner
          State.put oldPrelude
          pure result
        _anno :< UnprocessedParsedTermL (LamF v x) -> do
          oldState <- State.get
          State.modify (Map.insert (locatedNameText v) (VarP (locatedNameText v)))
          result <- validateWithEnvironment x
          State.put oldState
          pure $ openLambda (locatedNameText v) result
        anno :< UnprocessedParsedTermL (VarF n) -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _      -> State.lift . Left $ MissingDefinitionAt anno n

        anno :< (UnprocessedParsedTermH (ITEF i t e)) -> (\a b c -> embed $ ITEAFP anno a b c) <$> validateWithEnvironment i
                                                                <*> validateWithEnvironment t
                                                                <*> validateWithEnvironment e
        anno :< IntUPF x -> pure $ i2t anno x
        anno :< StringUPF s -> pure $ s2t anno s
        anno :< UnprocessedParsedTermB ZeroSF -> pure $ anno :< ParserTermB ZeroSF
        anno :< UnprocessedParsedTermB (PairSF a b) -> (\x y -> anno :< ParserTermB (PairSF x y)) <$> validateWithEnvironment a
                                                            <*> validateWithEnvironment b
        anno :< ListUPF l -> foldr (\x y -> anno :< ParserTermB (PairSF x y)) (anno :< ParserTermB ZeroSF) <$> mapM validateWithEnvironment l
        anno :< UnprocessedParsedTermL (AppF f x) -> (\a b -> embed $ AppAFP anno a b) <$> validateWithEnvironment f
                                                          <*> validateWithEnvironment x
        anno :< UnprocessedParsedTermH (RecursionF t r b) ->
          (\x y z -> embed $ AppAFP anno (anno :< embedH (RecursionF x y z)) (anno :< TUnsizedRepeaterF))
          <$> validateWithEnvironment t
          <*> validateWithEnvironment r
          <*> validateWithEnvironment b
        anno :< UnprocessedParsedTermH (ChurchF n) -> pure $ anno :< embedH (ChurchF n)
        anno :< UnprocessedParsedTermH (HLeftF x) -> (\y -> anno :< embedH (HLeftF y)) <$> validateWithEnvironment x
        anno :< UnprocessedParsedTermH (HRightF x) -> (\y -> anno :< embedH (HRightF y)) <$> validateWithEnvironment x
        anno :< UnprocessedParsedTermH (HTraceF x) -> (\y -> anno :< embedH (HTraceF y)) <$> validateWithEnvironment x
        anno :< UnprocessedParsedTermH (CheckF cf x) -> (\y y'-> anno :< embedH (CheckF y y')) <$> validateWithEnvironment cf <*> validateWithEnvironment x
        anno :< UnprocessedParsedTermH (HashF x) -> (\y -> anno :< embedH (HashF y)) <$> validateWithEnvironment x
        -- Cases cannot survive 'desugarTerm'; the witness field is 'Void'.
        _ :< CaseNodeUPF v _ _ -> absurd v
  in State.evalStateT (validateWithEnvironment term) Map.empty

annotateUnsizedCount :: DesugaredSurfaceTerm
                     -> Cofree DesugaredSurfaceTermF (LocTag, Int)
annotateUnsizedCount = capTop . flip evalStateT (0 :: Integer) . cata f where
  f = \case
    anno C.:< x -> case x of
      ur@(UnprocessedParsedTermH (RecursionF _ _ _)) -> sequence ur >>= \nur -> do
        n <- State.get
        State.put (n + 1)
        lift (Set.singleton n, embed $ AppAFP (anno, 0) ((anno, 0) :< nur) (embed $ VarAFP (anno, 0) (':' : show n)))
      LetUPF bindings inner -> (\b i -> (anno, 0) :< LetUPF b i) <$> traverse rebind bindings <*> inner
      other -> ((anno, 0) :<) <$> sequence other
  rebind (n, x) = (\(_n', x') -> (n, x')) <$> cap (locatedNameText n) (evalStateT x 0)
  cap n (vs, x@((anno, _) :< _)) = lift (Set.empty, (n, foldr (\v b -> embed $ LamAFP (anno, length vs) (locatedName anno (':' : show v)) b) x vs))
  -- HACK vars are just placehorders for next step
  capTop (vs, x@((anno, _) :< _)) =
    foldr (\v b -> embed $ AppAFP (anno, length vs) (embed $ LamAFP (anno, 0) (locatedName anno (':' : show v)) b) (embed $ VarAFP (anno, 0) (':' : show v))) x vs

-- convert let bindings to nested lambda/app brackets
letsToApps :: DesugaredSurfaceTerm -> Either ResolverError Term1
letsToApps term =
  let getTransitive deps n = Set.singleton n <> case Map.lookup n deps of
        Just s | not (null s) -> mconcat . fmap (getTransitive deps) $ Set.toList s
        _ -> Set.empty
      getTransitive' deps = mconcat . fmap (getTransitive deps) . Set.toList
      makeBindingsAsoc (name, def) = case runWriterT def of
        Left s           -> Left s
        Right (nx, refs) -> pure (locatedNameText name, (nx,refs))
      -- f algebra builds Term1 wrapped with metadata (WriterT) of unbound refs (Set String) or ResolverError
      buildRefs ((anno, urC) C.:< upf) = case upf of
        UnprocessedParsedTermL (VarF n) -> writer (embed $ VarAFP (anno, urC) n, Set.singleton n)
        UnprocessedParsedTermL (LamF v x) -> f (runWriterT x) where
          name = locatedNameText v
          -- f :: Either String ()
          f (Right (nx, refs)) = let nrefs = Set.delete name refs in if null nrefs && urC == 0
            then writer (embed $ LamAFP (anno, urC) (Closed name) nx, nrefs)
            else writer (embed $ LamAFP (anno, urC) (Open name) nx, nrefs)
          f (Left s)           = lift $ Left s
        LetUPF bindings inner -> case runWriterT inner of
          Left s -> lift $ Left s
          Right (nInner, refs) -> WriterT $ do
            -- Build dependency graph
            nBindings <- traverse makeBindingsAsoc bindings
            let originalOrder = letBindingName <$> bindings
                dependencies = Map.fromList $ fmap (second snd) nBindings
                sortedBindings =
                  -- reverse-dependency order: 'foldr makeBinding' below re-reverses
                  case reverse <$> topologicalSort originalOrder dependencies of
                    Left defCycle -> Left defCycle
                    Right sortedNames ->
                      pure [(name, def) | name <- sortedNames, (name', (def, _)) <- nBindings, name == name']
                makeBinding (n,d@((_, c) :< _)) letBody@(a :< _) = embed $ AppAFP a (embed $ LamAFP a (LetBinding c n) letBody) d
            sortedBindings >>= \sb -> let trans = getTransitive' dependencies refs
                                          sb' = [(n,t) | (n,t) <- sb,  n `elem` trans]
                                          newRefs = Set.difference trans (Set.fromList $ fmap fst sb')
                                      in pure (foldr makeBinding nInner $ reverse sb', newRefs)
        x -> WriterT . fmap (first (((anno, urC) :<) . brt)) . runWriterT $ sequence x where
          brt = \case
            UnprocessedParsedTermL (AppF f arg) -> ParserTermL $ AppF f arg
            UnprocessedParsedTermB b -> ParserTermB b
            UnprocessedParsedTermH h -> ParserTermH h
            IntUPF n -> unwrap $ i2t (anno, urC) n
            StringUPF s -> unwrap $ s2t (anno, urC) s
            ListUPF l -> unwrap $ foldr (\el y -> (anno, urC) :< ParserTermB (PairSF el y)) ((anno, urC) :< ParserTermB ZeroSF) l
            _ -> error "Telomare.Resolve.letsToApps: unexpected constructor"
      cleanup = \case
        Left s -> Left s
        Right (x, refs) -> forgetURCount <$> addRepeaters refs x
      -- HACK extended from annotateUnsizedCount
      addRepeaters refs = if null refs
        then pure
        else \case
        a :< ParserTermL (AppF x (_ :< ParserTermL (VarF v))) -> case Set.partition (== v) refs of
          (found, rest) | length found == 1 -> (\c i -> embed $ AppAFP a c i) <$> addRepeaters rest x <*> pure (a :< TUnsizedRepeaterF)
          _ -> Left . MissingDefinitions $ Set.toList refs
        _ -> Left . MissingDefinitions $ Set.toList refs

      forgetURCount = cata f where
        f ((a,_c) C.:< x) = a :< x
  in cleanup . runWriterT . cata buildRefs $ annotateUnsizedCount term

-- |Process an `Term2` to have all `HashUP` replaced by a unique number.
-- The unique number is constructed by doing a SHA1 hash of the Term2 and
-- adding one for all consecutive HashUP's.
generateAllHashes :: Term2 -> Term2
generateAllHashes x@(anno :< _) = transform interm x where
  hash' :: ByteString -> Digest SHA256
  hash' = hash
  term2Hash :: Term2 -> ByteString
  term2Hash = BS.pack . BA.unpack . hash' . BS.pack . encode . show . (forget :: Cofree (ParserTermF (LamType ()) Int) LocTag -> Fix (ParserTermF (LamType ()) Int))
  bs2Term2 :: ByteString -> Term2
  bs2Term2 bs = ints2t anno . drop 24 $ fromInteger . toInteger <$> BS.unpack bs
  interm :: Term2 -> Term2
  interm = \case
    (_anno :< ParserTermH (HashF term1)) -> bs2Term2 . term2Hash $ term1
    other                  -> other

-- |Process a fully desugared surface term to 'Term3'.
process :: DesugaredSurfaceTerm
        -> Either ResolverError Term3
process upt = (\dt -> debugTrace ("Resolver process term:\n" <> prettyPrint dt) dt) . splitExpr <$> process2Term2 upt

processWlet :: DesugaredSurfaceTerm -> Either ResolverError Term3
processWlet = fmap (splitExpr . (\dt -> debugTrace ("Resolver processWlet before split:\n" <> pt dt) dt)) . process2Term2let where
  pt x = prettyPrint $ fg x
  fg :: Term2 -> Fix (ParserTermF (LamType ()) Int)
  fg = forget

process2Term2 :: DesugaredSurfaceTerm
              -> Either ResolverError Term2
process2Term2 = fmap generateAllHashes
               . debruijinize <=< (fmap tf . validateVariables)
                  where tf x = debugTrace ("reg Term1:\n" <> prettyPrint x) x

process2Term2let :: DesugaredSurfaceTerm -> Either ResolverError Term2
process2Term2let = fmap generateAllHashes
                  . debruijinizeApp <=< fmap tf . letsToApps
                  where tf x = debugTrace ("wLet Term1:\n" <> prettyPrint x) x

resolveAllImports :: ExpandedModules -- ^All modules
                  -> ExpandedModule -- ^Module whose imports should be resolved
                  -> Either ResolverError [(String, ExpandedSurfaceTerm)]
resolveAllImports modules = resolveItems modules []

resolveImports :: ExpandedModules
               -> String
               -> Either ResolverError [(String, ExpandedSurfaceTerm)]
resolveImports modules = resolveModule modules []

resolveModule :: ExpandedModules
              -> [String]
              -> String
              -> Either ResolverError [(String, ExpandedSurfaceTerm)]
resolveModule modules stack moduleName
  | moduleName `elem` stack =
      Left . ImportCycle $ dropWhile (/= moduleName) stack <> [moduleName]
  | otherwise = case lookup moduleName modules of
      Nothing    -> Left $ ModuleNotFound moduleName
      Just items -> resolveItems modules (stack <> [moduleName]) items

resolveItems :: ExpandedModules
             -> [String]
             -> ExpandedModule
             -> Either ResolverError [(String, ExpandedSurfaceTerm)]
resolveItems modules stack = fmap concat . traverse resolveItem
  where
    resolveItem = \case
      ExpandedModuleBinding name value -> Right [(locatedNameText name, value)]
      ExpandedModuleImport importDecl -> do
        bindings <- resolveModule modules stack
          (locatedNameText $ parsedImportModule importDecl)
        pure $ case parsedImportQualifier importDecl of
          Nothing        -> bindings
          Just qualifier -> qualifyBindings (locatedNameText qualifier) bindings

qualifyBindings :: String
                -> [(String, ExpandedSurfaceTerm)]
                -> [(String, ExpandedSurfaceTerm)]
qualifyBindings qualifier bindings =
  [ (qualify name, qualifyTerm names qualifier value)
  | (name, value) <- bindings
  ]
  where
    names = Set.fromList $ fst <$> bindings
    qualify name = qualifier <> "." <> name

qualifyTerm :: Set String -> String -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm
qualifyTerm names qualifier = go Set.empty
  where
    go bound (loc :< term) = loc :< case term of
      UnprocessedParsedTermL (VarF name)
        | name `Set.member` names && name `Set.notMember` bound ->
            UnprocessedParsedTermL $ VarF (qualifier <> "." <> name)
      other -> mapScoped (\binders -> go (bound <> binderNames binders)) other

    binderNames = Set.fromList . fmap locatedNameText

resolveMain :: ExpandedModules -- ^Modules and their typed expanded items
            -> String -- ^Module name with main
            -> Either ResolverError ExpandedSurfaceTerm
resolveMain allModules mainModule = case lookup mainModule allModules of
  Nothing -> Left $ ModuleNotFound mainModule
  Just _ -> do
    resolved <- resolveImports allModules mainModule
    case lookup "main" resolved of
      Nothing -> Left $ NoMainFunction mainModule
      Just x ->
        let loc = case x of loc' :< _ -> loc'
            locatedBindings = first (locatedName (GeneratedLoc "resolveMain.binding" (Just loc))) <$> pruneBindings x resolved
        in Right $ GeneratedLoc "resolveMain" (Just loc) :< LetUPF locatedBindings x

main2Term3 :: ExpandedModules
           -> String -- ^Module name with main
           -> Either ResolverError Term3 -- ^Error on Left
main2Term3 moduleBindings s = resolveMain moduleBindings s >>= process . desugarTerm

main2Term3let :: ExpandedModules
            -> String -- ^Module name with main
            -> Either ResolverError Term3 -- ^Error on Left
main2Term3let moduleBindings s = resolveMain moduleBindings s >>= processWlet . desugarTerm

data Term3LiftingF f
  = Term3LB (BasicExprF f)
  | Term3LS (StuckF f)
  | Term3LA (AbortableF f)
  | Term3LUnsized UnsizedRecursionToken
  | Term3LCheckingWrapper LocTag f f
  | Term3LDeferRef (Digest SHA256)
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 Term3LiftingF)
instance BasicBase Term3LiftingF where
  embedB = Term3LB
  extractB = \case
    Term3LB x -> pure x
    _         -> Nothing
instance StuckBase Term3LiftingF where
  embedS = Term3LS
  extractS = \case
    Term3LS x -> pure x
    _         -> Nothing
instance AbortBase Term3LiftingF where
  embedA = Term3LA
  extractA = \case
    Term3LA x -> pure x
    _         -> Nothing
instance Show1 Term3LiftingF where
  liftShowsPrec shwPrec shwList prec = \case
    Term3LB x -> liftShowsPrec shwPrec shwList prec x
    Term3LS x -> liftShowsPrec shwPrec shwList prec x
    Term3LA x -> liftShowsPrec shwPrec shwList prec x
    Term3LUnsized urt -> shows $ "Term3LUnsized" <> show urt
    Term3LCheckingWrapper loc cf c -> shows "Term3LCheckingWrapper(" . shows loc . shows ", " . shwPrec 0 cf . shows ", " . shwPrec 0 c . shows ")"
    Term3LDeferRef h -> shows "Term3LDeferRef " . shows h

type Term3Lifting = Cofree Term3LiftingF LocTag

-- | Lifted Defer bodies, keyed by a hash of the (annotation-stripped) body.
-- Each entry keeps the first-seen FunctionIndex for reporting and inlining.
newtype DeferMap = DeferMap (Map (Digest SHA256) (FunctionIndex, Term3Lifting))

instance Semigroup DeferMap where
  (<>) (DeferMap a) (DeferMap b) = DeferMap $ Map.unionWithKey f a b where
    f _k x@(_, xb) (_, yb) = if forgetL xb /= forgetL yb
      then error "defer lifting encountered what must be an adversarial grammar, colliding defer subterms"
      else x
    forgetL :: Term3Lifting -> Fix Term3LiftingF
    forgetL = forget
instance Monoid DeferMap where
  mempty = DeferMap Map.empty

makeDM :: Digest SHA256 -> FunctionIndex -> Term3Lifting -> DeferMap
makeDM k fi e = DeferMap $ Map.singleton k (fi, e)

-- | Like lambda lifting: replace every Defer body with a hash reference and
-- collect the bodies in a DeferMap. Sound without free-variable abstraction
-- because Defer bodies are closed (their only free variable is their own
-- Env). Nested defers are lifted first, so bodies in the map contain only
-- references and the map is a DAG. Identical bodies (up to annotations)
-- dedupe to one entry. Hashing mirrors 'generateAllHashes': the hash is
-- taken over the annotation-stripped body.
deferLift :: Term3 -> (DeferMap, Term3Lifting)
deferLift = cata hF where
  hF :: C.CofreeF Term3F LocTag (DeferMap, Term3Lifting) -> (DeferMap, Term3Lifting)
  hF (anno C.:< x) = case x of
    StuckFW (DeferSF ind (dm, body)) ->
      let hash' :: ByteString -> Digest SHA256
          hash' = hash
          forgetL :: Term3Lifting -> Fix Term3LiftingF
          forgetL = forget
          h = hash' . BS.pack . encode . show $ forgetL body
      in (dm <> makeDM h ind body, anno :< Term3LDeferRef h)
    Term3B b -> (anno :<) . Term3LB <$> sequence b
    Term3S s -> (anno :<) . Term3LS <$> sequence s
    Term3A a -> (anno :<) . Term3LA <$> sequence a
    Term3Unsized urt -> pure $ anno :< Term3LUnsized urt
    Term3CheckingWrapper loc cf f -> (anno :<) <$> (Term3LCheckingWrapper loc <$> cf <*> f)
