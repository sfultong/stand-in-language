{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}

-- | Elementary Affine Logic annotation inference for 'Term3'.
--
-- This decorates a Term3 program with EAL box levels, in the style of
-- Coppola-Martini decoration inference: every AST edge gets a natural-number
-- variable counting the box doors on that edge, types carry bang-count
-- variables, and typing plus the EAL variable conditions become linear
-- constraints over the naturals. A successful inference is an
-- elementary-time certificate for the term; the maximum box nesting depth is
-- the height of the elementary bound's tower.
--
-- Appliable values have no arrow structure in the type language. A defer
-- reference is typed as an atomic code constant carrying its content hash
-- ('CodeT' over 'Tag' sets), gates and aborts are built-in tags, and
-- unification at code positions takes the UNION of tags rather than
-- equating anything — so a gate join of structurally different functions
-- is a set union, not a unification failure. Application is a deferred
-- constraint: every SetEnv registers an apply site, and a post-walk
-- fixpoint ('resolveApplies') dispatches each tag that flows into the
-- site's function position, deriving the referenced body's constraints
-- fresh per site per tag. Types and bangs are therefore per-application
-- (finer than per-reference), and nothing is ever pinned against a use.
--
-- Two consequences replace the classic failure modes of an equational
-- skeleton:
--
--   * There is no occurs check. Code types are atomic, so a type cycle can
--     only thread through pair structure, and an unboundedly nested pair
--     type is data of unknown shape — exactly what 'DataT' already means.
--     Cycles collapse to data; a function value hiding on a cycle then
--     surfaces as a code-vs-data mismatch instead of escaping tracking.
--   * Unbounded self-application shows up as unbounded dispatch nesting
--     (each derivation of a body re-applies itself) and is rejected by a
--     dispatch depth cap, the analogue of a flow analyzer's level blowup.
--
-- A function position nothing ever flows into (the program's unknown
-- input) is tolerated without constraints, mirroring the runtime contract
-- that input is data: applying data sticks at runtime, and stuckness is a
-- value until demanded.
--
-- Adaptations to Telomare:
--
--   * Each Defer body has exactly one free variable (Env), so promotion
--     constraints reduce to bookkeeping along Env occurrence paths.
--   * Contraction is detected at projection-path granularity: using
--     @Left Env@ and @Right Env@ once each is linear destructuring, not
--     duplication. Only overlapping uses of the same Env path force the
--     domain bang to be at least one.
--   * Gate branches are counted multiplicatively (evaluation is strict, so
--     both branches consume their Env occurrences).
--   * Term3Unsized is treated exactly like an Env occurrence, mirroring the
--     type checker.
--   * The check function of Term3CheckingWrapper is ignored, mirroring the
--     type checker.
--
-- The constraint solver is a propagate-then-repair heuristic with caps
-- rather than a complete ILP procedure; its limitations surface as errors
-- rather than wrong certificates.
--
-- The analyzer runs only over defer-lifted programs (see
-- 'Telomare.Resolver.deferLift'): every Defer body is hash-keyed in the
-- DeferMap and referenced via DeferRef, so raw DeferSF never reaches the
-- analyzer and the tags dispatched at apply sites are exactly the DeferMap
-- namespace that 'CodeGuidance' and the IC runtime's templates share.
module Telomare.EAL where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (foldM, forM, forM_, unless, void, when, (<=<))
import Control.Monad.Except
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Crypto.Hash (Digest, SHA256)
import Data.Either (rights)
import Data.List (find, isPrefixOf, minimumBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as Set
import Telomare.IR.Base (AbortableF (..), BasicExprF (..), FunctionIndex,
                         StuckF (..), pattern AbortFW, pattern BasicFW,
                         pattern StuckFW)
import Telomare.IR.Core (CompiledExpr, Term3, compiled2Term3)
import Telomare.IR.Loc (LocTag (..))
import Telomare.Resolve (DeferMap (..), Term3Lifting, Term3LiftingF (..),
                         deferLift)

-- | Maximum bang/box level before the solver assumes divergence.
levelCap :: Int
levelCap = 4096

-- | Maximum dispatch nesting depth before the analyzer assumes unbounded
-- self-application: a body derived at depth d dispatches its own apply
-- sites at depth d+1, so legitimate programs bottom out at their static
-- reference-nesting depth while omega-style terms climb forever.
dispatchDepthCap :: Int
dispatchDepthCap = 1024

-- | A bang-count variable (also used for per-edge box counts).
newtype BVar = BVar { unBVar :: Int } deriving (Eq, Ord, Show)

-- | Bang-annotated type: a bang count in front of a type skeleton.
data Sigma = Sigma BVar Tau deriving Show

-- | An appliable value's identity: a defer body by content hash, or one of
-- the built-in appliable values and their intermediate stages.
data Tag
  = TCode (Digest SHA256) -- ^ a lifted defer body
  | TGate                 -- ^ the gate value
  | TGateFn               -- ^ a gate applied to its scrutinee
  | TAbort                -- ^ the abort value
  | TAbortCont            -- ^ abort applied to a Zero message (identity)
  deriving (Eq, Ord, Show)

data Tau
  = DataT              -- ^ Zero-typed data trees (pairs collapse into this)
  | VarT Int
  | PairT Sigma Sigma
  | CodeT Int          -- ^ appliable constants: a tag-set class ('esTagSets')
                       --   that unions at joins instead of unifying
  | CapT Int           -- ^ the capture of whichever tag a closure package
                       --   turns out to be: joins union the package, and
                       --   dispatch resolves it per tag, so captures of
                       --   different tags never unify structurally
  deriving Show

-- | Where and why a constraint arose, for error reporting.
data Blame = Blame LocTag String deriving (Eq, Show)

data EALError
  = EALTypeMismatch LocTag String
  -- | A bang class is required to be boxed (first blame) and forced to be
  -- unboxed (second blame). This is the interesting error for affine-repair
  -- transformations: it names the duplication and the site that forbids
  -- boxing it.
  | EALBoxConflict Blame Blame
  | EALSolverGaveUp String
  -- | Lifted inference only: this body references a lifted body that itself
  -- failed inference, so it was not analyzed.
  | EALDependencyFailed (Digest SHA256)
  -- | An analyzer invariant was violated: a bug in this module (or a term
  -- that skipped 'deferLift'), never a fact about the analyzed program.
  | EALInternal String
  deriving (Eq, Show)

-- | One step into the env pair structure.
data Step = SL | SR deriving (Eq, Ord, Show)

showSteps :: [Step] -> String
showSteps [] = "<whole env>"
showSteps xs = concatMap (\case SL -> "L"; SR -> "R") xs

-- | Constraint state of a bang-variable class: unconstrained, forced to
-- zero (unboxed), or bounded below (boxed). Zero-forcing and a lower bound
-- are mutually exclusive; asserting both is an 'EALBoxConflict'.
--
-- Invariant: 'ForcedLevel' carries a level of at least one. Both
-- 'getLowerBound' and the unconditional 'ForcedLevel'/'ForcedZero' conflict
-- in 'mergeClasses' rely on this.
data ClassInfo
  = Unrestricted
  | ForcedZero Blame
  | ForcedLevel Int Blame
  deriving (Eq, Show)

-- | Sum equation over bang variables: sum of lhs = rhs.
data SumEq = SumEq
  { seLhs   :: [BVar]
  , seRhs   :: BVar
  , seBlame :: Blame
  } deriving Show

-- | One registered application, dispatched by 'resolveApplies' once its
-- function position resolves to code.
data ApplySite = ApplySite
  { apFn         :: Tau     -- ^ function position (usually still a variable)
  , apEnv        :: Sigma   -- ^ operand env
  , apRes        :: Sigma   -- ^ site result
  , apGlobal     :: [BVar]  -- ^ global box path at the site
  , apDepth      :: Int     -- ^ dispatch nesting depth (self-application
                            --   guard)
  , apLoc        :: LocTag
  , apDispatched :: Set Tag -- ^ tags already dispatched at this site
  }

data EALState = EALState
  { esNextVar    :: Int
  , esTVarBinds  :: Map Int Tau
  , esParents    :: Map Int Int       -- ^ union-find parent pointers (bangs)
  , esClasses    :: Map Int ClassInfo -- ^ info stored at roots
  , esTagParents :: Map Int Int       -- ^ union-find parent pointers (tags)
  , esTagSets    :: Map Int (Map Tag (Maybe Sigma))
    -- ^ per class root: its tags, each optionally carrying the capture
    -- that rides with that tag's code (Just for closure packages,
    -- Nothing for bare code and built-ins)
  , esSumEqs     :: [SumEq]
  , esApplies    :: Map Int ApplySite
  , esNextApply  :: Int
  , esDefers     :: Map FunctionIndex [BVar]
    -- ^ per Defer: the env domain bang of each dispatch derivation
    -- (reported as their max)
  , esLeafPaths  :: [[BVar]]          -- ^ root-to-leaf box paths, for max
                                      -- depth
  , esBodies     :: Map (Digest SHA256) (FunctionIndex, Term3Lifting)
    -- ^ the DeferMap: dispatching a code tag derives its body from here
  }

initEALState :: EALState
initEALState = EALState 0 mempty mempty mempty mempty mempty mempty mempty 0
  mempty mempty mempty

type EALM = ExceptT EALError (State EALState)

data EALResult = EALResult
  { ealTopLevelBang :: Int                  -- ^ bang on the program input
  , ealDeferBangs   :: Map FunctionIndex Int -- ^ env domain bang per Defer
  , ealMaxLevel     :: Int                  -- ^ max box nesting depth
  } deriving (Eq, Show)

-- | Per-hash guidance from one lifted Defer body's standalone inference:
-- what a consumer — the IC runtime foremost — can use about this code,
-- keyed by the same content hash that keys the DeferMap, so analysis and
-- runtime share one namespace. Guidance exists only for bodies whose
-- derivation certified — with nothing assumed about the env, so the
-- promise covers the body's own work — and its presence is itself a
-- whitelist (a consumer that would speculate or restructure sharing must
-- treat absence as "keep to the semantics-preserving default"); the
-- fields grade and localize that promise.
data CodeGuidance = CodeGuidance
  { cgIndex        :: FunctionIndex -- ^ first-seen index, for reporting
  , cgUsage        :: Map [Step] Int
    -- ^ env occurrences per projection path: disjoint single-use paths
    -- are linear destructuring (routable as wiring, no sharing needed);
    -- a path counted twice, or overlapping a used sub-path, is where
    -- duplication actually happens
  , cgEnvBang      :: Int       -- ^ solved bang on the body's env domain
                                --   (this body's standalone derivation; a
                                --   dispatch site's derivation may differ)
  , cgMaxLevel     :: Int       -- ^ max box depth inside the body (including
                                --   depths of bodies it applies)
  , cgSpeculatable :: Bool
    -- ^ False when the body, or a body it references, still carries an
    -- unsized recursion oracle: its work is unbounded until sizing, so a
    -- speculating consumer must not evaluate it ahead of demand
  , cgCaptureLayout :: Maybe CapShape
    -- ^ the shape of the capture this code is constructed with, merged
    -- over every certified construction site the global pass saw;
    -- Nothing when the hash is never built into a closure there (or the
    -- global pass failed)
  } deriving (Eq, Show)

-- | The shape of what rides with a hash's code — its capture, as the
-- solved package classes know it. A static schema of the closure value:
-- consumers may use it to choose strategies (where to attempt eager
-- copying, what to clone, what a frame looks like), never to skip the
-- checks that make those strategies safe, so a stale or merged-away
-- shape can cost performance but not correctness.
data CapShape
  = CapData                  -- ^ hereditarily data (any tree of pairs/zeros)
  | CapCode                  -- ^ a bare code constant (a pointer at runtime)
  | CapPair CapShape CapShape -- ^ known pair structure
  | CapOther                 -- ^ anything else: unknown, package, variable
  deriving (Eq, Show)

allDataShape :: CapShape -> Bool
allDataShape = \case
  CapData -> True
  CapPair a b -> allDataShape a && allDataShape b
  _notData -> False

-- | Conservative merge of the layouts a hash is constructed with at
-- different sites: keep what every site agrees on, weaken the rest.
meetShape :: CapShape -> CapShape -> CapShape
meetShape a b
  | a == b = a
meetShape (CapPair a b) (CapPair c d) = CapPair (meetShape a c) (meetShape b d)
meetShape a b
  | allDataShape a && allDataShape b = CapData
  | otherwise = CapOther

-- | Result of 'inferEALLifted': guidance (or a failure verdict) for every
-- lifted body plus the main term's result. Per-body results survive even
-- when main fails, which is the point: they localize exactly which Defer
-- bodies EAL-tag and which don't.
data EALLiftedResult = EALLiftedResult
  { ealGuidance   :: Map (Digest SHA256) (Either EALError CodeGuidance)
  , ealLiftedMain :: Either EALError EALResult
  } deriving (Eq, Show)

-- | The certified capture layouts of a result, keyed by hash: the map a
-- runtime consumer hands to its guided strategies.
ealCaptureLayouts :: EALLiftedResult -> Map (Digest SHA256) CapShape
ealCaptureLayouts lr = Map.fromList
  [ (h, s) | (h, Right g) <- Map.toList (ealGuidance lr)
  , Just s <- [cgCaptureLayout g] ]

-- * Variable supply

freshInt :: EALM Int
freshInt = do
  st <- State.get
  State.put st { esNextVar = esNextVar st + 1 }
  pure (esNextVar st)

freshB :: EALM BVar
freshB = BVar <$> freshInt

freshTau :: EALM Tau
freshTau = VarT <$> freshInt

freshSigma :: EALM Sigma
freshSigma = Sigma <$> freshB <*> freshTau

-- | A fresh code type carrying exactly these tags (captureless).
freshCode :: Set Tag -> EALM Tau
freshCode tags = do
  i <- freshInt
  State.modify $ \st -> st
    { esTagSets = Map.insert i (Map.fromSet (const Nothing) tags)
        (esTagSets st) }
  pure (CodeT i)

-- | Allocate a closure package: the tags of the code class @i@, each
-- carrying this pair's capture. A fresh class per construction, so the
-- head class and the package evolve in lockstep only through joins of
-- the pair itself.
packageClass :: Int -> Sigma -> EALM Int
packageClass i cap = do
  tags <- tagSetOf i
  p <- freshInt
  State.modify $ \st -> st
    { esTagSets = Map.insert p (Map.fromSet (const (Just cap)) tags)
        (esTagSets st) }
  pure p

-- | A bang variable forced to zero, with blame for the forcing.
forcedZeroB :: Blame -> EALM BVar
forcedZeroB blame = do
  b <- freshB
  _ <- constrainB b (ForcedZero blame)
  pure b

-- | Intrinsic sigma of a value constructor: locally unboxed.
plainSigma :: LocTag -> String -> Tau -> EALM Sigma
plainSigma loc what tau = flip Sigma tau <$> forcedZeroB (Blame loc what)

-- * Union-find over bang variables

findB :: BVar -> EALM Int
findB (BVar i) = go i where
  go j = State.gets (Map.lookup j . esParents) >>= \case
    Nothing -> pure j
    Just p -> do
      r <- go p
      unless (r == p) . State.modify $ \st ->
        st { esParents = Map.insert j r (esParents st) }
      pure r

classInfo :: Int -> EALM ClassInfo
classInfo r = State.gets (fromMaybe Unrestricted . Map.lookup r . esClasses)

-- | Assert a constraint on a bang variable's class, merging it with
-- whatever is already known. Returns True if the class changed (the signal
-- 'propagate' uses to detect its fixpoint). Throws on a level over the cap
-- or a boxed/unboxed conflict.
constrainB :: BVar -> ClassInfo -> EALM Bool
constrainB b nc = case nc of
  ForcedLevel n blame | n > levelCap ->
    throwError . EALSolverGaveUp $
      "bang level exceeded cap of " <> show levelCap <> ": " <> show blame
  _notExcessLevel -> do
    r <- findB b
    ci <- classInfo r
    rc <- mergeClasses ci nc
    if rc /= ci
      then do
        State.modify $ \st ->
          st { esClasses = Map.insert r rc (esClasses st) }
        pure True
      else pure False

-- | Combine two constraints on the same class; throws 'EALBoxConflict' if
-- one forces boxing and the other forbids it. On ties this prefers its
-- FIRST argument: 'constrainB' and 'unionB' pass the existing class first
-- and detect change by (in)equality, so re-asserting a constraint that
-- differs only in blame must merge to the existing class exactly, or
-- 'propagate' would see phantom changes and never converge.
mergeClasses :: ClassInfo -> ClassInfo -> EALM ClassInfo
mergeClasses a b = case (a,b) of
  (Unrestricted, _) -> pure b
  (_, Unrestricted) -> pure a
  (ForcedLevel _ l, ForcedZero z) -> throwError $ EALBoxConflict l z
  (ForcedZero z, ForcedLevel _ l) -> throwError $ EALBoxConflict l z
  (ForcedLevel la _, ForcedLevel lb _) -> pure $ if la >= lb then a else b
  _forcedZero -> pure a

-- | Merge two bang classes (used during type unification).
unionB :: BVar -> BVar -> EALM ()
unionB a b = do
  ra <- findB a
  rb <- findB b
  unless (ra == rb) $ do
    ia <- classInfo ra
    ib <- classInfo rb
    mergeClasses ia ib >>= \merged ->
      State.modify $ \st -> st
        { esParents = Map.insert ra rb (esParents st)
        , esClasses = Map.insert rb merged (Map.delete ra (esClasses st))
        }

-- | Is this class forbidden from being boxed?
isForcedZero :: ClassInfo -> Bool
isForcedZero = \case
  ForcedZero _ -> True
  _notForcedZero -> False

-- | The class's known lower bound (zero unless a level has been forced).
getLowerBound :: ClassInfo -> Int
getLowerBound = \case
  ForcedLevel n _ -> n
  _notForcedLevel -> 0

addSumEq :: Blame -> [BVar] -> BVar -> EALM ()
addSumEq blame lhs rhs = State.modify $ \st ->
  st { esSumEqs = SumEq lhs rhs blame : esSumEqs st }

-- * Union-find over tag-set classes

findTag :: Int -> EALM Int
findTag i = State.gets (Map.lookup i . esTagParents) >>= \case
  Nothing -> pure i
  Just p -> do
    r <- findTag p
    unless (r == p) . State.modify $ \st ->
      st { esTagParents = Map.insert i r (esTagParents st) }
    pure r

capturesOf :: Int -> EALM (Map Tag (Maybe Sigma))
capturesOf i = do
  r <- findTag i
  State.gets (fromMaybe mempty . Map.lookup r . esTagSets)

tagSetOf :: Int -> EALM (Set Tag)
tagSetOf = fmap Map.keysSet . capturesOf

-- | Join two code classes: their tag sets UNION, and captures meet only
-- where the SAME tag appears on both sides (same code, same layout) —
-- different tags' captures never unify. This is the one place the type
-- system is flow-like rather than equational. The classes are merged
-- BEFORE the same-tag captures are unified, so self-referential packages
-- (a capture containing its own package, as sized recursion chains build)
-- unify as regular trees: revisiting the merged class no-ops.
unionTags :: LocTag -> Int -> Int -> EALM ()
unionTags loc a b = do
  ra <- findTag a
  rb <- findTag b
  unless (ra == rb) $ do
    ma <- capturesOf ra
    mb <- capturesOf rb
    let pending = [ (ca, cb) | (t, Just ca) <- Map.toList ma
                  , Just (Just cb) <- [Map.lookup t mb] ]
        keep x y = case x of
          Just _  -> x
          Nothing -> y
    State.modify $ \st -> st
      { esTagParents = Map.insert ra rb (esTagParents st)
      , esTagSets = Map.insert rb (Map.unionWith keep ma mb)
          (Map.delete ra (esTagSets st))
      }
    mapM_ (uncurry (unifySigma loc)) pending

-- * Type unification

walkTau :: Tau -> EALM Tau
walkTau = \case
  t@(VarT i) -> State.gets (Map.lookup i . esTVarBinds) >>=
    maybe (pure t) walkTau
  t -> pure t

occurs :: Int -> Tau -> EALM Bool
occurs i t = walkTau t >>= \case
  VarT j -> pure $ i == j
  DataT -> pure False
  CodeT _ -> pure False
  CapT _ -> pure False
  PairT (Sigma _ a) (Sigma _ b) -> (||) <$> occurs i a <*> occurs i b

-- | Bind a type variable. A cyclic binding is not an error: code types are
-- atomic, so a cycle can only thread through pair structure, and an
-- unboundedly nested pair type is data of unknown shape — exactly what
-- 'DataT' already means. The cycle collapses to data (forcing its bangs
-- unboxed); a function value hiding on the cycle then surfaces as a
-- code-vs-data mismatch instead of silently escaping level tracking.
bindTVar :: LocTag -> Int -> Tau -> EALM ()
bindTVar loc i t = do
  cyclic <- occurs i t
  if cyclic
    then do
      State.modify $ \st ->
        st { esTVarBinds = Map.insert i DataT (esTVarBinds st) }
      unifyTau loc t DataT
    else State.modify $ \st ->
      st { esTVarBinds = Map.insert i t (esTVarBinds st) }

describeTau :: Tau -> String
describeTau = \case
  DataT -> "data"
  VarT i -> "t" <> show i
  PairT _ _ -> "pair"
  CodeT _ -> "code"
  CapT _ -> "capture"

-- | The dispatching tag, when unification runs on behalf of one tag's
-- dispatch: a 'CapT' met under a mode resolves to exactly that tag's
-- capture. Outside a dispatch (Nothing) it falls back to unifying with
-- every capture the package holds — sound over-approximation.
type CapMode = Maybe Tag

unifySigma :: LocTag -> Sigma -> Sigma -> EALM ()
unifySigma = unifySigmaAt mempty Nothing

unifyTau :: LocTag -> Tau -> Tau -> EALM ()
unifyTau = unifyTauAt mempty Nothing

unifySigmaAt :: Set Int -> CapMode -> LocTag -> Sigma -> Sigma -> EALM ()
unifySigmaAt vis mode loc (Sigma b1 t1) (Sigma b2 t2) =
  unionB b1 b2 >> unifyTauAt vis mode loc t1 t2

-- | Unification with a visited set of capture-class roots: descending
-- into a class's captures marks it, and meeting it again succeeds
-- coinductively — the regular-tree reading self-referential packages
-- need.
unifyTauAt :: Set Int -> CapMode -> LocTag -> Tau -> Tau -> EALM ()
unifyTauAt vis mode loc a b = do
  a' <- walkTau a
  b' <- walkTau b
  let collapse (Sigma bv t) = do
        _ <- constrainB bv $
          ForcedZero (Blame loc "component of a data pair is unboxed data")
        unifyTauAt vis mode loc t DataT
  case (a', b') of
    (VarT i, VarT j) | i == j -> pure ()
    (VarT i, t) -> bindTVar loc i t
    (t, VarT i) -> bindTVar loc i t
    (DataT, DataT) -> pure ()
    (CodeT i, CodeT j) -> unionTags loc i j
    (CapT i, CapT j) -> unionTags loc i j
    (CapT i, t) -> resolveCapT vis mode loc i t
    (t, CapT i) -> resolveCapT vis mode loc i t
    (PairT a1 a2, PairT b1 b2) ->
      unifySigmaAt vis mode loc a1 b1 >> unifySigmaAt vis mode loc a2 b2
    (PairT p1 p2, DataT) -> collapse p1 >> collapse p2
    (DataT, PairT p1 p2) -> collapse p1 >> collapse p2
    _ -> throwError . EALTypeMismatch loc $
      describeTau a' <> " vs " <> describeTau b'

-- | A capture selection meeting a concrete type: under a dispatch mode
-- whose tag the package holds, exactly that tag's capture is meant;
-- otherwise every capture the package holds must fit (the sound
-- fallback for captures consumed outside their own code's dispatch).
resolveCapT :: Set Int -> CapMode -> LocTag -> Int -> Tau -> EALM ()
resolveCapT vis mode loc i t = do
  r <- findTag i
  unless (Set.member r vis) $ do
    let vis' = Set.insert r vis
    caps <- capturesOf r
    case mode of
      Just h | Just (Just (Sigma _ ct)) <- Map.lookup h caps ->
        unifyTauAt vis' mode loc ct t
      _fallback -> forM_ (Map.elems caps) $ \case
        Just (Sigma _ ct) -> unifyTauAt vis' mode loc ct t
        Nothing -> pure ()

-- * Env usage analysis (contraction detection)

-- | Collect Env (and Unsized) occurrences of one Defer body, keyed by the
-- projection path directly applied to the occurrence. DeferRefs are closed
-- values (their bodies use their own Env, not this frame's).
envUsageL :: Term3Lifting -> Map [Step] (Int, LocTag)
envUsageL = go [] where
  merge = Map.unionWith (\(c1, l1) (c2, _) -> (c1 + c2, l1))
  go proj (anno :< t) = case t of
    StuckFW (LeftSF x) -> go (SL : proj) x
    StuckFW (RightSF x) -> go (SR : proj) x
    -- the accumulated list is innermost projection first, which is the order
    -- the projections apply to the env value, so it is used unreversed
    StuckFW EnvSF -> Map.singleton proj (1, anno)
    Term3LUnsized _ -> Map.singleton proj (1, anno)
    Term3LDeferRef _ -> mempty
    -- unreachable in a lifted term; 'intrinsic' rejects it
    StuckFW (DeferSF _ _) -> mempty
    Term3LCheckingWrapper _ _ c -> go proj c
    BasicFW (PairSF a b) -> merge (go [] a) (go [] b)
    StuckFW (SetEnvSF x) -> go [] x
    -- gate is a value; branch and scrutinee usage flows through the
    -- SetEnv/Pair nodes of the GateSwitch encoding
    StuckFW GateSF -> mempty
    BasicFW ZeroSF -> mempty
    AbortFW _ -> mempty
    _ -> mempty

-- | Is some env path consumed more than once? A path is duplicated if it has
-- two direct uses, or a direct use plus a use of one of its sub-paths.
-- Disjoint sub-path uses (Left once, Right once) are linear destructuring.
contractionSite :: Map [Step] (Int, LocTag) -> Maybe ([Step], LocTag)
contractionSite m =
  let ks = Map.keys m
      subPathUsed p = any (\q -> p /= q && p `isPrefixOf` q) ks
      bad (p, (c, _)) = c >= 2 || (c >= 1 && subPathUsed p)
  in (\(p, (_, l)) -> (p, l)) <$> find bad (Map.toList m)

-- * Constraint generation

data DeferCtx = DeferCtx
  { dcBang  :: BVar -- ^ bang count on this frame's env domain
  , dcTau   :: Tau  -- ^ this frame's env type
  , dcDepth :: Int  -- ^ dispatch nesting depth this frame derives at
  }

-- | Box paths: per-frame (for occurrence depth equations) and global (for
-- computing overall nesting depth). Innermost variable first.
data Paths = Paths
  { pLocal  :: [BVar]
  , pGlobal :: [BVar]
  }

recordLeaf :: Paths -> EALM ()
recordLeaf paths = State.modify $ \st ->
  st { esLeafPaths = pGlobal paths : esLeafPaths st }

-- | Allocate this node's edge box variable and wrap its intrinsic type into
-- the type seen by the parent (view bang = edge boxes + intrinsic bang).
viewNode :: DeferCtx -> Paths -> Term3Lifting -> EALM Sigma
viewNode ctx (Paths loc glob) term@(anno :< _) = do
  w <- freshB
  Sigma bi ti <- intrinsic ctx (Paths (w : loc) (w : glob)) term
  v <- freshB
  addSumEq (Blame anno "view bangs = edge boxes + intrinsic bangs") [w, bi] v
  pure $ Sigma v ti

intrinsic :: DeferCtx -> Paths -> Term3Lifting -> EALM Sigma
intrinsic ctx paths (anno :< t) = case t of
  BasicFW ZeroSF -> do
    recordLeaf paths
    plainSigma anno "Zero is an unboxed value" DataT
  BasicFW (PairSF a b) -> do
    sa@(Sigma _ ta) <- viewNode ctx paths a
    sb@(Sigma bCap _) <- viewNode ctx paths b
    walkTau ta >>= \case
      -- a code-headed pair is a closure package: whatever rides in its
      -- Right belongs to its Left's tags, so record the capture per tag
      -- and expose the position symbolically — joins of different
      -- packages then union instead of unifying captures structurally
      CodeT i -> do
        p <- packageClass i sb
        plainSigma anno "pair constructor is locally unboxed" $
          PairT sa (Sigma bCap (CapT p))
      _notCode -> plainSigma anno "pair constructor is locally unboxed" $
        PairT sa sb
  StuckFW EnvSF -> envOccurrence ctx paths anno
  Term3LUnsized _ -> envOccurrence ctx paths anno
  StuckFW (DeferSF _ _) -> throwError $
    EALInternal "raw DeferSF in a lifted term"
  -- a reference is an atomic code constant; its body's constraints are
  -- derived only where it is applied ('dispatchTag'), fresh per site
  Term3LDeferRef h -> do
    recordLeaf paths
    ct <- freshCode (Set.singleton (TCode h))
    plainSigma anno "code constant is an unboxed value" ct
  StuckFW (SetEnvSF x) -> do
    sx <- viewNode ctx paths x
    si <- freshSigma
    so <- freshSigma
    fnT <- freshTau
    -- pairs are passive conduits: opening the (function, env) pair imposes
    -- no level constraint (the compiled application plumbing re-projects
    -- shared pairs at different depths); only the applied code must
    -- level-match the site
    fnB <- forcedZeroB $ Blame anno "applied function must be unboxed"
    pairB <- freshB
    unifySigma anno sx . Sigma pairB $ PairT (Sigma fnB fnT) si
    State.modify $ \st -> st
      { esApplies = Map.insert (esNextApply st)
          (ApplySite fnT si so (pGlobal paths) (dcDepth ctx) anno mempty)
          (esApplies st)
      , esNextApply = esNextApply st + 1 }
    pure so
  StuckFW GateSF -> do
    recordLeaf paths
    ct <- freshCode (Set.singleton TGate)
    plainSigma anno "gate is an unboxed value" ct
  StuckFW (LeftSF x) -> projection ctx paths anno x fst
  StuckFW (RightSF x) -> projection ctx paths anno x snd
  AbortFW AbortF -> do
    recordLeaf paths
    ct <- freshCode (Set.singleton TAbort)
    plainSigma anno "abort is an unboxed value" ct
  AbortFW (AbortedF _) -> recordLeaf paths >>
    plainSigma anno "aborted value" DataT
  Term3LCheckingWrapper _ _ c -> intrinsic ctx paths c

envOccurrence :: DeferCtx -> Paths -> LocTag -> EALM Sigma
envOccurrence ctx paths anno = do
  recordLeaf paths
  -- the occurrence sits at its env bang's depth OR DEEPER: extra unopened
  -- boxes above a variable are weakening (the flow analyzer's stance).
  -- The slack is also what keeps the solver's repair local: occurrence
  -- equations share their frame bang and their prefix edges, and without
  -- a private absorber the greedy assignment pumps such families forever
  -- (fixing one equation's deficit overshoots its siblings through the
  -- shared edges, which raises the shared bang, which reopens the first).
  d <- freshB
  slack <- freshB
  addSumEq (Blame anno "env occurrence depth = domain bang + slack")
    [dcBang ctx, slack] d
  addSumEq (Blame anno "env occurrence depth matches its path boxes")
    (pLocal paths) d
  b <- forcedZeroB $ Blame anno "variable occurrence is locally unboxed"
  pure . Sigma b $ dcTau ctx

projection :: DeferCtx -> Paths -> LocTag -> Term3Lifting
  -> ((Sigma, Sigma) -> Sigma) -> EALM Sigma
projection ctx paths anno x pick = do
  sx <- viewNode ctx paths x
  sl <- freshSigma
  sr <- freshSigma
  -- pairs are passive conduits: projecting one imposes no level constraint
  pB <- freshB
  unifySigma anno sx . Sigma pB $ PairT sl sr
  pure $ pick (sl, sr)

-- * Application dispatch

-- | Dispatch every tag that has flowed into every apply site's function
-- position, to a fixpoint: dispatching a code tag derives its body, which
-- registers new sites and can grow other sites' tag sets. A function
-- position that never resolves (nothing flows there but the program's
-- unknown input) is tolerated without constraints — input is data by the
-- runtime contract, and applying data sticks only when demanded.
resolveApplies :: EALM ()
resolveApplies = loop (0 :: Int) where
  loop n = do
    when (n > 10000) . throwError $
      EALSolverGaveUp "application dispatch did not converge"
    keys <- State.gets (Map.keys . esApplies)
    changed <- foldM (\acc k -> (acc ||) <$> resolveSite k) False keys
    when changed $ loop (n + 1)
  resolveSite k = State.gets (Map.lookup k . esApplies) >>= \case
    Nothing -> pure False
    Just site -> walkTau (apFn site) >>= \case
      VarT _ -> pure False
      CodeT i -> dispatchNew k site =<< tagSetOf i
      -- a capture selection applied directly: any code its package's
      -- captures can hold may run here
      CapT i -> dispatchNew k site =<< fnTagsOfCaptures mempty i
      -- applying data sticks immediately at runtime, and stuckness is a
      -- value until demanded — bounded work, so nothing for the
      -- certificate to reject. (Shape errors are the language checker's
      -- job; sized recursion machinery really does leave data in dead
      -- applied positions, e.g. the abort base's escape path.) Note this
      -- is more tolerant than a flow analyzer's must-fail rule: with
      -- unification a data binding can shadow code that flow would have
      -- kept as a separate union member, so data-here must not be read
      -- as data-only.
      DataT -> pure False
      other -> throwError . EALTypeMismatch (apLoc site) $
        "applied value is " <> describeTau other <> ", not code"
  dispatchNew k site tags = do
    let new = Set.difference tags (apDispatched site)
    if Set.null new
      then pure False
      else do
        -- mark first: dispatch can grow this very set, and the next
        -- round picks up only what is genuinely new
        State.modify $ \st -> st
          { esApplies = Map.insert k
              site { apDispatched = Set.union (apDispatched site) tags }
              (esApplies st) }
        mapM_ (dispatchTag site) (Set.toList new)
        pure True

-- | The code tags a capture position can hold, for a capture applied as
-- a function: the union over the package's captures' own code, chasing
-- nested selections coinductively.
fnTagsOfCaptures :: Set Int -> Int -> EALM (Set Tag)
fnTagsOfCaptures vis i = do
  r <- findTag i
  if Set.member r vis
    then pure mempty
    else do
      caps <- capturesOf r
      fmap Set.unions . mapM (tagsIn (Set.insert r vis)) $ Map.elems caps
  where
    tagsIn vis' = \case
      Just (Sigma _ t) -> walkTau t >>= \case
        CodeT j -> tagSetOf j
        CapT j  -> fnTagsOfCaptures vis' j
        _       -> pure mempty
      Nothing -> pure mempty

-- | Emit the constraints of applying one tag at one site.
dispatchTag :: ApplySite -> Tag -> EALM ()
dispatchTag site tag = case tag of
  TCode h -> do
    when (apDepth site >= dispatchDepthCap) . throwError . EALSolverGaveUp $
      "code dispatch depth exceeded " <> show dispatchDepthCap
        <> " (unbounded self-application?): " <> show (apLoc site)
    (fi, body) <- State.gets (Map.lookup h . esBodies) >>= \case
      Just fb -> pure fb
      Nothing -> throwError . EALInternal $
        "dispatched code not in the DeferMap " <> show h
    bEnv <- freshB
    tEnv <- freshTau
    forM_ (contractionSite (envUsageL body)) $ \(path, uloc) ->
      void . constrainB bEnv . ForcedLevel 1 $
        Blame uloc ("env path " <> showSteps path <> " duplicated in "
          <> show fi)
    State.modify $ \st ->
      st { esDefers = Map.insertWith (<>) fi [bEnv] (esDefers st) }
    sBody <- viewNode (DeferCtx bEnv tEnv (apDepth site + 1))
      (Paths [] (apGlobal site)) body
    -- the operand meets the domain under this tag's mode: capture
    -- selections inside it resolve to THIS tag's capture
    unifySigmaAt mempty (Just tag) (apLoc site) (apEnv site)
      (Sigma bEnv tEnv)
    unifySigma (apLoc site) (apRes site) sBody
  TGate -> do
    scrB <- forcedZeroB $ Blame loc "gate scrutinee must be unboxed data"
    unifySigma loc (apEnv site) (Sigma scrB DataT)
    gfn <- plainSigma loc "gate switch function is locally unboxed"
      =<< freshCode (Set.singleton TGateFn)
    unifySigma loc (apRes site) gfn
  TGateFn -> do
    sbE <- freshSigma
    sbT <- freshSigma
    -- the branch pair is a passive conduit like any other pair
    branchesB <- freshB
    unifySigma loc (apEnv site) (Sigma branchesB (PairT sbE sbT))
    -- the switch can yield either branch: both JOIN into the result (code
    -- positions union, data collapses) instead of the branches unifying
    -- with each other structurally
    unifySigma loc (apRes site) sbE
    unifySigma loc (apRes site) sbT
  -- abort messages need no shape or bang constraint: the runtime
  -- truncates non-data message components to Zero
  TAbort -> do
    cont <- plainSigma loc "abort continuation is locally unboxed"
      =<< freshCode (Set.singleton TAbortCont)
    unifySigma loc (apRes site) cont
  TAbortCont -> unifySigma loc (apEnv site) (apRes site)
  where loc = apLoc site

-- * Constraint solving

data EqR = EqR
  { eqLhs   :: [Int]
  , eqRhs   :: Int
  , eqBlame :: Blame
  }

resolveEqs :: EALM [EqR]
resolveEqs = State.gets esSumEqs >>= mapM res where
  res (SumEq lhs rhs blame) =
    EqR <$> mapM findB lhs <*> findB rhs <*> pure blame

-- | Propagate zero-forcings and lower bounds through the sum equations to a
-- fixpoint.
propagate :: EALM ()
propagate = do
  eqCount <- State.gets (length . esSumEqs)
  loop (eqCount * 4 + 64)
  where
    loop n = do
      when (n <= 0) . throwError $
        EALSolverGaveUp "constraint propagation did not converge"
      changed <- resolveEqs >>= foldM (\acc eq -> (acc ||) <$> step eq) False
      when changed $ loop (n - 1)
    step (EqR lhs rhs blame) = do
      let derived what = let Blame l s = blame in Blame l (what <> ": " <> s)
      ri <- classInfo rhs
      c1 <- case ri of
        ForcedZero _ -> foldM
          (\acc l -> fmap (acc ||) . constrainB (BVar l) $
            ForcedZero (derived "summand of an unboxed total"))
          False lhs
        _notZero -> pure False
      lhsIs <- mapM (classInfo <=< findB . BVar) lhs
      c2 <- if all isForcedZero lhsIs
        then constrainB (BVar rhs) $ ForcedZero (derived "all summands unboxed")
        else pure False
      let sumLB = sum $ fmap getLowerBound lhsIs
      c3 <- if sumLB > 0
        then constrainB (BVar rhs) $
          ForcedLevel sumLB (derived "sum of summand lower bounds")
        else pure False
      ri' <- classInfo =<< findB (BVar rhs)
      c4 <- case ([l | (l, i) <- zip lhs lhsIs, not $ isForcedZero i], ri') of
        ([lone], ForcedLevel lb _) -> constrainB (BVar lone) $
          ForcedLevel lb (derived "only boxable summand")
        _notSingularBoxable -> pure False
      pure $ c1 || c2 || c3 || c4

-- | Find concrete values satisfying every sum equation, starting from the
-- propagated lower bounds and greedily raising free variables.
assignValues :: EALM (Map Int Int)
assignValues = do
  eqs <- resolveEqs
  classes <- State.gets esClasses
  let look vals r = fromMaybe 0 $ Map.lookup r vals
      vals0 = fmap getLowerBound classes
      isZeroForced r = maybe False isForcedZero $ Map.lookup r classes
      memberCount :: Map Int Int
      memberCount = Map.fromListWith (+) $
        concatMap (\eq -> [(l, 1) | l <- eqLhs eq]) eqs
      adjust (vals, ch) (EqR lhs rhs blame) =
        let s = sum $ fmap (look vals) lhs
            r = look vals rhs
            giveUp what = throwError . EALSolverGaveUp $
              what <> ": " <> show blame
        in case compare s r of
          EQ -> pure (vals, ch)
          GT | isZeroForced rhs -> giveUp "sum exceeds an unboxed total"
             | s > levelCap -> giveUp "assignment exceeded level cap"
             | otherwise -> pure (Map.insert rhs s vals, True)
          LT -> case filter (not . isZeroForced) lhs of
            [] -> giveUp "no boxable position to absorb required boxes"
            frees ->
              let pick = minimumBy
                    (comparing $ \l -> (look memberCount l, l)) frees
                  v' = look vals pick + (r - s)
              in if v' > levelCap
                then giveUp "assignment exceeded level cap"
                else pure (Map.insert pick v' vals, True)
      loop n vals
        | n <= 0 = throwError $ EALSolverGaveUp "assignment did not converge"
        | otherwise = do
            (vals', changed) <- foldM adjust (vals, False) eqs
            if changed then loop (n - 1) vals' else pure vals'
  final <- loop (length eqs * 4 + 16) vals0
  -- verify the assignment exactly satisfies every equation
  mapM_ (\(EqR lhs rhs blame) ->
    when (sum (fmap (look final) lhs) /= look final rhs) .
      throwError . EALSolverGaveUp $
        "assignment verification failed: " <> show blame) eqs
  pure final

-- * Entry points

-- | Shared driver: constrain one top-level term (the main program, or one
-- lifted body treated as a program over its own env), dispatch its
-- applications, solve, and verify.
analyzeTop :: String -> Term3Lifting -> EALM (BVar, Tau, Sigma, Map Int Int)
analyzeTop what term = do
  bEnv <- freshB
  tEnv <- freshTau
  case contractionSite (envUsageL term) of
    Just (path, uloc) -> void . constrainB bEnv . ForcedLevel 1 $
      Blame uloc (what <> " path " <> showSteps path <> " duplicated")
    Nothing -> pure ()
  sRes <- viewNode (DeferCtx bEnv tEnv 0) (Paths [] []) term
  resolveApplies
  propagate
  vals <- assignValues
  pure (bEnv, tEnv, sRes, vals)

leafDepths :: Map Int Int -> EALM [Int]
leafDepths vals = State.gets esLeafPaths >>= mapM depth where
  value r = fromMaybe 0 $ Map.lookup r vals
  depth vs = sum . fmap value <$> mapM findB vs

-- * Lifted inference

-- | Direct DeferRef dependencies of a lifted term.
refsOf :: Term3Lifting -> Set (Digest SHA256)
refsOf (_ :< t) = case t of
  Term3LDeferRef h -> Set.singleton h
  x -> foldMap refsOf x

-- | Does this term, or any body it references, still contain an unsized
-- recursion oracle? (The map is a DAG, so the walk terminates.)
unsizedIn :: Map (Digest SHA256) (FunctionIndex, Term3Lifting)
          -> Term3Lifting -> Bool
unsizedIn bodies = go where
  go (_ :< t) = case t of
    Term3LUnsized _  -> True
    Term3LDeferRef h -> maybe False (go . snd) (Map.lookup h bodies)
    x                -> any go x

-- | Infer one lifted body standalone, dispatching the code it applies from
-- the DeferMap, and package the result as guidance. Failures are localized
-- per body; the solved env bang is this derivation's, and a dispatch
-- site's fresh derivation may solve differently.
summarizeBody :: Map (Digest SHA256) (FunctionIndex, Term3Lifting)
              -> FunctionIndex -> Term3Lifting
              -> Either EALError CodeGuidance
summarizeBody bodies fi body =
  State.evalState (runExceptT go) (initEALState { esBodies = bodies }) where
    go = do
      (bEnv, _, _, vals) <- analyzeTop
        ("env of lifted body " <> show fi) body
      let value r = fromMaybe 0 $ Map.lookup r vals
      envBang <- value <$> findB bEnv
      depths <- leafDepths vals
      pure CodeGuidance
        { cgIndex = fi
        , cgUsage = fmap fst (envUsageL body)
        , cgEnvBang = envBang
        , cgMaxLevel = maximum (0 : depths)
        , cgSpeculatable = not (unsizedIn bodies body)
        , cgCaptureLayout = Nothing -- filled from the global pass
        }

-- | Ground every package class into capture shapes, merged per hash over
-- all the construction sites this run saw.
groundCaptureShapes :: EALM (Map (Digest SHA256) CapShape)
groundCaptureShapes = do
  classes <- State.gets (Map.elems . esTagSets)
  fmap (Map.fromListWith meetShape . concat . concat) .
    forM classes $ \m ->
      forM (Map.toList m) $ \case
        (TCode h, Just sig) -> do
          s <- shapeOf sig
          pure [(h, s)]
        _bare -> pure []
  where
    shapeOf (Sigma _ t) = walkTau t >>= \case
      DataT -> pure CapData
      PairT a b -> CapPair <$> shapeOf a <*> shapeOf b
      CodeT _ -> pure CapCode
      _other -> pure CapOther

-- | Infer EAL annotations over a lifted program: each unique Defer body
-- first gets a standalone verdict (which bodies tag, which fail, and why),
-- then main is analyzed globally, deriving each applied body's constraints
-- fresh per apply site per tag. Bodies the program carries but never
-- applies contribute their standalone bangs and levels to the result — the
-- certificate covers all the code the program contains.
inferEALLifted :: DeferMap -> Term3Lifting -> EALLiftedResult
inferEALLifted (DeferMap dm) mainTerm =
  EALLiftedResult guidance mainResult where
    bodyResults = Map.mapWithKey summarize dm
    summarize _h (fi, body) = withDeps body $ summarizeBody dm fi body
    -- capture layouts come from the global pass, which sees every
    -- certified construction site
    layouts = case withDeps mainTerm (Right ()) of
      Right () -> either (const mempty) snd runMain
      Left _   -> mempty
    guidance = Map.mapWithKey
      (\h -> fmap (\g -> g { cgCaptureLayout = Map.lookup h layouts }))
      bodyResults
    mainResult = withDeps mainTerm (mergeStandalone . fst <$> runMain)
    resultOf d = case Map.lookup d bodyResults of
      Just r  -> r
      Nothing -> Left $ EALDependencyFailed d
    -- gate on direct dependencies' verdicts; transitive failures propagate
    -- through the verdicts themselves. The map is a DAG (bodies reference
    -- only hashes of subterms), so this lazy self-reference through
    -- bodyResults terminates.
    withDeps :: Term3Lifting -> Either EALError a -> Either EALError a
    withDeps term k =
      case [d | d <- Set.toList (refsOf term), Left _ <- [resultOf d]] of
        (d:_) -> Left $ EALDependencyFailed d
        []    -> k
    certified = rights (Map.elems bodyResults)
    mergeStandalone r = r
      { ealDeferBangs = Map.unionWith max (ealDeferBangs r) $
          Map.fromListWith max [(cgIndex g, cgEnvBang g) | g <- certified]
      , ealMaxLevel = maximum (ealMaxLevel r : fmap cgMaxLevel certified)
      }
    runMain = State.evalState (runExceptT goMain)
      (initEALState { esBodies = dm })
    goMain = do
      (bMain, _, _, vals) <- analyzeTop "program input" mainTerm
      let value r = fromMaybe 0 $ Map.lookup r vals
      topBang <- value <$> findB bMain
      defers <- State.gets esDefers >>=
        traverse (fmap (maximum . (0 :)) . traverse (fmap value . findB))
      depths <- leafDepths vals
      shapes <- groundCaptureShapes
      pure ( EALResult
               { ealTopLevelBang = topBang
               , ealDeferBangs = defers
               , ealMaxLevel = maximum (0 : depths)
               }
           , shapes )

-- | The composed pipeline: lift, then infer over the lifted form.
inferEALWithLifting :: Term3 -> EALLiftedResult
inferEALWithLifting = uncurry inferEALLifted . deferLift

-- | Infer over a sized, runnable term: the candidate post-sizing gate
-- position. Sizing has already resolved Unsized recursion to concrete
-- iteration machinery, so the verdict here is about the code that will
-- actually run — the pre-sizing verdict is about the recursion scaffolding
-- as well.
inferEALCompiled :: CompiledExpr -> EALLiftedResult
inferEALCompiled = inferEALWithLifting . compiled2Term3
