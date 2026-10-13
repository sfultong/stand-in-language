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
-- Appliable values are code tags with an interface. A defer reference is
-- typed as a code constant carrying its content hash ('CodeT' over 'Tag'
-- sets), gates and aborts are built-in tags, and unification at code
-- positions takes the UNION of tags rather than equating anything — so a
-- gate join of structurally different functions is a set union, not a
-- unification failure. Every DeferRef OCCURRENCE instantiates the
-- referenced body once (a fresh copy of its constraints, served from a
-- per-body template), and the tag minted for the occurrence carries that
-- instance's 'Iface': the env it consumes and the value it yields. This is
-- let-polymorphism over the DeferMap: bodies are closed, the map is a DAG,
-- so instances are finite by construction. Application is a deferred
-- constraint: every SetEnv registers an apply site, and a post-walk
-- fixpoint ('resolveApplies') unifies the site's operand and result with
-- the interface of every tag that flows into its function position.
-- Dispatch never derives anything — it only unifies — so the fixpoint is
-- bounded by sites times tags and terminates without a budget.
--
-- Two consequences of this skeleton:
--
--   * A type cycle through pair structure alone is unboundedly nested pair
--     data of unknown shape — exactly what 'DataT' already means — and
--     collapses to data; a function value hiding on such a cycle then
--     surfaces as a code-vs-data mismatch instead of escaping tracking.
--   * A cycle through an INTERFACE — a code class reachable from its own
--     env or result — is self-application: the function's argument would
--     have to contain the function. It has no finite derivation and is
--     rejected outright ('selfReferential'), the role the occurs check
--     plays for arrow types. Cycles through captures are not cycles of
--     this kind: a package capturing a package of its own shape is a
--     regular tree (sized recursion chains build exactly these).
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

import Control.Applicative ((<|>))
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
import Telomare.Error (Blame (..), EALError (..), renderEALError)
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

-- | The interface of one instance of a lifted body: the env it consumes
-- and the value it yields. Minted at the DeferRef occurrence that
-- instantiates the body, carried with the body's tag through every join,
-- and unified with every apply site the tag reaches. This is the arrow
-- structure of a code value.
data Iface = Iface
  { ifEnv :: Sigma
  , ifRes :: Sigma
  } deriving Show

-- | What a code class knows about one of its tags: the capture that rides
-- with the tag's code (Just for closure packages, Nothing for bare code
-- and built-ins) and the interface of the instance the tag came from
-- (Nothing for built-ins, which dispatch by rule).
data TagInfo = TagInfo
  { tiCapture :: Maybe Sigma
  , tiIface   :: Maybe Iface
  } deriving Show

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
  | AbortedT           -- ^ a value that never exists: the result of an
                       --   abort that really aborts (a pair message), or
                       --   of applying such a result. Bottom of the type
                       --   lattice — it absorbs every unification without
                       --   binding anything, so the dead bottom of a sized
                       --   recursion chain joins with the live links
  deriving Show

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
  , apLoc        :: LocTag
  , apDispatched :: Set Tag -- ^ tags already dispatched at this site
  }

data EALState = EALState
  { esNextVar    :: Int
  , esTVarBinds  :: Map Int Tau
  , esParents    :: Map Int Int       -- ^ union-find parent pointers (bangs)
  , esClasses    :: Map Int ClassInfo -- ^ info stored at roots
  , esTagParents :: Map Int Int       -- ^ union-find parent pointers (tags)
  , esTagSets    :: Map Int (Map Tag TagInfo)
    -- ^ per class root: its tags, each with the capture that rides with
    -- that tag's code and the interface of the instance it came from
  , esSumEqs     :: [SumEq]
  , esSumEqCount :: !Int              -- ^ length of 'esSumEqs', so template
                                      -- capture can take a delta in O(delta)
  , esApplies    :: Map Int ApplySite
  , esNextApply  :: Int
  , esDefers     :: [(FunctionIndex, BVar)]
    -- ^ per body instance: its env domain bang (reported per Defer as
    -- their max); append-only, so template capture can take a delta
  , esDeferCount :: !Int              -- ^ length of 'esDefers'
  , esLeafPaths  :: [[BVar]]          -- ^ root-to-leaf box paths, for max
                                      -- depth
  , esLeafCount  :: !Int              -- ^ length of 'esLeafPaths'
  , esBodies     :: Map (Digest SHA256) (FunctionIndex, Term3Lifting)
    -- ^ the DeferMap: a DeferRef occurrence instantiates its body from here
  , esTemplates  :: Map (Digest SHA256) BodyTemplate
    -- ^ per body: the reusable constraint delta of its walk
  }

initEALState :: EALState
initEALState = EALState
  { esNextVar = 0
  , esTVarBinds = mempty
  , esParents = mempty
  , esClasses = mempty
  , esTagParents = mempty
  , esTagSets = mempty
  , esSumEqs = mempty
  , esSumEqCount = 0
  , esApplies = mempty
  , esNextApply = 0
  , esDefers = mempty
  , esDeferCount = 0
  , esLeafPaths = mempty
  , esLeafCount = 0
  , esBodies = mempty
  , esTemplates = mempty
  }

-- | One body's walk, captured as a reusable constraint template. The walk
-- of a lifted body is operand-independent — operands meet the instance
-- only through interface unification at apply sites — and every variable
-- it mints is drawn from one contiguous block starting at 'btBase', so a
-- later occurrence of the same body is served by an offset copy of this
-- delta instead of a monadic re-walk. The walk of a body instantiates the
-- bodies it references, so the block holds those nested instances too and
-- an offset copy carries its own copies of them. The occurrence's
-- contribution is factored out as a parameter: its global box path
-- (stored stripped from leaf paths and nested sites, re-appended at
-- instantiation).
data BodyTemplate = BodyTemplate
  { btIndex        :: FunctionIndex     -- ^ for error reporting
  , btBase         :: Int               -- ^ first variable of the block
  , btSize         :: Int               -- ^ variables the walk minted
  , btParents      :: [(Int, Int)]      -- ^ union-find edges inside the block
  , btClasses      :: [(Int, ClassInfo)]
  , btTVarBinds    :: [(Int, Tau)]
  , btTagParents   :: [(Int, Int)]
  , btTagSets      :: [(Int, Map Tag TagInfo)]
  , btSumEqs       :: [SumEq]
  , btLeafPrefixes :: [[BVar]]        -- ^ block-local leaf paths, occurrence
                                      -- path appended at instantiation
  , btApplies      :: [ApplySite]       -- ^ nested sites; 'apGlobal' holds the
                                      -- block-local prefix only
  , btDefers       :: [(FunctionIndex, BVar)] -- ^ env bangs of the instances
                                              -- inside the block
  , btEnvBang      :: BVar              -- ^ interface: frame env domain bang
  , btEnvTau       :: Tau               -- ^ interface: frame env type
  , btResult       :: Sigma             -- ^ interface: body result
  }

type EALM = ExceptT EALError (State EALState)

data EALResult = EALResult
  { ealTopLevelBang :: Int                  -- ^ bang on the program input
  , ealDeferBangs   :: Map FunctionIndex Int -- ^ env domain bang per Defer
  , ealMaxLevel     :: Int                  -- ^ max box nesting depth
  , ealMainShape    :: CapShape
    -- ^ the resolved shape of the whole program's value. Certification
    -- tolerates applied data (it sticks at runtime), so a driver that
    -- needs main to be an appliable function must ask this shape:
    -- 'allDataShape' here means the program is hereditarily data and can
    -- never consume input.
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
  { cgIndex         :: FunctionIndex -- ^ first-seen index, for reporting
  , cgUsage         :: Map [Step] Int
    -- ^ env occurrences per projection path: disjoint single-use paths
    -- are linear destructuring (routable as wiring, no sharing needed);
    -- a path counted twice, or overlapping a used sub-path, is where
    -- duplication actually happens
  , cgEnvBang       :: Int       -- ^ solved bang on the body's env domain
                                --   (this body's standalone derivation; a
                                --   dispatch site's derivation may differ)
  , cgMaxLevel      :: Int       -- ^ max box depth inside the body (including
                                --   depths of bodies it applies)
  , cgSpeculatable  :: Bool
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

-- | A fresh code class holding exactly these tags.
freshCode :: Map Tag TagInfo -> EALM Tau
freshCode tags = do
  i <- freshInt
  State.modify $ \st -> st { esTagSets = Map.insert i tags (esTagSets st) }
  pure (CodeT i)

-- | A fresh code class holding one built-in tag (no capture, no interface:
-- built-ins dispatch by rule).
builtinCode :: Tag -> EALM Tau
builtinCode tag = freshCode (Map.singleton tag (TagInfo Nothing Nothing))

-- | Allocate a closure package: the tags of the code class @i@ (with their
-- interfaces), each now carrying this pair's capture. A fresh class per
-- construction, so the head class and the package evolve in lockstep only
-- through joins of the pair itself.
packageClass :: Int -> Sigma -> EALM Int
packageClass i cap = do
  infos <- capturesOf i
  p <- freshInt
  State.modify $ \st -> st
    { esTagSets = Map.insert p (fmap (\ti -> ti { tiCapture = Just cap }) infos)
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
  (Unrestricted, _)                    -> pure b
  (_, Unrestricted)                    -> pure a
  (ForcedLevel _ l, ForcedZero z)      -> throwError $ EALBoxConflict l z
  (ForcedZero z, ForcedLevel _ l)      -> throwError $ EALBoxConflict l z
  (ForcedLevel la _, ForcedLevel lb _) -> pure $ if la >= lb then a else b
  _forcedZero                          -> pure a

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
  st { esSumEqs = SumEq lhs rhs blame : esSumEqs st
     , esSumEqCount = esSumEqCount st + 1 }

-- * Union-find over tag-set classes

findTag :: Int -> EALM Int
findTag i = State.gets (Map.lookup i . esTagParents) >>= \case
  Nothing -> pure i
  Just p -> do
    r <- findTag p
    unless (r == p) . State.modify $ \st ->
      st { esTagParents = Map.insert i r (esTagParents st) }
    pure r

capturesOf :: Int -> EALM (Map Tag TagInfo)
capturesOf i = do
  r <- findTag i
  State.gets (fromMaybe mempty . Map.lookup r . esTagSets)

tagSetOf :: Int -> EALM (Set Tag)
tagSetOf = fmap Map.keysSet . capturesOf

-- | Two records of the same tag meeting: captures unify (same code, same
-- layout) and so do interfaces (two instances of one body flowing to one
-- position are used as one, the let-polymorphic reading of a join).
unifyTagInfo :: LocTag -> TagInfo -> TagInfo -> EALM ()
unifyTagInfo loc (TagInfo ca ia) (TagInfo cb ib) = do
  case (ca, cb) of
    (Just x, Just y) -> unifySigma loc x y
    _oneSided        -> pure ()
  case (ia, ib) of
    (Just (Iface ea ra), Just (Iface eb rb)) ->
      unifySigma loc ea eb >> unifySigma loc ra rb
    _oneSided -> pure ()

-- | Fill the gaps of one record from another.
mergeTagInfo :: TagInfo -> TagInfo -> TagInfo
mergeTagInfo (TagInfo ca ia) (TagInfo cb ib) =
  TagInfo (ca <|> cb) (ia <|> ib)

-- | Join two code classes: their tag sets UNION, and captures and
-- interfaces meet only where the SAME tag appears on both sides —
-- different tags' records never unify. This is the one place the type
-- system is flow-like rather than equational. The classes are merged
-- BEFORE the same-tag records are unified, so self-referential packages
-- (a capture containing its own package, as sized recursion chains build)
-- unify as regular trees: revisiting the merged class no-ops. A join that
-- closes a cycle through an interface is self-application and is
-- rejected ('selfReferential').
unionTags :: LocTag -> Int -> Int -> EALM ()
unionTags loc a b = do
  ra <- findTag a
  rb <- findTag b
  unless (ra == rb) $ do
    ma <- capturesOf ra
    mb <- capturesOf rb
    let pending = [ (ia, ib) | (t, ia) <- Map.toList ma
                  , Just ib <- [Map.lookup t mb] ]
    State.modify $ \st -> st
      { esTagParents = Map.insert ra rb (esTagParents st)
      , esTagSets = Map.insert rb (Map.unionWith mergeTagInfo ma mb)
          (Map.delete ra (esTagSets st))
      }
    mapM_ (uncurry (unifyTagInfo loc)) pending
    rejectSelfReference loc rb

-- | Is this code class reachable from its own interfaces, through pair
-- structure and other classes' interfaces? Only the ARGUMENT half of an
-- env (its Left, by the compiled convention a body's argument is @Left
-- Env@ and its captures @Right Env@) and the result are followed. The
-- capture half is deliberately not: a closure whose captures hold a
-- closure of its own code is a regular shape — @\\x -> g (g x)@ with @g@
-- another such partial, or a sized recursion chain — just as captures
-- never appear in a simple type. A function whose argument contains the
-- function is the one thing with no finite derivation.
-- Returns the cycle as the tags whose interfaces it threads, in order.
selfReferential :: Int -> EALM (Maybe [Tag])
selfReferential r0 = classIfaces mempty r0 where
  classIfaces vis r = do
    infos <- capturesOf r
    let vis' = Set.insert r vis
    starts <- fmap concat . forM
      [ (t, i) | (t, TagInfo _ (Just i)) <- Map.toList infos ] $
        \(t, Iface e res) -> do
          arg <- argumentOf e
          pure [(t, arg), (t, res)]
    firstJustM (\(t, Sigma _ ty) -> fmap (t :) <$> tau vis' ty) starts
  -- an env's argument half only; an unresolved or data env has nothing
  -- to follow
  argumentOf (Sigma b t) = walkTau t >>= \case
    PairT arg _caps -> pure arg
    _notPair -> pure (Sigma b DataT)
  tau vis t = walkTau t >>= \case
    VarT _ -> pure Nothing
    DataT -> pure Nothing
    CapT _ -> pure Nothing
    PairT (Sigma _ x) (Sigma _ y) ->
      tau vis x >>= maybe (tau vis y) (pure . Just)
    CodeT c -> do
      r <- findTag c
      if r == r0 then pure (Just [])
        else if Set.member r vis then pure Nothing
        else classIfaces vis r

-- | Reject a code class that has just become self-referential: the
-- function it names is applied to (or yields) a value containing itself,
-- which has no finite derivation — this is the occurs check of arrow
-- types, stated on interfaces.
rejectSelfReference :: LocTag -> Int -> EALM ()
rejectSelfReference loc c = selfReferential c >>= \case
  Nothing -> pure ()
  Just cycleTags -> do
    bodies <- State.gets esBodies
    let name = \case
          TCode h -> maybe (take 8 (show h)) (show . fst) (Map.lookup h bodies)
          builtin -> show builtin
    throwError . EALTypeMismatch loc $
      "self-application: a function is applied to a value that contains the"
        <> " function itself, so its argument would have to contain its own"
        <> " interface (cycle through " <> unwords (fmap name cycleTags) <> ")"

firstJustM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
firstJustM _ [] = pure Nothing
firstJustM f (x:xs) = f x >>= maybe (firstJustM f xs) (pure . Just)

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
  AbortedT -> pure False
  PairT (Sigma _ a) (Sigma _ b) -> (||) <$> occurs i a <*> occurs i b

-- | Bind a type variable. A cyclic binding through pair structure is not
-- an error: an unboundedly nested pair type is data of unknown shape —
-- exactly what 'DataT' already means. The cycle collapses to data
-- (forcing its bangs unboxed); a function value hiding on the cycle then
-- surfaces as a code-vs-data mismatch instead of silently escaping level
-- tracking. A binding that closes a cycle through a code class's
-- interface is self-application and is rejected: the classes the bound
-- structure exposes are checked, since any such cycle passes through
-- the first class reached.
bindTVar :: LocTag -> Int -> Tau -> EALM ()
bindTVar loc i t = do
  cyclic <- occurs i t
  if cyclic
    then do
      State.modify $ \st ->
        st { esTVarBinds = Map.insert i DataT (esTVarBinds st) }
      unifyTau loc t DataT
    else do
      State.modify $ \st ->
        st { esTVarBinds = Map.insert i t (esTVarBinds st) }
      exposedClasses t >>= mapM_ (rejectSelfReference loc)

-- | The code classes a type exposes through pair structure alone.
exposedClasses :: Tau -> EALM [Int]
exposedClasses t = walkTau t >>= \case
  CodeT c -> pure [c]
  PairT (Sigma _ a) (Sigma _ b) -> (<>) <$> exposedClasses a <*> exposedClasses b
  _leaf -> pure []

describeTau :: Tau -> String
describeTau = \case
  DataT -> "data"
  VarT i -> "t" <> show i
  PairT _ _ -> "pair"
  CodeT _ -> "code"
  CapT _ -> "capture"
  AbortedT -> "aborted"

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
    -- bottom absorbs: a value that never exists fits every position, and
    -- binds no variable (the position stays open for the values that do
    -- exist)
    (AbortedT, _) -> pure ()
    (_, AbortedT) -> pure ()
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
    _ -> do
      da <- deepShowTau 5 a'
      db <- deepShowTau 5 b'
      throwError . EALTypeMismatch loc $
        describeTau a' <> " vs " <> describeTau b'
          <> " [mode " <> show mode <> "; " <> da <> " ||| " <> db <> "]"

-- | Resolved rendering of a type to bounded depth, for mismatch reports.
deepShowTau :: Int -> Tau -> EALM String
deepShowTau n t
  | n <= 0 = pure "..."
  | otherwise = walkTau t >>= \case
      DataT -> pure "D"
      VarT i -> pure ("t" <> show i)
      CodeT i -> do
        r <- findTag i
        tags <- tagSetOf i
        pure ("Code#" <> show r <> show (Set.toList tags))
      CapT i -> do
        r <- findTag i
        pure ("Cap#" <> show r)
      AbortedT -> pure "_|_"
      PairT (Sigma _ a) (Sigma _ b) -> do
        sa <- deepShowTau (n - 1) a
        sb <- deepShowTau (n - 1) b
        pure ("(" <> sa <> ", " <> sb <> ")")

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
      Just h | Just (TagInfo (Just (Sigma _ ct)) _) <- Map.lookup h caps ->
        unifyTauAt vis' mode loc ct t
      _fallback -> forM_ (Map.elems caps) $ \case
        TagInfo (Just (Sigma _ ct)) _ -> unifyTauAt vis' mode loc ct t
        TagInfo Nothing _ -> pure ()

-- * Env usage analysis (contraction detection)

-- | Collect Env (and Unsized) occurrences of one Defer body, keyed by the
-- projection path directly applied to the occurrence. DeferRefs are closed
-- values (their bodies use their own Env, not this frame's).
envUsageL :: Term3Lifting -> Map [Step] (Int, LocTag)
envUsageL = go [] where
  merge = Map.unionWith (\(c1, l1) (c2, _) -> (c1 + c2, l1))
  go proj (anno :< t) = case t of
    StuckFW (LeftSF x)          -> go (SL : proj) x
    StuckFW (RightSF x)         -> go (SR : proj) x
    -- the accumulated list is innermost projection first, which is the order
    -- the projections apply to the env value, so it is used unreversed
    StuckFW EnvSF               -> Map.singleton proj (1, anno)
    Term3LUnsized _             -> Map.singleton proj (1, anno)
    Term3LDeferRef _            -> mempty
    -- unreachable in a lifted term; 'intrinsic' rejects it
    StuckFW (DeferSF _ _)       -> mempty
    Term3LCheckingWrapper _ _ c -> go proj c
    BasicFW (PairSF a b)        -> merge (go [] a) (go [] b)
    StuckFW (SetEnvSF x)        -> go [] x
    -- gate is a value; branch and scrutinee usage flows through the
    -- SetEnv/Pair nodes of the GateSwitch encoding
    StuckFW GateSF              -> mempty
    BasicFW ZeroSF              -> mempty
    AbortFW _                   -> mempty
    _                           -> mempty

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
  }

-- | Box paths: per-frame (for occurrence depth equations) and global (for
-- computing overall nesting depth). Innermost variable first.
data Paths = Paths
  { pLocal  :: [BVar]
  , pGlobal :: [BVar]
  }

recordLeaf :: Paths -> EALM ()
recordLeaf paths = State.modify $ \st ->
  st { esLeafPaths = pGlobal paths : esLeafPaths st
     , esLeafCount = esLeafCount st + 1 }

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
  -- a reference instantiates its body: a fresh copy of the body's
  -- constraints, whose interface rides with the tag to every apply site
  -- the reference reaches
  Term3LDeferRef h -> do
    recordLeaf paths
    iface <- instantiateBody paths h
    ct <- freshCode (Map.singleton (TCode h) (TagInfo Nothing (Just iface)))
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
          (ApplySite fnT si so (pGlobal paths) anno mempty)
          (esApplies st)
      , esNextApply = esNextApply st + 1 }
    pure so
  StuckFW GateSF -> do
    recordLeaf paths
    ct <- builtinCode TGate
    plainSigma anno "gate is an unboxed value" ct
  StuckFW (LeftSF x) -> projection ctx paths anno x fst
  StuckFW (RightSF x) -> projection ctx paths anno x snd
  AbortFW AbortF -> do
    recordLeaf paths
    ct <- builtinCode TAbort
    plainSigma anno "abort is an unboxed value" ct
  AbortFW (AbortedF _) -> recordLeaf paths >> bottomSigma
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

-- * Body instantiation

-- | Instantiate a lifted body at a DeferRef occurrence: a fresh copy of
-- its constraints, served from the body's template (captured by walking
-- the body on its first occurrence). The result is the instance's
-- interface, which rides with the occurrence's tag.
--
-- Instances are finite by construction: one per occurrence per enclosing
-- instance, and the DeferMap is a DAG, so the walk of a body — which
-- instantiates the bodies it references — bottoms out. No budget is
-- needed, and none exists.
instantiateBody :: Paths -> Digest SHA256 -> EALM Iface
instantiateBody paths h = do
  (fi, body) <- State.gets (Map.lookup h . esBodies) >>= \case
    Just fb -> pure fb
    Nothing -> throwError . EALInternal $
      "referenced code not in the DeferMap " <> show h
  State.gets (Map.lookup h . esTemplates) >>= \case
    Just t  -> instantiateTemplate paths t
    Nothing -> captureTemplate paths h fi body

-- | First occurrence of a body: walk it, and capture the walk's state
-- delta as a 'BodyTemplate' for later occurrences. The capture relies on
-- the walk's writes staying inside the fresh variable block — the body
-- is closed, so unions, class constraints, type bindings and tag classes
-- all live on block variables (nested instances included) — plus the
-- append-only channels (sum equations, leaf paths, apply sites, instance
-- env bangs) whose deltas are taken by count.
captureTemplate :: Paths -> Digest SHA256 -> FunctionIndex -> Term3Lifting
                -> EALM Iface
captureTemplate paths h fi body = do
  st0 <- State.get
  let v0 = esNextVar st0
      a0 = esNextApply st0
      eq0 = esSumEqCount st0
      leaf0 = esLeafCount st0
      defer0 = esDeferCount st0
      occGLen = length (pGlobal paths)
  bEnv <- freshB
  tEnv <- freshTau
  forM_ (contractionSite (envUsageL body)) $ \(path, uloc) ->
    void . constrainB bEnv . ForcedLevel 1 $
      Blame uloc ("env path " <> showSteps path <> " duplicated in "
        <> show fi)
  recordDefer fi bEnv
  sBody <- viewNode (DeferCtx bEnv tEnv) (Paths [] (pGlobal paths)) body
  st1 <- State.get
  let blockOf :: Map Int a -> [(Int, a)]
      blockOf = Map.toAscList . snd . Map.split (v0 - 1)
      stripOcc xs = take (length xs - occGLen) xs
      template = BodyTemplate
        { btIndex = fi
        , btBase = v0
        , btSize = esNextVar st1 - v0
        , btParents = blockOf (esParents st1)
        , btClasses = blockOf (esClasses st1)
        , btTVarBinds = blockOf (esTVarBinds st1)
        , btTagParents = blockOf (esTagParents st1)
        , btTagSets = blockOf (esTagSets st1)
        , btSumEqs = take (esSumEqCount st1 - eq0) (esSumEqs st1)
        , btLeafPrefixes = fmap stripOcc
            (take (esLeafCount st1 - leaf0) (esLeafPaths st1))
        , btApplies =
            [ s { apGlobal = stripOcc (apGlobal s) }
            | s <- Map.elems (snd (Map.split (a0 - 1) (esApplies st1))) ]
        , btDefers = take (esDeferCount st1 - defer0) (esDefers st1)
        , btEnvBang = bEnv
        , btEnvTau = tEnv
        , btResult = sBody
        }
  State.modify $ \st ->
    st { esTemplates = Map.insert h template (esTemplates st) }
  pure $ Iface (Sigma bEnv tEnv) sBody

recordDefer :: FunctionIndex -> BVar -> EALM ()
recordDefer fi b = State.modify $ \st ->
  st { esDefers = (fi, b) : esDefers st
     , esDeferCount = esDeferCount st + 1 }

-- | Serve an occurrence from the body's captured template: allocate a
-- fresh contiguous variable block, offset-copy every constraint of the
-- walk into it, and splice this occurrence's global path where the
-- capturing occurrence's was stripped. Emits exactly the constraints a
-- fresh walk would, at the cost of copying the delta instead of
-- re-running the walk.
instantiateTemplate :: Paths -> BodyTemplate -> EALM Iface
instantiateTemplate paths t = do
  base <- State.gets esNextVar
  let shift = base - btBase t
      sh i = if i >= btBase t then i + shift else i
      shB (BVar i) = BVar (sh i)
      shTau = \case
        VarT i -> VarT (sh i)
        CodeT i -> CodeT (sh i)
        CapT i -> CapT (sh i)
        PairT a b -> PairT (shSig a) (shSig b)
        DataT -> DataT
        AbortedT -> AbortedT
      shSig (Sigma b tau) = Sigma (shB b) (shTau tau)
      shIface (Iface e r) = Iface (shSig e) (shSig r)
      shInfo (TagInfo c i) = TagInfo (fmap shSig c) (fmap shIface i)
      shEq (SumEq lhs rhs blame) = SumEq (fmap shB lhs) (shB rhs) blame
      shKV f (k, v) = (sh k, f v)
      splice p = fmap shB p <> pGlobal paths
      instApply s = s
        { apFn = shTau (apFn s)
        , apEnv = shSig (apEnv s)
        , apRes = shSig (apRes s)
        , apGlobal = splice (apGlobal s)
        , apDispatched = mempty
        }
  State.modify $ \st -> st
    { esNextVar = base + btSize t
    , esParents = Map.union
        (Map.fromAscList (fmap (shKV sh) (btParents t))) (esParents st)
    , esClasses = Map.union
        (Map.fromAscList (fmap (shKV id) (btClasses t))) (esClasses st)
    , esTVarBinds = Map.union
        (Map.fromAscList (fmap (shKV shTau) (btTVarBinds t))) (esTVarBinds st)
    , esTagParents = Map.union
        (Map.fromAscList (fmap (shKV sh) (btTagParents t))) (esTagParents st)
    , esTagSets = Map.union
        (Map.fromAscList (fmap (shKV (fmap shInfo)) (btTagSets t)))
        (esTagSets st)
    , esSumEqs = fmap shEq (btSumEqs t) <> esSumEqs st
    , esSumEqCount = esSumEqCount st + length (btSumEqs t)
    , esLeafPaths = fmap splice (btLeafPrefixes t) <> esLeafPaths st
    , esLeafCount = esLeafCount st + length (btLeafPrefixes t)
    , esApplies = Map.union
        (Map.fromAscList
          (zip [esNextApply st ..] (fmap instApply (btApplies t))))
        (esApplies st)
    , esNextApply = esNextApply st + length (btApplies t)
    , esDefers = fmap (fmap shB) (btDefers t) <> esDefers st
    , esDeferCount = esDeferCount st + length (btDefers t)
    }
  pure $ Iface (Sigma (shB (btEnvBang t)) (shTau (btEnvTau t)))
               (shSig (btResult t))

-- * Application dispatch

-- | Dispatch every tag that has flowed into every apply site's function
-- position, to a fixpoint: dispatching unifies the site with the tag's
-- interface, which can grow other sites' tag sets. Nothing is derived
-- here — the set of sites is fixed once the walk is done and the tags
-- are the finite DeferMap namespace plus the built-ins — so every round
-- that changes anything dispatches at least one new (site, tag) pair and
-- the loop terminates by construction. A function position that never
-- resolves (nothing flows there but the program's unknown input) is
-- tolerated without constraints — input is data by the runtime contract,
-- and applying data sticks only when demanded.
resolveApplies :: EALM ()
resolveApplies = do
  changed <- dispatchRound False
  if changed
    then resolveApplies
    else do
      -- at a fixpoint some abort sites may still be waiting to learn
      -- their message's shape; read those conservatively and go on
      committed <- dispatchRound True
      when committed resolveApplies
  where
  dispatchRound force = do
    keys <- State.gets (Map.keys . esApplies)
    foldM (\acc k -> (acc ||) <$> resolveSite force k) False keys
  resolveSite force k = State.gets (Map.lookup k . esApplies) >>= \case
    Nothing -> pure False
    Just site -> walkTau (apFn site) >>= \case
      VarT _ -> pure False
      CodeT i -> dispatchNew force k site =<< capturesOf i
      -- a capture selection applied directly: any code its package's
      -- captures can hold may run here
      CapT i ->
        dispatchNew force k site =<< codeInfosOfCaptures (apLoc site) i
      -- applying data sticks immediately at runtime, and stuckness is a
      -- value until demanded — bounded work, so nothing for the
      -- certificate to reject. (Shape errors are the language checker's
      -- job.) Note this is more tolerant than a flow analyzer's must-fail
      -- rule: with unification a data binding can shadow code that flow
      -- would have kept as a separate union member, so data-here must not
      -- be read as data-only.
      DataT -> pure False
      -- applying a value that never exists yields a value that never
      -- exists (the runtime propagates the aborted value)
      AbortedT -> do
        bottomSigma >>= unifySigma (apLoc site) (apRes site)
        pure False
      other -> throwError . EALTypeMismatch (apLoc site) $
        "applied value is " <> describeTau other <> ", not code"
  dispatchNew force k site infos = do
    let new = Map.withoutKeys infos (apDispatched site)
    if Map.null new
      then pure False
      else do
        -- mark first: dispatch can grow this very set, and the next
        -- round picks up only what is genuinely new
        adjustDispatched k (Set.union (Map.keysSet new))
        deferred <- fmap concat . forM (Map.toList new) $ \ti@(t, _) -> do
          done <- dispatchTag force site ti
          pure [t | not done]
        unless (null deferred) $
          adjustDispatched k (`Set.difference` Set.fromList deferred)
        pure (length deferred < Map.size new)
  adjustDispatched k f = State.modify $ \st -> st
    { esApplies = Map.adjust
        (\s -> s { apDispatched = f (apDispatched s) }) k (esApplies st) }

-- | The code records a capture position can hold, for a capture applied
-- as a function: the union over the package's captures' own code,
-- chasing nested selections coinductively. Two records of one tag met
-- this way are two instances flowing to one position and are unified.
codeInfosOfCaptures :: LocTag -> Int -> EALM (Map Tag TagInfo)
codeInfosOfCaptures loc = go mempty where
  go vis i = do
    r <- findTag i
    if Set.member r vis
      then pure mempty
      else do
        caps <- capturesOf r
        foldM (\acc c -> infosIn (Set.insert r vis) c >>= merge acc)
          mempty (Map.elems caps)
  infosIn vis' = \case
    TagInfo (Just (Sigma _ t)) _ -> walkTau t >>= \case
      CodeT j -> capturesOf j
      CapT j  -> go vis' j
      _       -> pure mempty
    TagInfo Nothing _ -> pure mempty
  merge acc m = do
    forM_ (Map.toList (Map.intersectionWith (,) acc m)) $ \(_t, (a, b)) ->
      unifyTagInfo loc a b
    pure (Map.unionWith mergeTagInfo acc m)

-- | Emit the constraints of applying one tag at one site. False means
-- the dispatch is deferred: an abort whose message shape is not known
-- yet (unless forced, which reads it as the identity continuation).
dispatchTag :: Bool -> ApplySite -> (Tag, TagInfo) -> EALM Bool
dispatchTag force site (tag, info) = case tag of
  TCode h -> do
    Iface envS resS <- case tiIface info of
      Just i  -> pure i
      Nothing -> throwError . EALInternal $
        "code tag without an interface: " <> show h
    -- the operand meets the instance's env under this tag's mode:
    -- capture selections inside it resolve to THIS tag's capture
    unifySigmaAt mempty (Just tag) (apLoc site) (apEnv site) envS
    unifySigma (apLoc site) (apRes site) resS
    pure True
  TGate -> do
    scrB <- forcedZeroB $ Blame loc "gate scrutinee must be unboxed data"
    unifySigma loc (apEnv site) (Sigma scrB DataT)
    gfn <- plainSigma loc "gate switch function is locally unboxed"
      =<< builtinCode TGateFn
    unifySigma loc (apRes site) gfn
    pure True
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
    pure True
  -- abort messages need no shape or bang constraint: the runtime
  -- truncates non-data message components to Zero. A message that is
  -- statically a pair really aborts, and the result never exists; a Zero
  -- (or unresolved) message yields the identity continuation.
  TAbort -> do
    let Sigma _ msgT = apEnv site
    messageAborts mempty msgT >>= \case
      Just True -> do
        bottomSigma >>= unifySigma loc (apRes site)
        pure True
      Nothing | not force -> pure False
      _zeroOrUnknown -> do
        cont <- plainSigma loc "abort continuation is locally unboxed"
          =<< builtinCode TAbortCont
        unifySigma loc (apRes site) cont
        pure True
  TAbortCont -> do
    unifySigma loc (apEnv site) (apRes site)
    pure True
  where loc = apLoc site

-- | The sigma of a value that never exists; its bang is free, since no
-- box discipline applies to a value nothing ever consumes.
bottomSigma :: EALM Sigma
bottomSigma = flip Sigma AbortedT <$> freshB

-- | Does an abort message of this type really abort? A pair message
-- does (Just True), Zero does not (Just False: the identity
-- continuation), and a message whose shape is still unknown cannot be
-- read yet (Nothing). A capture selection is read through its captures:
-- it aborts if every capture it may stand for does. Non-data components
-- are truncated to Zero by the runtime, so code and captureless tags
-- read as Zero.
messageAborts :: Set Int -> Tau -> EALM (Maybe Bool)
messageAborts vis t = walkTau t >>= \case
  PairT _ _ -> pure (Just True)
  DataT -> pure (Just False)
  CodeT _ -> pure (Just False)
  AbortedT -> pure (Just True)
  VarT _ -> pure Nothing
  CapT i -> do
    r <- findTag i
    if Set.member r vis
      then pure (Just True)
      else do
        caps <- capturesOf r
        verdicts <- forM (Map.elems caps) $ \case
          TagInfo (Just (Sigma _ ct)) _ -> messageAborts (Set.insert r vis) ct
          TagInfo Nothing _ -> pure (Just False)
        pure $ if null verdicts then Just False else foldr1 both verdicts
  where
    both (Just a) (Just b) = Just (a && b)
    both _ _ = Nothing

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
analyzeTop = analyzeTopWith False

-- | 'analyzeTop', optionally also certifying one application of the
-- program's value to its (data) input — the main pass runs with this on.
analyzeTopWith :: Bool -> String -> Term3Lifting
               -> EALM (BVar, Tau, Sigma, Map Int Int)
analyzeTopWith applyToInput what term = do
  bEnv <- freshB
  tEnv <- freshTau
  case contractionSite (envUsageL term) of
    Just (path, uloc) -> void . constrainB bEnv . ForcedLevel 1 $
      Blame uloc (what <> " path " <> showSteps path <> " duplicated")
    Nothing -> pure ()
  sRes <- viewNode (DeferCtx bEnv tEnv) (Paths [] []) term
  resolveApplies
  when applyToInput $ virtualMainApply sRes >> resolveApplies
  propagate
  vals <- assignValues
  pure (bEnv, tEnv, sRes, vals)

-- | The runtime applies the whole program to its input every iteration,
-- so the certificate must cover main's body running against data — a
-- divergence sitting under main's outermost lambda is invisible in the
-- program-as-value alone (its body is derived nowhere, and the
-- standalone body pass cannot see the captures that feed it). This is
-- the moral successor of the old checker's main-against-@Zero -> Zero@
-- comparison. One application level matches the run loop's contract
-- exactly: an iteration's result must be a data pair, never a closure
-- that gets applied further.
--
-- Registered against the RESOLVED shape of the program's value, after
-- the first dispatch fixpoint: a closure package applies its code to
-- @(input, captures)@ (the compiled convention: a body's argument is
-- @Left Env@, its captures @Right Env@), bare code applies to the input
-- alone, and anything else — data, or a shape nothing constrains — has
-- no derivable body to cover (applying data sticks, boundedly).
virtualMainApply :: Sigma -> EALM ()
virtualMainApply (Sigma _ tRes) = walkTau tRes >>= \case
  PairT (Sigma _ tCode) sCap -> walkTau tCode >>= \case
    tc | appliable tc -> do
      inputS <- inputSigma
      envB <- freshB
      register tc (Sigma envB (PairT inputS sCap))
    _notCode -> pure ()
  tc | appliable tc -> register tc =<< inputSigma
  _notAppliable -> pure ()
  where
    vAnno = GeneratedLoc "virtual application of main to input" Nothing
    appliable = \case
      CodeT _ -> True
      CapT _  -> True
      _other  -> False
    inputSigma = flip Sigma DataT <$> freshB
    register fnT env = do
      so <- freshSigma
      State.modify $ \st -> st
        { esApplies = Map.insert (esNextApply st)
            (ApplySite fnT env so [] vAnno mempty)
            (esApplies st)
        , esNextApply = esNextApply st + 1 }

leafDepths :: Map Int Int -> EALM [Int]
leafDepths vals = State.gets esLeafPaths >>= mapM depth where
  value r = fromMaybe 0 $ Map.lookup r vals
  depth vs = sum . fmap value <$> mapM findB vs

-- * Lifted inference

-- | Direct DeferRef dependencies of a lifted term.
refsOf :: Term3Lifting -> Set (Digest SHA256)
refsOf (_ :< t) = case t of
  Term3LDeferRef h -> Set.singleton h
  x                -> foldMap refsOf x

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
        (TCode h, TagInfo (Just sig) _) -> do
          s <- shapeOfSigma sig
          pure [(h, s)]
        _bare -> pure []

-- | The resolved shape of a value, as 'CapShape' grades it: data, bare
-- code, known pair structure, or unknown.
shapeOfSigma :: Sigma -> EALM CapShape
shapeOfSigma (Sigma _ t) = walkTau t >>= \case
  DataT     -> pure CapData
  PairT a b -> CapPair <$> shapeOfSigma a <*> shapeOfSigma b
  CodeT _   -> pure CapCode
  _other    -> pure CapOther

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
      (bMain, _, sRes, vals) <- analyzeTopWith True "program input" mainTerm
      let value r = fromMaybe 0 $ Map.lookup r vals
      topBang <- value <$> findB bMain
      defers <- State.gets esDefers >>= fmap (Map.fromListWith max) .
        traverse (\(fi, b) -> (,) fi . value <$> findB b)
      depths <- leafDepths vals
      shapes <- groundCaptureShapes
      mainShape <- shapeOfSigma sRes
      pure ( EALResult
               { ealTopLevelBang = topBang
               , ealDeferBangs = defers
               , ealMaxLevel = maximum (0 : depths)
               , ealMainShape = mainShape
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

-- | The compile gate: certify a whole program, additionally requiring
-- that main is an appliable function. Certification itself tolerates a
-- hereditarily-data program (applying data sticks at runtime, which is
-- bounded work), but a main that can never consume input is a mistake
-- worth naming at compile time, as the type checker used to.
certifyMain :: Term3 -> Either EALError EALResult
certifyMain t = do
  r <- ealLiftedMain (inferEALWithLifting t)
  if allDataShape (ealMainShape r)
    then Left $ EALTypeMismatch
           (GeneratedLoc "EAL certification" Nothing)
           "main is data through and through; a program must be a function of its input"
    else pure r

-- | One-line human rendering of a whole-program verdict, for the REPL
-- and diagnostics.
renderEALVerdict :: EALLiftedResult -> String
renderEALVerdict lr = case ealLiftedMain lr of
  Left e -> "does not certify: " <> renderEALError e
  Right r ->
    "certifies: max box level " <> show (ealMaxLevel r)
      <> ", input bang " <> show (ealTopLevelBang r)
