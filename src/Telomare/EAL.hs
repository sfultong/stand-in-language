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
import Data.Bifunctor (first)
import Control.Monad (filterM, foldM, forM, forM_, unless, void, when,
                      zipWithM_)
import Control.Monad.Except
import Control.Monad.State.Strict (State)
import qualified Control.Monad.State.Strict as State
import Crypto.Hash (Digest, SHA256)
import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Graph as Graph
import qualified Data.Tree as Tree
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (isPrefixOf, minimumBy, partition, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Ratio (denominator, numerator)
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
  { ifEnv   :: Sigma
  , ifRes   :: Sigma
  , ifDoors :: [BVar] -- ^ one per capture path the body duplicates: the
                      --   bang consumed by contracting that capture
                      --   outside the closure's box (see 'envOccurrence')
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
  , esLeafPaths  :: [(Maybe FunctionIndex, [BVar])]
                                      -- ^ leaf depths as [base, depth],
                                      -- tagged with the body they sit in
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
  , btLeafPrefixes :: [(Maybe FunctionIndex, [BVar])] -- ^ block-local leaf depths; the
                                      -- instance base is prepended at
                                      -- instantiation
  , btApplies      :: [ApplySite]       -- ^ nested sites
  , btDefers       :: [(FunctionIndex, BVar)] -- ^ env bangs of the instances
                                              -- inside the block
  , btEnvBang      :: BVar              -- ^ interface: frame env domain bang
  , btEnvTau       :: Tau               -- ^ interface: frame env type
  , btResult       :: Sigma             -- ^ interface: body result
  , btDoors        :: [BVar]            -- ^ interface: the body's doors
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

-- | Per-hash guidance about one lifted Defer body: what a consumer — the
-- IC runtime foremost — can use about this code, keyed by the same
-- content hash that keys the DeferMap, so analysis and runtime share one
-- namespace. Under a certified main every body's guidance is certified
-- (main instantiated every body, and a body's own constraints are a
-- subset of its instance's); under a failed main the guidance that
-- survives is the standalone verdicts that localize the failure, not a
-- certificate, and no consumer reads it as one. Presence is itself a
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
                                --   (the max over its instances in the
                                --   global pass)
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
constrainB b nc = do
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
    (Just (Iface ea ra da), Just (Iface eb rb db)) -> do
      unifySigma loc ea eb
      unifySigma loc ra rb
      zipWithM_ unionB da db
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
        \(t, Iface e res _) -> do
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
  -- data is level-free: a component of a data tree is data, and its bang
  -- stays free (copying data is bounded work, so a box on it is never
  -- needed and never forbidden)
  let collapse (Sigma _ t) = unifyTauAt vis mode loc t DataT
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
contractionSites :: Map [Step] (Int, LocTag) -> [([Step], LocTag)]
contractionSites m =
  let ks = Map.keys m
      subPathUsed p = any (\q -> p /= q && p `isPrefixOf` q) ks
      bad (p, (c, _)) = c >= 2 || (c >= 1 && subPathUsed p)
  in [ (p, l) | (p, (_, l)) <- Map.toList m, bad (p, (fst (m Map.! p), l)) ]

-- | The projection path of an env occurrence:  (Right Env)@ is
-- @[SR, SL]@, innermost projection first (the order they apply to the
-- env value, matching 'envUsageL'). Nothing for any other term.
envPath :: Term3Lifting -> Maybe [Step]
envPath (_ :< t) = case t of
  StuckFW EnvSF               -> Just []
  Term3LUnsized _             -> Just []
  StuckFW (LeftSF x)          -> (<> [SL]) <$> envPath x
  StuckFW (RightSF x)         -> (<> [SR]) <$> envPath x
  Term3LCheckingWrapper _ _ c -> envPath c
  _notAnOccurrence            -> Nothing

-- * Constraint generation

data DeferCtx = DeferCtx
  { dcBang  :: BVar -- ^ bang count on this frame's env domain
  , dcTau   :: Tau  -- ^ this frame's env type
  , dcUnit  :: BVar -- ^ the analysis-wide unit (a bang of exactly one, up
                    --   to the homogeneous scaling of the whole system)
  , dcDoorList :: [BVar] -- ^ the door variables themselves
  , dcIndex :: Maybe FunctionIndex -- ^ the body this frame instantiates
                                   --   (Nothing for the program itself)
  , dcDoors :: Map [Step] BVar
    -- ^ per capture path this body duplicates: the part of the
    -- component's bang the body still has to open (the rest, one unit,
    -- is consumed by the contraction outside the closure's box)
  }

-- | Set up a frame: charge every duplicated env path to its component's
-- bang, and for a duplicated CAPTURE path split that bang into the one
-- door consumed outside the closure's box and the part the body opens
-- (see 'envOccurrence').
frameContext :: BVar -> Maybe FunctionIndex -> String -> BVar -> Tau
             -> Term3Lifting -> EALM DeferCtx
frameContext unit idx what bEnv tEnv body = do
  let ctx0 = DeferCtx bEnv tEnv unit [] idx mempty
  doors <- forM (contractionSites (envUsageL body)) $ \(path, uloc) -> do
    (_, Sigma bq _) <- envComponent uloc ctx0 path
    void . constrainB bq . ForcedLevel 1 $
      Blame uloc (what <> " path " <> showSteps path <> " duplicated")
    case path of
      (SR : _) -> do
        door <- freshB
        inner <- freshB
        rest <- freshB
        addSumEq (Blame uloc "a duplicated capture's bang = door + what the body opens")
          [door, inner] bq
        addSumEq (Blame uloc "at most one door per duplicated capture")
          [door, rest] unit
        pure [(path, door, inner)]
      _argumentOrWhole -> pure []
  pure ctx0 { dcDoorList = [ d | (_, d, _) <- concat doors ]
            , dcDoors = Map.fromList [ (p, i) | (p, _, i) <- concat doors ] }

-- | Box paths: per-frame (for occurrence depth equations) and global (for
-- computing overall nesting depth). Innermost variable first.
-- | Where a node sits. Depths are cumulative: one variable per node holds
-- the boxes on the edges from the frame root down to it, defined by the
-- three-term equation  = parent's depth + this edge@, so every
-- occurrence equation mentions one depth variable instead of the whole
-- path. The base is the global depth of the occurrence that instantiated
-- the frame; a leaf's global depth is base + its own depth.
data Paths = Paths
  { pParent :: Maybe BVar -- ^ the parent's cumulative depth (Nothing at
                          --   the frame root); inside 'intrinsic' this is
                          --   the node's own depth
  , pBase   :: BVar       -- ^ the frame's global depth
  }

-- | The depth of the node being analyzed ('intrinsic' always runs under
-- 'viewNode', which sets it).
nodeDepth :: Paths -> EALM BVar
nodeDepth paths = case pParent paths of
  Just d  -> pure d
  Nothing -> throwError (EALInternal "a node outside viewNode")

recordLeaf :: DeferCtx -> Paths -> EALM ()
recordLeaf ctx paths = do
  d <- nodeDepth paths
  State.modify $ \st ->
    st { esLeafPaths = (dcIndex ctx, [pBase paths, d]) : esLeafPaths st
       , esLeafCount = esLeafCount st + 1 }

-- | Allocate this node's edge box variable, define its cumulative depth,
-- and wrap its intrinsic type into the type seen by the parent (view
-- bang = edge boxes + intrinsic bang).
viewNode :: DeferCtx -> Paths -> Term3Lifting -> EALM Sigma
viewNode ctx paths term@(anno :< _) = do
  w <- freshB
  d <- case pParent paths of
    Nothing -> pure w
    Just p -> do
      d <- freshB
      addSumEq (Blame anno "box depth = the parent's depth + this edge's boxes")
        [p, w] d
      pure d
  Sigma bi ti <- intrinsic ctx paths { pParent = Just d } term
  v <- freshB
  addSumEq (Blame anno "view bangs = edge boxes + intrinsic bangs") [w, bi] v
  pure $ Sigma v ti

intrinsic :: DeferCtx -> Paths -> Term3Lifting -> EALM Sigma
intrinsic ctx paths (anno :< t) = case t of
  BasicFW ZeroSF -> do
    recordLeaf ctx paths
    plainSigma anno "Zero is an unboxed value" DataT
  BasicFW (PairSF a b) -> do
    -- a closed data tree under a pair is not walked node by node: its
    -- internal edges would carry no constraint, and its type would carry
    -- a view bang per component that every instance copies. It becomes
    -- one leaf: data with a free bang (data is level-free), keeping one
    -- level of pair structure so that an abort message @(0, token)@ still
    -- reads as a pair and a capture layout still says pair-of-data
    let dataLeaf = (`Sigma` DataT) <$> freshB
        childView c
          | dataLiteral c = do
              recordLeaf ctx paths
              case c of
                _ :< BasicFW (PairSF _ _) -> do
                  l <- dataLeaf
                  r <- dataLeaf
                  (`Sigma` PairT l r) <$> freshB
                _zero -> dataLeaf
          | otherwise = viewNode ctx paths c
    sa@(Sigma _ ta) <- childView a
    sb@(Sigma bCap _) <- childView b
    walkTau ta >>= \case
      -- a code-headed pair is a closure package: whatever rides in its
      -- Right belongs to its Left's tags, so record the capture per tag
      -- and expose the position symbolically — joins of different
      -- packages then union instead of unifying captures structurally
      CodeT i -> do
        p <- packageClass i sb
        -- a closure whose body contracts a capture outside its own box
        -- (a door) is born inside that box: the package's own bang
        -- bounds every door of its code
        infos <- capturesOf i
        bpkg <- freshB
        forM_ [ d | TagInfo _ (Just (Iface _ _ ds)) <- Map.elems infos, d <- ds ] $
          \d -> do
            slack <- freshB
            addSumEq (Blame anno "a door needs the closure's own box") [d, slack] bpkg
        pure . Sigma bpkg $ PairT sa (Sigma bCap (CapT p))
      _notCode -> plainSigma anno "pair constructor is locally unboxed" $
        PairT sa sb
  StuckFW EnvSF -> envOccurrence ctx paths anno []
  Term3LUnsized _ -> envOccurrence ctx paths anno []
  StuckFW (DeferSF _ _) -> throwError $
    EALInternal "raw DeferSF in a lifted term"
  -- a reference instantiates its body: a fresh copy of the body's
  -- constraints, whose interface rides with the tag to every apply site
  -- the reference reaches
  Term3LDeferRef h -> do
    recordLeaf ctx paths
    iface <- instantiateBody (dcUnit ctx) paths h
    ct <- freshCode (Map.singleton (TCode h) (TagInfo Nothing (Just iface)))
    plainSigma anno "code constant is an unboxed value" ct
  StuckFW (SetEnvSF x) -> do
    sx <- viewNode ctx paths x
    si@(Sigma siB siT) <- freshSigma
    fnT <- freshTau
    -- boxes pass through an application, they never vanish: a function
    -- carrying k boxes (on the pair and on the function itself) is
    -- applied INSIDE those k boxes, the implicit  !g = f in !^k(g a)@
    -- the compiler never writes. So the operand must carry at least k
    -- (it enters the box too; the callee sees the rest), and the result
    -- comes out with k more.
    fnB <- freshB
    pairB <- freshB
    k <- freshB
    addSumEq (Blame anno "boxes entered = boxes on the applied pair + on the function")
      [pairB, fnB] k
    unifySigma anno sx . Sigma pairB $ PairT (Sigma fnB fnT) si
    -- the operand is a component of the applied pair, so it sits under
    -- the pair's boxes as well as its own
    operandB <- freshB
    addSumEq (Blame anno "operand boxes = applied pair boxes + its own")
      [pairB, siB] operandB
    calleeEnvB <- freshB
    addSumEq (Blame anno "operand boxes = boxes entered + boxes the callee sees")
      [k, calleeEnvB] operandB
    so@(Sigma soB _) <- freshSigma
    outB <- freshB
    addSumEq (Blame anno "result boxes = boxes entered + the callee's result boxes")
      [k, soB] outB
    State.modify $ \st -> st
      { esApplies = Map.insert (esNextApply st)
          (ApplySite fnT (Sigma calleeEnvB siT) so anno mempty)
          (esApplies st)
      , esNextApply = esNextApply st + 1 }
    pure (Sigma outB (let Sigma _ t = so in t))
  StuckFW GateSF -> do
    recordLeaf ctx paths
    ct <- builtinCode TGate
    plainSigma anno "gate is an unboxed value" ct
  -- projections of the env are one occurrence at a path (no box can sit
  -- between them); projections of anything else open an unboxed pair
  StuckFW (LeftSF x) -> case envPath x of
    Just steps -> envOccurrence ctx paths anno (steps <> [SL])
    Nothing    -> projection ctx paths anno x fst
  StuckFW (RightSF x) -> case envPath x of
    Just steps -> envOccurrence ctx paths anno (steps <> [SR])
    Nothing    -> projection ctx paths anno x snd
  AbortFW AbortF -> do
    recordLeaf ctx paths
    ct <- builtinCode TAbort
    plainSigma anno "abort is an unboxed value" ct
  AbortFW (AbortedF _) -> recordLeaf ctx paths >> bottomSigma
  Term3LCheckingWrapper _ _ c -> intrinsic ctx paths c

-- | An occurrence of the env at a projection path. In EAL a variable is
-- used exactly as many box doors deep as its type has bangs, so the
-- occurrence's depth (the boxes on the path from the frame root down
-- to it) equals the bangs this body opens on the way to the component,
-- and the value it yields is that component fully opened. No slack: an
-- unopened box above a variable is not weakening, it is a use at the
-- wrong level.
--
-- Which bangs the body opens depends on the half of the env (the
-- compiled convention: argument on the Left, captures on the Right).
-- The env's top bang and the bangs along an ARGUMENT path are opened
-- here: a duplicated argument is used inside a box of this body. The
-- bangs along a CAPTURE path were opened by the closure's own box: in
-- EAL a closure duplicating a captured variable is
-- @\\g. !(\\x. g (g x))@ — the contraction happens outside the box, at the
-- construction site, and each copy enters through its own door to be
-- used once at depth zero inside. So a duplicated capture is charged to
-- the component's bang at construction (its occurrence there sits one
-- level down) and costs nothing in the body. This is what types Church
-- numerals as @!(A -o A) -o !(A -o A)@ instead of demanding a box
-- around every application.
envOccurrence :: DeferCtx -> Paths -> LocTag -> [Step] -> EALM Sigma
envOccurrence ctx paths anno steps = do
  recordLeaf ctx paths
  (bangs, Sigma _ t) <- envComponent anno ctx steps
  d <- nodeDepth paths
  let opened = case steps of
        -- argument side: every bang is opened here
        (SL : _) -> dcBang ctx : bangs
        -- capture side: every bang too, except that a duplicated
        -- capture's own bang had one door consumed outside the box
        (SR : _) | Just inner <- Map.lookup steps (dcDoors ctx) ->
          dcBang ctx : init bangs <> [inner]
        _captureOrWhole -> dcBang ctx : bangs
  addSumEq (Blame anno "env occurrence depth = the bangs this body opens")
    opened d
  b <- forcedZeroB $ Blame anno "variable occurrence is locally unboxed"
  pure (Sigma b t)

-- | The env component at a projection path, refining the env type into
-- pair structure as needed: the bangs of the components stepped
-- through (outermost first) and the component's sigma.
envComponent :: LocTag -> DeferCtx -> [Step] -> EALM ([BVar], Sigma)
envComponent loc ctx = go (Sigma (dcBang ctx) (dcTau ctx)) [] where
  go sig acc [] = pure (reverse acc, sig)
  go (Sigma _ t) acc (s : rest) = do
    sl <- freshSigma
    sr <- freshSigma
    unifyTau loc t (PairT sl sr)
    let next@(Sigma b _) = case s of
          SL -> sl
          SR -> sr
    go next (b : acc) rest

projection :: DeferCtx -> Paths -> LocTag -> Term3Lifting
  -> ((Sigma, Sigma) -> Sigma) -> EALM Sigma
projection ctx paths anno x pick = do
  sx <- viewNode ctx paths x
  sl <- freshSigma
  sr <- freshSigma
  -- boxes pass through a projection: the component of a pair under k
  -- boxes comes out under k boxes plus its own (@!(A x B) |- !A@)
  pB <- freshB
  unifySigma anno sx . Sigma pB $ PairT sl sr
  let Sigma bc tc = pick (sl, sr)
  out <- freshB
  addSumEq (Blame anno "projected component boxes = pair boxes + its own")
    [pB, bc] out
  pure (Sigma out tc)

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
instantiateBody :: BVar -> Paths -> Digest SHA256 -> EALM Iface
instantiateBody unit paths h = do
  (fi, body) <- State.gets (Map.lookup h . esBodies) >>= \case
    Just fb -> pure fb
    Nothing -> throwError . EALInternal $
      "referenced code not in the DeferMap " <> show h
  -- the instance's base: this occurrence's global depth. Minted outside
  -- the template block, so copies of the block refer to their own base
  d <- nodeDepth paths
  base <- freshB
  addSumEq (Blame (GeneratedLoc "instance base" Nothing)
              "an occurrence's global depth = its frame's base + its depth")
    [pBase paths, d] base
  State.gets (Map.lookup h . esTemplates) >>= \case
    Just t  -> instantiateTemplate base t
    Nothing -> captureTemplate unit base h fi body

-- | First occurrence of a body: walk it, and capture the walk's state
-- delta as a 'BodyTemplate' for later occurrences. The capture relies on
-- the walk's writes staying inside the fresh variable block — the body
-- is closed, so unions, class constraints, type bindings and tag classes
-- all live on block variables (nested instances included) — plus the
-- append-only channels (sum equations, leaf paths, apply sites, instance
-- env bangs) whose deltas are taken by count.
captureTemplate :: BVar -> BVar -> Digest SHA256 -> FunctionIndex
                -> Term3Lifting -> EALM Iface
captureTemplate unit base h fi body = do
  st0 <- State.get
  let v0 = esNextVar st0
      a0 = esNextApply st0
      eq0 = esSumEqCount st0
      leaf0 = esLeafCount st0
      defer0 = esDeferCount st0
  bEnv <- freshB
  tEnv <- freshTau
  ctx <- frameContext unit (Just fi) ("env of " <> show fi) bEnv tEnv body
  recordDefer fi bEnv
  sBody <- viewNode ctx (Paths Nothing base) body
  st1 <- State.get
  let blockOf :: Map Int a -> [(Int, a)]
      blockOf = Map.toAscList . snd . Map.split (v0 - 1)
      -- leaves are [base, depth]; the base is the occurrence's and is
      -- replaced at instantiation
      stripBase = fmap (drop 1)
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
        , btLeafPrefixes = fmap stripBase
            (take (esLeafCount st1 - leaf0) (esLeafPaths st1))
        , btApplies = Map.elems (snd (Map.split (a0 - 1) (esApplies st1)))
        , btDefers = take (esDeferCount st1 - defer0) (esDefers st1)
        , btEnvBang = bEnv
        , btEnvTau = tEnv
        , btResult = sBody
        , btDoors = dcDoorList ctx
        }
  State.modify $ \st ->
    st { esTemplates = Map.insert h template (esTemplates st) }
  pure $ Iface (Sigma bEnv tEnv) sBody (dcDoorList ctx)

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
instantiateTemplate :: BVar -> BodyTemplate -> EALM Iface
instantiateTemplate newBase t = do
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
      shIface (Iface e r ds) = Iface (shSig e) (shSig r) (fmap shB ds)
      shInfo (TagInfo c i) = TagInfo (fmap shSig c) (fmap shIface i)
      shEq (SumEq lhs rhs blame) = SumEq (fmap shB lhs) (shB rhs) blame
      shKV f (k, v) = (sh k, f v)
      splice (fi, p) = (fi, newBase : fmap shB p)
      instApply s = s
        { apFn = shTau (apFn s)
        , apEnv = shSig (apEnv s)
        , apRes = shSig (apRes s)
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
               (shSig (btResult t)) (fmap shB (btDoors t))

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
    Iface envS resS _ <- case tiIface info of
      Just i  -> pure i
      Nothing -> throwError . EALInternal $
        "code tag without an interface: " <> show h
    -- the operand meets the instance's env under this tag's mode:
    -- capture selections inside it resolve to THIS tag's capture
    unifySigmaAt mempty (Just tag) (apLoc site) (apEnv site) envS
    unifySigma (apLoc site) (apRes site) resS
    pure True
  TGate -> do
    -- data is level-free, so the scrutinee may sit under any boxes
    scrB <- freshB
    unifySigma loc (apEnv site) (Sigma scrB DataT)
    gfn <- plainSigma loc "gate switch function is locally unboxed"
      =<< builtinCode TGateFn
    unifySigma loc (apRes site) gfn
    pure True
  TGateFn -> do
    sbE@(Sigma bE tE) <- freshSigma
    sbT@(Sigma bT tT) <- freshSigma
    -- boxes on the branch pair pass through to whichever branch is taken
    branchesB <- freshB
    unifySigma loc (apEnv site) (Sigma branchesB (PairT sbE sbT))
    -- the switch can yield either branch: both JOIN into the result (code
    -- positions union, data collapses) instead of the branches unifying
    -- with each other structurally
    rE <- freshB
    addSumEq (Blame loc "taken branch boxes = branch pair boxes + its own") [branchesB, bE] rE
    unifySigma loc (apRes site) (Sigma rE tE)
    rT <- freshB
    addSumEq (Blame loc "taken branch boxes = branch pair boxes + its own") [branchesB, bT] rT
    unifySigma loc (apRes site) (Sigma rT tT)
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

-- | A sum equation over class roots.
data EqR = EqR
  { eqLhs   :: [Int]
  , eqRhs   :: Int
  , eqBlame :: Blame
  }

resolveEqs :: EALM [EqR]
resolveEqs = do
  parents <- State.gets esParents
  -- a read-only resolution: no path compression, so a pass over every
  -- equation writes nothing
  let root i = maybe i root (Map.lookup i parents)
      res (SumEq lhs rhs blame) =
        EqR (fmap (root . unBVar) lhs) (root (unBVar rhs)) blame
  State.gets (fmap res . esSumEqs)

-- | Solve the box constraints exactly: every sum equation holds, every
-- unboxed class is zero, every boxed class meets its lower bound, and all
-- values are naturals. The system is homogeneous (sums of variables equal
-- a variable, no constants), so a rational solution scales to a natural
-- one, and feasibility over the rationals decides feasibility over the
-- naturals. Three stages, each terminating by construction:
--
--   1. 'presolve' draws every consequence that needs no arithmetic —
--      zeros propagate down and up, a total equal to a single summand
--      merges the two classes, a cycle of @summand <= total@ edges makes
--      its members equal and its other summands zero, lower bounds add up
--      the chain — and reports a boxed/unboxed clash as 'EALBoxConflict'
--      with both blames.
--   2. 'solveLinear' eliminates every variable that occurs once (a fresh
--      view or a slack), then runs an exact simplex over the residual.
--      Infeasibility names the rows the simplex could not satisfy
--      together ('EALUnsatisfiable').
--   3. The assignment is verified against every equation exactly.
--
-- The solution is a vertex minimizing the sum of the box variables over
-- the rationals, scaled to naturals; it is a small decoration, not a
-- canonical least one.
solveConstraints :: EALM (Map Int Int)
solveConstraints = do
  presolve
  eqs <- resolveEqs
  classes <- State.gets esClasses
  let info r = fromMaybe Unrestricted (Map.lookup r classes)
      lb = getLowerBound . info
      zero = isForcedZero . info
      live = [ EqR (filter (not . zero) lhs) rhs b
             | EqR lhs rhs b <- eqs, not (zero rhs) ]
  -- phase two of the solve minimizes total leaf depth: an edge weighs
  -- as many leaf paths as run through it, plus one so nothing is free
  leafRoots <- State.gets esLeafPaths >>= mapM (mapM findB . snd)
  let multiplicity = Map.fromListWith (+) [ (r, 1 :: Integer) | p <- leafRoots, r <- p ]
      weight r = 1 + Map.findWithDefault 0 r multiplicity
  sol <- case solveLinear lb weight live of
    Left bad -> throwError . EALUnsatisfiable $ fmap
      (\e -> derivedBlame ("[eq " <> show (eqLhs e) <> " = " <> show (eqRhs e) <> "]")
               (eqBlame e))
      bad
    Right s  -> pure s
  let roots = Set.fromList $
        Map.keys classes <> concatMap (\e -> eqRhs e : eqLhs e) eqs
      value r
        | zero r = 0
        | otherwise = fromMaybe (lb r) (Map.lookup r sol)
      vals = Map.fromSet value roots
  forM_ eqs $ \(EqR lhs rhs blame) ->
    when (sum (fmap value lhs) /= value rhs) . throwError . EALInternal $
      "solver assignment violates an equation: " <> show blame
  pure vals

-- | Draw the arithmetic-free consequences of the constraints to a
-- fixpoint. Merges and zero-forcings are finitely many; lower bounds
-- only rise once the graph is acyclic (the cycle step runs first in
-- every round), and then only along a DAG, so the loop terminates.
presolve :: EALM ()
presolve = do
  -- one resolution per round: a step that merges classes may leave a
  -- later step in the same round looking at a stale root, which only
  -- delays that consequence to the next round (the merge itself counts
  -- as a change). A round without change saw no merge, so it saw every
  -- root fresh and the fixpoint is genuine.
  eqs <- resolveEqs
  changed <- or <$> sequence
    [zeroStep eqs, equalityStep eqs, cycleStep eqs, boundStep eqs]
  when changed presolve

derivedBlame :: String -> Blame -> Blame
derivedBlame what (Blame l s) = Blame l (what <> ": " <> s)

-- | Zeros propagate: an unboxed total has unboxed summands; a total whose
-- summands are all unboxed (none, in particular) is unboxed.
zeroStep :: [EqR] -> EALM Bool
zeroStep eqs = foldM step False eqs where
  step acc (EqR lhs rhs blame) = do
    rhsZero <- isForcedZero <$> classInfo rhs
    lhsZero <- mapM (fmap isForcedZero . classInfo) lhs
    let eqNote = " [eq " <> show lhs <> " = " <> show rhs <> "]"
    c1 <- if rhsZero
      then foldM (\a l -> (a ||) <$> constrainB (BVar l)
                   (ForcedZero (derivedBlame ("summand of an unboxed total" <> eqNote) blame)))
             False lhs
      else pure False
    c2 <- if and lhsZero
      then constrainB (BVar rhs)
             (ForcedZero (derivedBlame ("all summands unboxed" <> eqNote) blame))
      else pure False
    pure (acc || c1 || c2)

-- | A total with exactly one boxable summand equals it: merge the classes.
equalityStep :: [EqR] -> EALM Bool
equalityStep eqs = foldM step False eqs where
  step acc (EqR lhs rhs _) = do
    rhs' <- findB (BVar rhs)
    lhs' <- mapM (findB . BVar) lhs
    boxable <- filterM (fmap (not . isForcedZero) . classInfo) lhs'
    case boxable of
      [l] | l /= rhs' -> unionB (BVar l) (BVar rhs') >> pure True
      _notLone -> pure acc

-- | On the graph with an edge from every summand to its total (summand
-- <= total), the members of a cycle are all equal. Merge them, and in
-- every equation whose total is on a cycle: with one summand on the same
-- cycle the other summands are zero; with two or more the total itself
-- is zero.
cycleStep :: [EqR] -> EALM Bool
cycleStep eqs = do
  classes <- State.gets esClasses
  let zero r = maybe False isForcedZero (Map.lookup r classes)
      live = [ EqR (filter (not . zero) lhs) rhs b
             | EqR lhs rhs b <- eqs, not (zero rhs) ]
      edges = Map.fromListWith (<>) [ (l, [eqRhs e]) | e <- live, l <- eqLhs e ]
      nodes = Set.toList . Set.fromList $ concatMap (\e -> eqRhs e : eqLhs e) live
      cyclic = [ ms | CyclicSCC ms <-
                   stronglyConnComp [ (n, n, Map.findWithDefault [] n edges)
                                    | n <- nodes ] ]
      sccOf = Map.fromList [ (m, i) | (i, ms) <- zip [0 :: Int ..] cyclic, m <- ms ]
  c1 <- foldM (\acc ms -> case ms of
                  (m : rest) -> foldM (\a m' -> (a ||) <$> unionBChanged m m') acc rest
                  [] -> pure acc)
          False cyclic
  c2 <- foldM (\acc (EqR lhs rhs blame) -> case Map.lookup rhs sccOf of
          Nothing -> pure acc
          Just i ->
            let (members, others) = partition (\l -> Map.lookup l sccOf == Just i) lhs
                ms = cyclic !! i
                touching = [ (eqLhs e, eqRhs e, take 24 (let Blame _ s = eqBlame e in s))
                           | e <- live, any (`elem` ms) (eqRhs e : eqLhs e) ]
                cycleNote = " [cycle " <> show ms <> " through " <> show touching <> "]"
            in case members of
              [] -> pure acc
              [_] -> foldM (\a l -> (a ||) <$> constrainB (BVar l)
                             (ForcedZero (derivedBlame
                               ("summand beside one equal to the total" <> cycleNote) blame)))
                       acc others
              _twoOrMore -> (acc ||) <$> constrainB (BVar rhs)
                (ForcedZero (derivedBlame
                  ("total equal to two of its own summands" <> cycleNote) blame)))
          False live
  pure (c1 || c2)
  where
    unionBChanged a b = do
      ra <- findB (BVar a)
      rb <- findB (BVar b)
      if ra == rb then pure False else unionB (BVar a) (BVar b) >> pure True

-- | Lower bounds add up: a total is at least the sum of its summands'
-- lower bounds.
boundStep :: [EqR] -> EALM Bool
boundStep eqs = foldM step False eqs where
  step acc (EqR lhs rhs blame) = do
    s <- sum <$> mapM (fmap getLowerBound . classInfo) lhs
    if s > 0
      then (acc ||) <$> constrainB (BVar rhs)
             (ForcedLevel s (derivedBlame ("sum of summand lower bounds [eq " <> show lhs <> " = " <> show rhs <> "]") blame))
      else pure acc

-- ** Exact linear solving

-- | A linear row over the substituted variables @y_r = x_r - lb r@:
-- @sum coef*y (= | <=) const@, with the equations it was derived from.
data Row = Row
  { rowCoefs :: IntMap Rational
  , rowConst :: Rational
  , rowIsEq  :: Bool
  , rowFrom  :: [EqR]
  }

-- | A variable eliminated from the system: @y_v = max 0 ((const - sum
-- coefs*y) / k)@, where the max only matters for a variable whose row
-- was already an inequality.
data Elim = Elim
  { elVar   :: Int
  , elCoefs :: IntMap Rational
  , elConst :: Rational
  , elK     :: Rational
  }

-- | Solve the live equations over naturals with the given lower bounds.
-- Returns the value of every variable mentioned, or the equations of an
-- inconsistent subsystem.
solveLinear :: (Int -> Int) -> (Int -> Integer) -> [EqR] -> Either [EqR] (Map Int Int)
solveLinear lb weight eqs = do
  let rows0 = IntMap.fromList (zip [0 ..] (fmap toRow eqs))
      (rows1, elims) = eliminate (const True) rows0
      (trivial, residual0) = IntMap.partition (IntMap.null . rowCoefs) rows1
      -- an inequality every nonnegative assignment satisfies (nonpositive
      -- coefficients, nonnegative constant) says nothing
      residual = IntMap.filter (not . vacuous) residual0
      violated = concat [ rowFrom r | r <- IntMap.elems trivial, not (trivialOk r) ]
  unless (null violated) $ Left violated
  -- the residual splits into connected components; one that the all-zero
  -- assignment satisfies needs no simplex (zero is also optimal, every
  -- weight being positive), and the rest are solved separately
  ys <- IntMap.unions <$> mapM (simplexSolve weight)
    [ comp | comp <- components residual, not (all zeroSatisfies (IntMap.elems comp)) ]
  -- elims holds the last elimination first; it depends only on
  -- variables still in the residual, so substitute in that order
  let ysAll = foldl (flip backSubstitute) ys elims
      vars = Set.toList . Set.fromList $ concatMap (\e -> eqRhs e : eqLhs e) eqs
      xs = [ (v, fromIntegral (lb v) + IntMap.findWithDefault 0 v ysAll) | v <- vars ]
      scale = foldr (lcm . denominator . snd) 1 xs :: Integer
  pure $ Map.fromList
    [ (v, fromInteger (numerator (x * fromInteger scale))) | (v, x) <- xs ]
  where
    toRow e@(EqR lhs rhs _) = Row
      { rowCoefs = IntMap.filter (/= 0) $ IntMap.fromListWith (+)
          ([ (l, 1) | l <- lhs ] <> [ (rhs, -1) ])
      , rowConst = fromIntegral (lb rhs) - sum (fmap (fromIntegral . lb) lhs)
      , rowIsEq = True
      , rowFrom = [e]
      }
    trivialOk r
      | rowIsEq r = rowConst r == 0
      | otherwise = rowConst r >= 0
    zeroSatisfies = trivialOk
    vacuous r = not (rowIsEq r) && rowConst r >= 0 && all (<= 0) (IntMap.elems (rowCoefs r))
    backSubstitute (Elim v coefs c k) ys =
      let s = sum [ a * IntMap.findWithDefault 0 u ys | (u, a) <- IntMap.toList coefs ]
      in IntMap.insert v (max 0 ((c - s) / k)) ys

-- | Sparse Gaussian elimination that keeps nonnegativity: every variable
-- occurring in some equality is solved for from one of them (the
-- shortest), substituted into every other row it occurs in, and the
-- solving row becomes the inequality @y_v >= 0@ over the rest. Variables
-- with the fewest occurrences go first to limit fill-in. Afterwards no
-- equality has a variable left, so the residual is a system of
-- inequalities over the free variables only. Each step removes one
-- variable from the system, so this terminates.
eliminate :: (Int -> Bool) -> IntMap Row -> (IntMap Row, [Elim])
eliminate eligible rows0 = passes rows0 (occurrences rows0) [] where
  occurrences rows = IntMap.fromListWith IntSet.union
    [ (v, IntSet.singleton i) | (i, r) <- IntMap.toList rows
    , v <- IntMap.keys (rowCoefs r) ]
  passes rows occ elims =
    let candidates = sortOn snd
          [ (v, IntSet.size is) | (v, is) <- IntMap.toList occ, eligible v
          , any (\i -> maybe False rowIsEq (IntMap.lookup i rows)) (IntSet.toList is) ]
    in if null candidates
      then (rows, elims)
      else let (rows', occ', elims') = foldl step (rows, occ, elims) (fmap fst candidates)
           in passes rows' occ' elims'
  step (rows, occ, elims) v =
    let is = IntSet.toList (IntMap.findWithDefault IntSet.empty v occ)
        eqRows = [ (i, r) | i <- is, Just r <- [IntMap.lookup i rows], rowIsEq r
                 , IntMap.member v (rowCoefs r) ]
    in case sortOn (IntMap.size . rowCoefs . snd) eqRows of
      [] -> (rows, occ, elims)
      ((i, r) : _) ->
        let k = rowCoefs r IntMap.! v
            rest = IntMap.delete v (rowCoefs r)
            c = rowConst r
            pivotRow = if k > 0
              then r { rowCoefs = rest, rowIsEq = False }
              else r { rowCoefs = IntMap.map negate rest, rowConst = negate c
                     , rowIsEq = False }
            substitute (rs, oc) j = case IntMap.lookup j rs of
              Just rj | Just a <- IntMap.lookup v (rowCoefs rj) ->
                let f = a / k
                    coefs' = IntMap.filter (/= 0) $ IntMap.unionWith (+)
                      (IntMap.delete v (rowCoefs rj)) (IntMap.map (negate . (f *)) rest)
                    rj' = rj { rowCoefs = coefs', rowConst = rowConst rj - f * c
                             , rowFrom = rowFrom rj <> rowFrom r }
                    gone = IntMap.keys (IntMap.difference (rowCoefs rj) coefs')
                    new = IntMap.keys (IntMap.difference coefs' (rowCoefs rj))
                    oc' = foldr (IntMap.insertWith IntSet.union `flip` IntSet.singleton j)
                            (foldr (IntMap.adjust (IntSet.delete j)) oc gone) new
                in (IntMap.insert j rj' rs, oc')
              _unchanged -> (rs, oc)
            (rows1, occ1) = foldl substitute (rows, occ) (filter (/= i) is)
            rows2 = IntMap.insert i pivotRow rows1
            occ2 = IntMap.delete v occ1
        in (rows2, occ2, Elim v rest c k : elims)

-- | Values of the residual system's variables from a two-phase exact
-- simplex: phase one finds a feasible vertex or names the rows that
-- cannot hold together, phase two minimizes the weighted sum of the
-- variables.
simplexSolve :: (Int -> Integer) -> IntMap Row -> Either [EqR] (IntMap Rational)
simplexSolve weight rows
  | IntMap.null rows = Right IntMap.empty
  | not (any rowIsEq (IntMap.elems rows)) = dualSolve weight rows
  | otherwise =
      let vars = IntSet.toList . IntSet.unions $ fmap (IntMap.keysSet . rowCoefs) (IntMap.elems rows)
          nVars = length vars
          colOf = IntMap.fromList (zip vars [0 ..])
          varOf = IntMap.fromList (zip [0 ..] vars)
          rowList = zip [0 ..] (IntMap.elems rows)
          rowByIndex = IntMap.fromList rowList
          nRows = length rowList
          slackBase = nVars
          artBase = nVars + nRows
          -- row i: coefs over var columns (+ slack column for an
          -- inequality), rhs made nonnegative. An inequality with a
          -- nonnegative constant starts from its slack; only the other
          -- rows get an artificial column artBase+i, so phase one is as
          -- small as the lower bounds make it
          build (i, r) =
            let base = IntMap.fromList [ (colOf IntMap.! v, a) | (v, a) <- IntMap.toList (rowCoefs r) ]
                withSlack = if rowIsEq r then base else IntMap.insert (slackBase + i) 1 base
                (coefs, b) = if rowConst r >= 0
                  then (withSlack, rowConst r)
                  else (IntMap.map negate withSlack, negate (rowConst r))
                slackStarts = not (rowIsEq r) && rowConst r >= 0
            in if slackStarts
              then (i, ((coefs, b), slackBase + i))
              else (i, ((IntMap.insert (artBase + i) 1 coefs, b), artBase + i))
          built = fmap build rowList
          tRows = IntMap.fromList [ (i, rb) | (i, (rb, _)) <- built ]
          basis0 = IntMap.fromList [ (i, c) | (i, (_, c)) <- built ]
          artRowsInit = [ i | (i, (_, c)) <- built, c >= artBase ]
          obj1 = IntMap.filter (/= 0) . IntMap.unionsWith (+) $
            [ IntMap.map negate (IntMap.filterWithKey (\c _ -> c < artBase) coefs)
            | i <- artRowsInit, let (coefs, _) = tRows IntMap.! i ]
          phase1 = if null artRowsInit
            then mkTab tRows basis0 IntMap.empty
            else runSimplex (mkTab tRows basis0 obj1)
          blamed = concat
            [ rowFrom (rowByIndex IntMap.! i)
            | (i, (_, b)) <- IntMap.toList (tbRows phase1)
            , tbBasis phase1 IntMap.! i >= artBase, b > 0 ]
      in if not (null blamed)
        then Left blamed
        else
          let cleaned = dropArtificials artBase phase1
              cost c = if c < slackBase then fromInteger (weight (varOf IntMap.! c)) else 0 :: Rational
              obj2 = IntMap.filter (/= 0) . IntMap.unionsWith (+) $
                IntMap.fromList [ (c, cost c) | c <- [0 .. artBase - 1] ]
                  : [ IntMap.map (negate . (cost (tbBasis cleaned IntMap.! i) *)) coefs
                    | (i, (coefs, _)) <- IntMap.toList (tbRows cleaned)
                    , cost (tbBasis cleaned IntMap.! i) /= 0 ]
              obj2' = foldr IntMap.delete obj2 (IntMap.elems (tbBasis cleaned))
              phase2 = runSimplex cleaned { tbObj = obj2' }
              values = IntMap.fromList
                [ (varOf IntMap.! c, b)
                | (i, (_, b)) <- IntMap.toList (tbRows phase2)
                , let c = tbBasis phase2 IntMap.! i, c < slackBase ]
          in Right values

data Tab = Tab
  { tbRows  :: IntMap (IntMap Rational, Rational) -- ^ row: coefficients by column, rhs
  , tbBasis :: IntMap Int                         -- ^ row: its basic column
  , tbObj   :: IntMap Rational                    -- ^ reduced costs of nonbasic columns
  , tbCols  :: IntMap IntSet                      -- ^ column: the rows with a nonzero
                                                  --   entry in it (the sparse column
                                                  --   index a pivot walks)
  , tbNeg   :: IntSet                             -- ^ rows whose rhs is negative
  }

-- | A tableau with its indices built from the rows.
mkTab :: IntMap (IntMap Rational, Rational) -> IntMap Int -> IntMap Rational -> Tab
mkTab rows basis obj = Tab rows basis obj cols neg where
  cols = IntMap.fromListWith IntSet.union
    [ (c, IntSet.singleton i) | (i, (row, _)) <- IntMap.toList rows, c <- IntMap.keys row ]
  neg = IntMap.keysSet (IntMap.filter ((< 0) . snd) rows)

-- | Remove a row, keeping the indices consistent.
deleteRow :: Int -> Tab -> Tab
deleteRow i tab = case IntMap.lookup i (tbRows tab) of
  Nothing -> tab
  Just (row, _) -> tab
    { tbRows = IntMap.delete i (tbRows tab)
    , tbBasis = IntMap.delete i (tbBasis tab)
    , tbCols = foldr (IntMap.adjust (IntSet.delete i)) (tbCols tab) (IntMap.keys row)
    , tbNeg = IntSet.delete i (tbNeg tab)
    }

-- | Pivot row @r@ on column @c@. Only the rows with a nonzero entry in
-- column @c@ change, and the column index says which those are, so a
-- pivot costs the column's density times the pivot row's length rather
-- than a pass over the whole tableau.
pivot :: Int -> Int -> Tab -> Tab
pivot r c (Tab rows basis obj cols neg) =
  let (prow, pb) = rows IntMap.! r
      p = prow IntMap.! c
      prow' = IntMap.map (/ p) prow
      pb' = pb / p
      combine a row = IntMap.filter (/= 0) $
        IntMap.unionWith (+) row (IntMap.map (negate . (a *)) prow')
      -- the column index is a superset: an entry that cancelled to zero
      -- stays listed and is skipped here, which is cheaper than keeping
      -- the index exact
      affected = [ j | j <- IntSet.toList (IntMap.findWithDefault IntSet.empty c cols)
                 , j /= r, IntMap.member c (fst (rows IntMap.! j)) ]
      step (rs, cs, ng) j =
        let (row, b) = rs IntMap.! j
            a = row IntMap.! c
            row' = combine a row
            b' = b - a * pb'
            new = IntMap.keys (IntMap.difference prow' row)
            cs' = foldr (\k -> IntMap.insertWith IntSet.union k (IntSet.singleton j)) cs new
            ng' = if b' < 0 then IntSet.insert j ng else IntSet.delete j ng
        in (IntMap.insert j (row', b') rs, cs', ng')
      (rows1, cols1, neg1) = foldl step (rows, cols, neg) affected
      -- scaling the pivot row changes no sparsity pattern; afterwards
      -- column c is nonzero in row r alone
      rows' = IntMap.insert r (prow', pb') rows1
      cols' = cols1
      neg' = if pb' < 0 then IntSet.insert r neg1 else IntSet.delete r neg1
      obj' = maybe obj (`combine` obj) (IntMap.lookup c obj)
  in Tab rows' (IntMap.insert r c basis) obj' cols' neg'

-- | Minimize. Pricing is Dantzig.s (the most negative reduced cost
-- enters) while pivots are non-degenerate, and Bland.s (the
-- lowest-numbered improving column enters, the minimum-ratio row with the
-- lowest-numbered basic column leaves) after a degenerate pivot. Every
-- non-degenerate pivot lowers an objective bounded below over finitely
-- many vertices, and a run of degenerate pivots under Bland.s rule cannot
-- cycle, so this terminates.
runSimplex :: Tab -> Tab
runSimplex = go False where
  go bland tab = case entering of
    Nothing -> tab
    Just c -> case leaving c of
      Nothing -> tab -- unbounded: impossible for a nonnegative objective
      Just (r, degenerate) -> go degenerate (pivot r c tab)
    where
      improving = filter ((< 0) . snd) (IntMap.toAscList (tbObj tab))
      entering = case improving of
        [] -> Nothing
        (first : _) | bland -> Just (fst first)
        _ -> Just (fst (minimumBy (comparing snd) improving))
      leaving c =
        let candidates = [ (b / a, tbBasis tab IntMap.! i, i)
                         | i <- IntSet.toList (IntMap.findWithDefault IntSet.empty c (tbCols tab))
                         , Just (row, b) <- [IntMap.lookup i (tbRows tab)]
                         , Just a <- [IntMap.lookup c row], a > 0 ]
        in case candidates of
          [] -> Nothing
          _  -> let (ratio, _, i) = minimum candidates in Just (i, ratio == 0)

-- | After phase one, pivot every artificial column out of the basis (its
-- value is zero, so any nonzero entry of a real column will do) or drop
-- the row if it has none (it was redundant), then forget the artificial
-- columns.
dropArtificials :: Int -> Tab -> Tab
dropArtificials artBase tab0 =
  let tab1 = foldr step tab0 (IntMap.toList (tbBasis tab0))
      step (i, c) tab
        | c < artBase = tab
        | otherwise = case IntMap.lookup i (tbRows tab) of
            Nothing -> tab
            Just (row, _) ->
              case [ j | (j, a) <- IntMap.toAscList row, j < artBase, a /= 0 ] of
                (j : _) -> pivot i j tab
                [] -> deleteRow i tab
      strip = IntMap.filterWithKey (\c _ -> c < artBase)
  in mkTab (IntMap.map (first strip) (tbRows tab1)) (tbBasis tab1)
       (strip (tbObj tab1))

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
  (bEnv, tEnv, sRes) <- walkTop applyToInput what term
  vals <- solveConstraints
  pure (bEnv, tEnv, sRes, vals)

-- | The structural part of 'analyzeTopWith': walk, dispatch, and presolve
-- (which is where type cycles and boxed/unboxed clashes surface, with
-- blame), without the solve.
walkTop :: Bool -> String -> Term3Lifting -> EALM (BVar, Tau, Sigma)
walkTop applyToInput what term = do
  unit <- freshB
  void . constrainB unit . ForcedLevel 1 $
    Blame (GeneratedLoc "EAL unit" Nothing) "the unit box count"
  bEnv <- freshB
  tEnv <- freshTau
  ctx <- frameContext unit Nothing what bEnv tEnv term
  rootBase <- forcedZeroB $
    Blame (GeneratedLoc "EAL root" Nothing) "the program's root sits at depth zero"
  sRes <- viewNode ctx (Paths Nothing rootBase) term
  resolveApplies
  when applyToInput $ virtualMainApply sRes >> resolveApplies
  presolve
  pure (bEnv, tEnv, sRes)

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
            (ApplySite fnT env so vAnno mempty)
            (esApplies st)
        , esNextApply = esNextApply st + 1 }

leafDepths :: Map Int Int -> EALM [Int]
leafDepths vals = State.gets esLeafPaths >>= mapM (depth . snd) where
  value r = fromMaybe 0 $ Map.lookup r vals
  depth vs = sum . fmap value <$> mapM findB vs

-- | The deepest leaf of each body, relative to its instances' bases: the
-- max box depth inside the body as the global pass solved it.
bodyLeafDepths :: Map Int Int -> EALM (Map FunctionIndex Int)
bodyLeafDepths vals = do
  leaves <- State.gets esLeafPaths
  depths <- forM [ (fi, d) | (Just fi, [_, d]) <- leaves ] $ \(fi, d) ->
    (,) fi . (\r -> fromMaybe 0 (Map.lookup r vals)) <$> findB d
  pure (Map.fromListWith max depths)

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

-- | The syntactic half of a body's guidance: usage and speculatability
-- need no derivation. Bangs, levels and the capture layout are the
-- global pass's to fill.
syntacticGuidance :: Map (Digest SHA256) (FunctionIndex, Term3Lifting)
                  -> FunctionIndex -> Term3Lifting -> CodeGuidance
syntacticGuidance bodies fi body = CodeGuidance
  { cgIndex = fi
  , cgUsage = fmap fst (envUsageL body)
  , cgEnvBang = 0
  , cgMaxLevel = 0
  , cgSpeculatable = not (unsizedIn bodies body)
  , cgCaptureLayout = Nothing
  }

-- | Infer one lifted body standalone, dispatching the code it applies from
-- the DeferMap, and package the result as guidance. This localizes a
-- failure of main to the bodies that fail on their own: structure only
-- (walk, dispatch, presolve), since the standalone system is never
-- solved and its levels are never reported.
summarizeBody :: Map (Digest SHA256) (FunctionIndex, Term3Lifting)
              -> FunctionIndex -> Term3Lifting
              -> Either EALError CodeGuidance
summarizeBody bodies fi body =
  State.evalState (runExceptT go) (initEALState { esBodies = bodies }) where
    go = do
      _ <- walkTop False ("env of lifted body " <> show fi) body
      pure (syntacticGuidance bodies fi body)

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

-- | Infer EAL annotations over a lifted program. Main is analyzed
-- globally first: every DeferRef occurrence instantiates its body there,
-- so a certified main has certified every body's instances in the
-- program, and bodies the program carries but never applies are covered
-- too — the certificate covers all the code the program contains. A
-- body's standalone constraints are a subset of its instance's (the
-- standalone frame assumes nothing about the env, and every derivation
-- step only adds constraints), so when main certifies no body can fail
-- on its own and the per-body guidance is read off the global pass with
-- no further derivation. Only when main fails does each unique body get
-- a standalone verdict, to localize the failure (which bodies fail on
-- their own, and why) and to blame main's own failure on a failing
-- dependency.
inferEALLifted :: DeferMap -> Term3Lifting -> EALLiftedResult
inferEALLifted (DeferMap dm) mainTerm = case runMain of
  Right (r, layouts, bodyLevels) ->
    let guidanceOf h (fi, body) = Right (syntacticGuidance dm fi body)
          { cgCaptureLayout = Map.lookup h layouts
          , cgEnvBang = Map.findWithDefault 0 fi (ealDeferBangs r)
          , cgMaxLevel = Map.findWithDefault 0 fi bodyLevels }
    in EALLiftedResult (Map.mapWithKey guidanceOf dm) (Right r)
  Left mainError ->
    EALLiftedResult bodyResults (withDeps mainTerm (Left mainError))
  where
    -- the localizing pass: structural per-body verdicts, with levels and
    -- layouts left at their defaults (nothing here is a certificate; a
    -- consumer only reads guidance under a certified main)
    bodyResults = Map.mapWithKey summarize dm
    summarize _h (fi, body) = withDeps body $ summarizeBody dm fi body
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
    runMain = State.evalState (runExceptT goMain)
      (initEALState { esBodies = dm })
    goMain = do
      (bMain, _, sRes, vals) <- analyzeTopWith True "program input" mainTerm
      let value r = fromMaybe 0 $ Map.lookup r vals
      topBang <- value <$> findB bMain
      defers <- State.gets esDefers >>= fmap (Map.fromListWith max) .
        traverse (\(fi, b) -> (,) fi . value <$> findB b)
      depths <- leafDepths vals
      levels <- bodyLeafDepths vals
      shapes <- groundCaptureShapes
      mainShape <- shapeOfSigma sRes
      pure ( EALResult
               { ealTopLevelBang = topBang
               , ealDeferBangs = defers
               , ealMaxLevel = maximum (0 : depths)
               , ealMainShape = mainShape
               }
           , shapes, levels )

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

-- | Split rows into connected components (rows sharing a variable are
-- connected), by union-find over the variables.
components :: IntMap Row -> [IntMap Row]
components rows =
  let vars = IntSet.toList . IntSet.unions $ fmap (IntMap.keysSet . rowCoefs) (IntMap.elems rows)
      -- a bipartite graph of rows and variables; 'Graph.components'
      -- reads it undirected, so one direction of edge is enough
      rowNodes = [ ((), (0 :: Int, i), [ (1, v) | v <- IntMap.keys (rowCoefs r) ])
                 | (i, r) <- IntMap.toList rows, not (IntMap.null (rowCoefs r)) ]
      varNodes = [ ((), (1, v), []) | v <- vars ]
      (g, nodeFromVertex, _) = Graph.graphFromEdges (rowNodes <> varNodes)
      keyOf v = let (_, k, _) = nodeFromVertex v in k
      rowsOf t = IntMap.fromList
        [ (i, rows IntMap.! i) | (0, i) <- fmap keyOf (Tree.flatten t) ]
  in filter (not . IntMap.null) (fmap rowsOf (Graph.components g))

-- | Dual simplex for a residual of inequalities only (what 'eliminate'
-- leaves). The slack basis is dual feasible from the start, because every
-- weight is positive and slacks cost nothing, and it is primal infeasible
-- only on the rows a lower bound made negative. Each pivot repairs one
-- such row: the infeasible basic variable with the lowest index leaves
-- (Bland), and the column minimizing reduced cost over its negative entry
-- enters, lowest index on ties; with that rule the dual simplex cannot
-- cycle, so it terminates. A row with no negative entry cannot be
-- repaired: the system is infeasible and the row's origins are blamed.
--
-- Rows enter the tableau lazily: only the rows the current point violates
-- are in it (initially those a lower bound made negative), and once the
-- active rows are satisfied the waiting rows are evaluated at the point,
-- the violated ones are rewritten over the current nonbasic columns and
-- added (primal infeasible, dual feasibility untouched), and the dual
-- simplex resumes. The active set is a relaxation, so a point satisfying
-- every row is optimal for the whole system, and each outer step adds at
-- least one of finitely many rows. A pivot then touches the active rows
-- alone, which stay a small fraction of the residual.
dualSolve :: (Int -> Integer) -> IntMap Row -> Either [EqR] (IntMap Rational)
dualSolve weight rows =
  let vars = IntSet.toList . IntSet.unions $ fmap (IntMap.keysSet . rowCoefs) (IntMap.elems rows)
      colOf = IntMap.fromList (zip vars [0 ..])
      varOf = IntMap.fromList (zip [0 ..] vars)
      rowList = zip [0 ..] (IntMap.elems rows)
      rowByIndex = IntMap.fromList rowList
      slackBase = length vars
      coefsOf r = IntMap.fromList
        [ (colOf IntMap.! v, a) | (v, a) <- IntMap.toList (rowCoefs r) ]
      build (i, r) = (i, (IntMap.insert (slackBase + i) 1 (coefsOf r), rowConst r))
      (active0, waiting0) = partition (\(_, r) -> rowConst r < 0) rowList
      tRows = IntMap.fromList (fmap build active0)
      basis0 = IntMap.fromList [ (i, slackBase + i) | (i, _) <- active0 ]
      obj0 = IntMap.fromList [ (colOf IntMap.! v, fromInteger (weight v)) | v <- vars ]
      go tab =
        case IntSet.toList (tbNeg tab) of
          [] -> Right tab
          infeasible ->
            let r = minimumBy (comparing (tbBasis tab IntMap.!)) infeasible
                (row, _) = tbRows tab IntMap.! r
                candidates =
                  [ (IntMap.findWithDefault 0 j (tbObj tab) / negate a, j)
                  | (j, a) <- IntMap.toList row, a < 0 ]
            in case candidates of
                 [] -> Left (rowFrom (rowByIndex IntMap.! r))
                 _  -> go (pivot r (snd (minimum candidates)) tab)
      -- the current point: basic structural columns carry their row's
      -- rhs, every other column is zero
      pointOf tab = IntMap.fromList
        [ (c, b) | (i, (_, b)) <- IntMap.toList (tbRows tab)
        , let c = tbBasis tab IntMap.! i, c < slackBase ]
      -- a waiting row over the current nonbasic columns: substitute every
      -- basic structural column by its tableau row
      addRow tab (i, r) =
        let rowOfCol = IntMap.fromList [ (c, ri) | (ri, c) <- IntMap.toList (tbBasis tab) ]
            coefs0 = coefsOf r
            substitute (cs, b) (j, a) = case IntMap.lookup j rowOfCol of
              Nothing -> (cs, b)
              Just ri ->
                let (prow, pb) = tbRows tab IntMap.! ri
                in ( IntMap.filter (/= 0) $
                       IntMap.unionWith (+) cs (IntMap.map (negate . (a *)) prow)
                   , b - a * pb )
            (coefs, b') = foldl substitute (coefs0, rowConst r)
                            (IntMap.toList coefs0)
            coefs' = IntMap.insert (slackBase + i) 1 coefs
        in tab { tbRows = IntMap.insert i (coefs', b') (tbRows tab)
               , tbBasis = IntMap.insert i (slackBase + i) (tbBasis tab)
               , tbCols = foldr (\k -> IntMap.insertWith IntSet.union k (IntSet.singleton i))
                            (tbCols tab) (IntMap.keys coefs')
               , tbNeg = if b' < 0 then IntSet.insert i (tbNeg tab) else tbNeg tab }
      loop tab waiting = do
        tab' <- go tab
        let point = pointOf tab'
            value r = sum [ a * IntMap.findWithDefault 0 (colOf IntMap.! v) point
                          | (v, a) <- IntMap.toList (rowCoefs r) ]
            (violated, waiting') = partition (\(_, r) -> value r > rowConst r) waiting
        if null violated
          then pure tab'
          else loop (foldl addRow tab' violated) waiting'
  in do
    tab <- loop (mkTab tRows basis0 obj0) waiting0
    pure $ IntMap.fromList
      [ (varOf IntMap.! c, b)
      | (i, (_, b)) <- IntMap.toList (tbRows tab)
      , let c = tbBasis tab IntMap.! i, c < slackBase ]

-- | A closed data tree: Zero, or a pair of closed data trees.
dataLiteral :: Term3Lifting -> Bool
dataLiteral (_ :< t) = case t of
  BasicFW ZeroSF       -> True
  BasicFW (PairSF a b) -> dataLiteral a && dataLiteral b
  _notData             -> False
