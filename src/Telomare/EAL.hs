{-# LANGUAGE DeriveFoldable   #-}
{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}

-- | Elementary Affine Logic annotation inference for 'Term3'.
--
-- This decorates a Term3 program with EAL box levels, in the spirit of
-- Coppola-Martini decoration inference: every AST edge gets a
-- natural-number variable counting the box doors on that edge, and the EAL
-- variable conditions become linear constraints over the naturals. A
-- successful inference is an elementary-time certificate for the term; the
-- maximum box nesting depth is the height of the elementary bound's tower.
--
-- There is no type skeleton. Where the usual presentation routes bang
-- variables from producers to consumers through unification of
-- bang-annotated types, this implementation routes them through a
-- closure-flow analysis (0CFA) plus absolute level variables:
--
--   * Every node gets a level @L@ with @L(child) = L(parent) + edge boxes@.
--   * A flow fixpoint computes which values (closures, gates, aborts,
--     pairs, data, or unknown) can reach each SetEnv operator and each
--     projection target, remembering each value's construction node.
--   * A consumer must sit at its producer's level: applying, projecting, or
--     switching on a value opens exactly the boxes between them. An operand
--     instead enters its callee at the callee's entry level plus its env
--     bang, and a Defer's entry level unifies with its application sites.
--   * Env occurrences sit at frame entry plus the frame's env bang, and a
--     duplicated env path forces that bang to at least one (contraction
--     needs a box).
--
-- Notably absent compared to a typed presentation:
--
--   * Gate branches are never unified with each other; a gate switch is a
--     flow union of its branches. Branch closures of different shapes
--     coexist freely.
--   * There is no occurs check and no recursive-type error. Non-terminating
--     self-application is instead rejected by its level arithmetic: the
--     constraints demand an unbounded box tower, which surfaces as the
--     level cap being exceeded ('EALSolverGaveUp'). Unapplied
--     self-application bodies are values and are accepted.
--   * Data (Zero and pairs of data) carries no levels at all: it cannot
--     encode divergence, so it moves between levels freely. Only its
--     duplication is counted, via env-path contraction.
--
-- Adaptations to Telomare:
--
--   * Each Defer body has exactly one free variable (Env), so promotion
--     constraints reduce to bookkeeping at Env occurrences.
--   * Contraction is detected at projection-path granularity: using
--     @Left Env@ and @Right Env@ once each is linear destructuring, not
--     duplication. Only overlapping uses of the same Env path force the
--     domain bang to be at least one.
--   * Gate branches are counted multiplicatively (evaluation is strict, so
--     both branches consume their Env occurrences).
--   * Term3Unsized is treated exactly like an Env occurrence, mirroring the
--     type checker.
--   * Term3CheckingWrapper is analyzed as the application
--     'removeRefinementWrappers' converts it to: the check function is
--     applied to the wrapped value (a virtual app site whose result is
--     discarded, matching the abort-on-check), and the wrapped value
--     passes through as the wrapper's result.
--
-- Inference is monomorphic: a Defer applied from several sites unifies its
-- entry level across all of them. The constraint solver is a
-- propagate-then-repair heuristic with caps rather than a complete ILP
-- procedure; both limitations surface as errors rather than wrong
-- certificates.
--
-- The analyzer runs only over defer-lifted programs (see
-- 'Telomare.Resolver.deferLift'): every Defer body is hash-keyed in the
-- DeferMap and referenced via DeferRef, so frames are built in exactly one
-- place and raw DeferSF never reaches the walker. 'inferEALLifted' first
-- gives each unique body a standalone verdict (localizing failures and
-- reusing work under dedup), then analyzes main globally, walking a fresh
-- copy of the referenced body at every DeferRef, so inter-body level flow
-- is exact and per-site: deduplication never merges distinct call sites'
-- flows (the shared application combinator would otherwise mix every
-- operand in the program through one env node).
module Telomare.EAL where

import Control.Applicative ((<|>))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (foldM, forM_, when)
import Control.Monad.Except
import Control.Monad.RWS (RWS, runRWS, tell)
import Control.Monad.State (MonadState, State)
import qualified Control.Monad.State as State
import Crypto.Hash (Digest, SHA256)
import Data.Foldable (toList)
import Data.List (minimumBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust)
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
levelCap = 64

-- | A bang-count variable (also used for per-edge box counts and absolute
-- node levels).
newtype BVar = BVar { unBVar :: Int } deriving (Eq, Ord, Show)

-- | Where and why a constraint arose, for error reporting.
data Blame = Blame LocTag String deriving (Eq, Show)

data EALError
  -- | The flow analysis proved that EVERY value reaching a consumer has
  -- the wrong shape (data applied as a function, a function where data is
  -- required, ...). Mixed unions are tolerated — see 'mustFail'.
  = EALTypeMismatch LocTag String
  -- | A bang class is required to be boxed (first blame) and forced to be
  -- unboxed (second blame). This is the interesting error for affine-repair
  -- transformations: it names the duplication and the site that forbids
  -- boxing it.
  | EALBoxConflict Blame Blame
  -- | Constraint solving exceeded a cap or failed to converge. Level-cap
  -- blowout is the shape non-terminating self-application takes here: its
  -- equations demand an unbounded box tower.
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

-- | Sum equation: sum of lhs = rhs. Generated over 'BVar's; 'solve'
-- fmaps the variables to their union-find roots before interpreting.
data SumEq v = SumEq
  { seLhs   :: [v]
  , seRhs   :: v
  , seBlame :: Blame
  } deriving (Functor, Show)

-- * Flow analysis domain

-- | A syntactic position in the walked program (or a virtual env-input
-- node of a Defer).
type NodeId = Int

-- | Abstract values. Every non-data tag remembers the node that constructed
-- the value, so consumers can unify their level with the producer's. Pair
-- tags also point at the component nodes. 'FTop' is the unknown value: it
-- imposes no constraints. 'FData' is level-free (data cannot encode
-- divergence).
data FlowTag
  = FData
  | FPair NodeId NodeId NodeId -- ^ origin, left component, right component
  | FClo NodeId -- ^ closure; its frame (when walked here) is registered
                --   under this node
  | FGate NodeId               -- ^ the gate value itself
  | FGateFn NodeId             -- ^ a gate applied to its scrutinee
  | FAbort NodeId
  | FAbortCont NodeId          -- ^ abort applied to its message (identity)
  | FTop
  deriving (Eq, Ord, Show)

-- | The producer node a consumer must level-match, if the value has one.
tagOrigin :: FlowTag -> Maybe NodeId
tagOrigin = \case
  FData          -> Nothing
  FTop           -> Nothing
  FPair o _ _    -> Just o
  FClo o         -> Just o
  FGate o        -> Just o
  FGateFn o      -> Just o
  FAbort o       -> Just o
  FAbortCont o   -> Just o

-- | Everything known about one walked frame (main, or one lifted Defer
-- body): allocated by 'setupFrame', and registered under the referencing
-- node for wiring applications.
data DeferInfo = DeferInfo
  { diEnvNode   :: NodeId -- ^ virtual node collecting all env inflows
  , diPathBangs :: Maybe BangTrie
    -- ^ box variable per used env path (and every prefix, structurally):
    -- the boxes on that component of the env value. Nothing if the body
    -- never touches its env.
  , diEntry     :: BVar   -- ^ absolute level the body executes at
  , diRoot      :: NodeId -- ^ body root (the application result)
  }

data AppSite = AppSite
  { asNode    :: NodeId
  , asOperand :: NodeId
  , asLoc     :: LocTag
  }

data ProjSite = ProjSite
  { psNode   :: NodeId
  , psTarget :: NodeId
  , psStep   :: Step
  , psLoc    :: LocTag
  }

-- | Fresh-variable supplies, shared by every stage.
data Supply = Supply
  { supNextVar  :: Int -- ^ next 'BVar'
  , supNextNode :: Int -- ^ next 'NodeId'
  }

-- | The declarative constraint system the generation phases produce: seed
-- classes from the walk, level unions and sum equations from the walk and
-- emission. 'solve' interprets it — nothing here is solver state.
data Constraints = Constraints
  { cSeeds  :: [(BVar, ClassInfo)]
    -- ^ initial classes; unions may later put two seeds in one class, so
    -- 'solve' merges seeds per root
  , cUnions :: [(BVar, BVar)] -- ^ level variables forced equal
  , cSumEqs :: [SumEq BVar]
  }

-- | The 0CFA flow graph: emitted by the walk, saturated by 'flowFixpoint',
-- then frozen — the emission phase receives it as a plain value and
-- cannot write it back.
data FlowGraph = FlowGraph
  { fgTags     :: Map NodeId (Set FlowTag)
  , fgEdges    :: Map NodeId (Set NodeId) -- ^ flow subset edges, src -> dsts
  , fgApps     :: [AppSite]
  , fgProjs    :: [ProjSite]
  , fgLevels   :: Map NodeId BVar
  , fgRegistry :: Map NodeId DeferInfo
    -- ^ frame of the body a DeferRef node references (global mode)
  }

-- levels and registry entries are keyed by fresh nodes, so their unions
-- are disjoint; tags and edges can genuinely merge (an env node collects
-- one edge per occurrence)
instance Semigroup FlowGraph where
  FlowGraph t1 e1 a1 p1 l1 r1 <> FlowGraph t2 e2 a2 p2 l2 r2 = FlowGraph
    (Map.unionWith (<>) t1 t2)
    (Map.unionWith (<>) e1 e2)
    (a1 <> a2) (p1 <> p2) (l1 <> l2) (r1 <> r2)

instance Monoid FlowGraph where
  mempty = FlowGraph mempty mempty mempty mempty mempty mempty

-- | Walk output only the result packaging reads
-- ('finishResult'/'summarizeBody').
data Reporting = Reporting
  { repDefers :: Map FunctionIndex [BVar]
    -- ^ per Defer: the path box variables of its env (reported as their max)
  , repLeaves :: [(BVar, Int)]
    -- ^ leaf level variables plus a constant offset (nonzero at references
    -- to summarized bodies), for the max depth
  }

instance Semigroup Reporting where
  Reporting d1 l1 <> Reporting d2 l2 =
    Reporting (Map.unionWith (<>) d1 d2) (l1 <> l2)

instance Monoid Reporting where
  mempty = Reporting mempty mempty

-- | What a DeferRef means to this analysis: the global pass walks a fresh
-- copy of the referenced body at each reference, a standalone pass
-- consults the body's summary. Fixed per run; each entry point hands it to
-- 'setupFrame', which threads it through the walk.
data AnalysisMode
  = GlobalMode (Map (Digest SHA256) (FunctionIndex, Term3Lifting))
  | StandaloneMode (Map (Digest SHA256) DeferSummary)

data EALResult = EALResult
  { ealTopLevelBang :: Int                  -- ^ bang on the program input
  , ealDeferBangs   :: Map FunctionIndex Int -- ^ env domain bang per Defer
  , ealMaxLevel     :: Int                  -- ^ max box nesting depth
  } deriving (Eq, Show)

-- | The result of inferring one lifted Defer body standalone.
data DeferSummary = DeferSummary
  { dsIndex    :: FunctionIndex -- ^ first-seen index, for reporting
  , dsEnvBang  :: Int           -- ^ solved bang on the body's env domain
                                --   (a lower bound; the global pass may
                                --   raise it)
  , dsMaxLevel :: Int           -- ^ max box depth inside the body (including
                                --   depths of bodies it references)
  } deriving (Eq, Show)

-- | Result of 'inferEALLifted': a verdict for every lifted body plus the
-- main term's result. Body verdicts survive even when main fails, which is
-- the point: they localize exactly which Defer bodies EAL-tag and which
-- don't.
data EALLiftedResult = EALLiftedResult
  { ealBodyResults :: Map (Digest SHA256) (Either EALError DeferSummary)
  , ealLiftedMain  :: Either EALError EALResult
  } deriving (Eq, Show)

-- * Variable and node supplies

nextVar :: Supply -> (BVar, Supply)
nextVar s = (BVar (supNextVar s), s { supNextVar = supNextVar s + 1 })

nextNode :: Supply -> (NodeId, Supply)
nextNode s = (supNextNode s, s { supNextNode = supNextNode s + 1 })

-- | Mint a fresh bang variable. The supply threads through every stage
-- (emission continues where the walk left it), so variables from
-- different stages never collide.
fresh :: MonadState Supply m => m BVar
fresh = State.state nextVar

freshNode :: WalkM NodeId
freshNode = State.state nextNode

-- * Bang classes

-- | The class an asserted constraint leaves behind: Nothing if it changes
-- nothing, Just the merged class otherwise. Throws on a level over the cap
-- or a boxed/unboxed conflict.
applyConstraint :: MonadError EALError m
  => ClassInfo -> ClassInfo -> m (Maybe ClassInfo)
applyConstraint ci nc = case nc of
  ForcedLevel n blame | n > levelCap ->
    throwError . EALSolverGaveUp $
      "bang level exceeded cap of " <> show levelCap <> ": " <> show blame
  _notExcessLevel -> do
    rc <- mergeClasses ci nc
    pure $ if rc /= ci then Just rc else Nothing

-- | Combine two constraints on the same class; throws 'EALBoxConflict' if
-- one forces boxing and the other forbids it. On ties this prefers its
-- FIRST argument: 'applyConstraint' and 'solve''s seeding pass the
-- existing class first and detect change by (in)equality, so re-asserting
-- a constraint that differs only in blame must merge to the existing class
-- exactly, or 'propagate' would see phantom changes and never converge.
mergeClasses :: MonadError EALError m => ClassInfo -> ClassInfo -> m ClassInfo
mergeClasses a b = case (a,b) of
  (Unrestricted, _) -> pure b
  (_, Unrestricted) -> pure a
  (ForcedLevel _ l, ForcedZero z) -> throwError $ EALBoxConflict l z
  (ForcedZero z, ForcedLevel _ l) -> throwError $ EALBoxConflict l z
  (ForcedLevel la _, ForcedLevel lb _) -> pure $ if la >= lb then a else b
  _forcedZero -> pure a

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

-- * Env usage analysis (contraction detection)

-- | A trie over env projection paths, mirroring the env value's pair
-- structure: the root is the whole env, children are the L/R components.
-- Nodes exist exactly for the used paths and their prefixes, so the
-- prefix-closure invariant the walker relies on holds by construction.
data PathTrie a = PathTrie
  { ptHere  :: a
  , ptLeft  :: Maybe (PathTrie a)
  , ptRight :: Maybe (PathTrie a)
  } deriving (Foldable, Show)

-- | Merge two tries, combining payloads where nodes coincide.
unionTrieWith :: (a -> a -> a) -> PathTrie a -> PathTrie a -> PathTrie a
unionTrieWith f (PathTrie a la ra) (PathTrie b lb rb) =
  PathTrie (f a b) (child la lb) (child ra rb) where
    child (Just u) (Just v) = Just (unionTrieWith f u v)
    child u v               = u <|> v

-- | Direct Env occurrences at exactly one path: how many, and where the
-- first one is (for blame). Nodes that are only prefixes of used paths
-- carry Nothing.
data PathUse = PathUse
  { puCount :: Int
  , puLoc   :: LocTag
  } deriving Show

type UsageTrie = PathTrie (Maybe PathUse)

-- | Collect Env (and Unsized) occurrences of one Defer body into a trie
-- keyed by the projection path directly applied to the occurrence (Nothing
-- if the body never touches its env). Does not descend into nested Defer
-- bodies (they are closed over their own Env), and DeferRefs are closed
-- values like defers.
envUsageL :: Term3Lifting -> Maybe UsageTrie
envUsageL = go [] where
  merge (Just u) (Just v) = Just (unionTrieWith mergeUse u v)
  merge u v               = u <|> v
  mergeUse a b = case (a, b) of
    (Just (PathUse c1 l1), Just (PathUse c2 _)) -> Just (PathUse (c1 + c2) l1)
    _ -> a <|> b
  -- the accumulated path is innermost projection first, which is the order
  -- the projections apply to the env value, so the trie descends it head
  -- first, unreversed
  occurrence path anno = go' path where
    go' []        = PathTrie (Just (PathUse 1 anno)) Nothing Nothing
    go' (SL : ps) = PathTrie Nothing (Just (go' ps)) Nothing
    go' (SR : ps) = PathTrie Nothing Nothing (Just (go' ps))
  go proj (anno :< t) = case t of
    StuckFW (LeftSF x) -> go (SL : proj) x
    StuckFW (RightSF x) -> go (SR : proj) x
    StuckFW EnvSF -> Just $ occurrence proj anno
    Term3LUnsized _ -> Just $ occurrence proj anno
    Term3LDeferRef _ -> Nothing
    StuckFW (DeferSF _ _) -> Nothing
    -- the check function sees the whole env; the wrapped value keeps the
    -- projection chain (the wrapper is transparent to its result)
    Term3LCheckingWrapper _ tc c -> merge (go [] tc) (go proj c)
    BasicFW (PairSF a b) -> merge (go [] a) (go [] b)
    StuckFW (SetEnvSF x) -> go [] x
    -- gate is a value; branch and scrutinee usage flows through the
    -- SetEnv/Pair nodes of the GateSwitch encoding
    StuckFW GateSF -> Nothing
    BasicFW ZeroSF -> Nothing
    AbortFW _ -> Nothing
    _ -> Nothing

-- | Is a path with this direct use a contraction site, given whether any
-- of its sub-paths is used? Duplication is two direct uses, or a direct
-- use plus a sub-path use; disjoint sub-path uses (Left once, Right once)
-- are linear destructuring. Sub-path use is child existence: trie nodes
-- only exist on the way to occurrences.
contractionAt :: Maybe PathUse -> Bool -> Maybe LocTag
contractionAt use subUsed = case use of
  Just (PathUse c uloc) | c >= 2 || subUsed -> Just uloc
  _ -> Nothing

-- | All duplicated env paths, each of which needs a box of its own. A pure
-- view for tests and tooling; 'framePathBangs' applies the same rule
-- ('contractionAt') while annotating.
contractionSites :: Maybe UsageTrie -> [([Step], LocTag)]
contractionSites = foldMap (go []) where
  go rpath (PathTrie use lt rt) =
    let here = [ (reverse rpath, uloc)
               | Just uloc <- [contractionAt use (isJust lt || isJust rt)] ]
        sub s = foldMap (go (s : rpath))
    in here <> sub SL lt <> sub SR rt

-- * Constraint generation (syntactic walk)
--
-- The walk is a Writer computation: it consumes fresh names and emits
-- facts — flow-graph pieces, seed classes, sum equations, reporting
-- entries — and never reads anything back. 'runWalk' collects the
-- product; every later phase starts from it.

-- | The walk monad: fresh-name supply as state, 'WalkOut' as output.
type WalkM = ExceptT EALError (RWS () WalkOut Supply)

-- | Everything one walk emits.
data WalkOut = WalkOut
  { woFlow   :: FlowGraph
  , woSeeds  :: [(BVar, ClassInfo)]
    -- ^ initial classes (contraction facts); the variables are fresh and
    -- distinct, so they seed 'cClasses' without any merging
  , woSumEqs :: [SumEq BVar]
  , woReport :: Reporting
  }

instance Semigroup WalkOut where
  WalkOut f1 s1 e1 r1 <> WalkOut f2 s2 e2 r2 =
    WalkOut (f1 <> f2) (s1 <> s2) (e1 <> e2) (r1 <> r2)

instance Monoid WalkOut where
  mempty = WalkOut mempty mempty mempty mempty

-- ** Walk emitters, one per kind of fact

tellFlow :: FlowGraph -> WalkM ()
tellFlow fg = tell mempty { woFlow = fg }

tellTag :: NodeId -> FlowTag -> WalkM ()
tellTag n t = tellFlow mempty { fgTags = Map.singleton n (Set.singleton t) }

tellEdge :: NodeId -> NodeId -> WalkM ()
tellEdge src dst =
  tellFlow mempty { fgEdges = Map.singleton src (Set.singleton dst) }

tellLevel :: NodeId -> BVar -> WalkM ()
tellLevel n l = tellFlow mempty { fgLevels = Map.singleton n l }

tellApp :: AppSite -> WalkM ()
tellApp a = tellFlow mempty { fgApps = [a] }

tellProj :: ProjSite -> WalkM ()
tellProj p = tellFlow mempty { fgProjs = [p] }

tellRegistry :: NodeId -> DeferInfo -> WalkM ()
tellRegistry n di = tellFlow mempty { fgRegistry = Map.singleton n di }

tellSumEq :: Blame -> [BVar] -> BVar -> WalkM ()
tellSumEq blame lhs rhs = tell mempty { woSumEqs = [SumEq lhs rhs blame] }

tellSeed :: BVar -> ClassInfo -> WalkM ()
tellSeed bv ci = tell mempty { woSeeds = [(bv, ci)] }

tellLeaf :: BVar -> Int -> WalkM ()
tellLeaf l offset =
  tell mempty { woReport = mempty { repLeaves = [(l, offset)] } }

tellDefer :: FunctionIndex -> [BVar] -> WalkM ()
tellDefer fi bangs =
  tell mempty { woReport = mempty { repDefers = Map.singleton fi bangs } }

-- ** Walking terms

-- | 'framePathBangs' annotation of one env path: its box variable, and
-- whether the path has a direct occurrence in the body.
data PathBox = PathBox
  { pbBang :: BVar
  , pbUsed :: Bool
  } deriving Show

type BangTrie = PathTrie PathBox

-- | All box variables of one frame's env trie.
bangVars :: Maybe BangTrie -> [BVar]
bangVars = foldMap (fmap pbBang . toList)

data WalkCtx = WalkCtx
  { wcEnvNode   :: NodeId -- ^ flow source for Env occurrences
  , wcPathBangs :: Maybe BangTrie -- ^ box count per used env path/prefix
  , wcEntry     :: BVar   -- ^ absolute level this frame executes at
  , wcMode      :: AnalysisMode -- ^ what DeferRefs mean (fixed per run)
  }

-- | The box variables along a path's prefixes (including the path itself):
-- an occurrence at that path sits under all of them.
prefixBangs :: Maybe BangTrie -> [Step] -> WalkM [BVar]
prefixBangs mt p0 = go mt p0 where
  go Nothing _ = throwError . EALInternal $
    "no box variable for env path " <> showSteps p0
  go (Just t) steps = case steps of
    [] -> pure [pbBang (ptHere t)]
    (s : ps) -> (pbBang (ptHere t) :) <$>
      go (case s of SL -> ptLeft t; SR -> ptRight t) ps

-- | Each directly-used env path with the box variables along its prefixes
-- (including itself): the callee-side interface 'emitApp' wires operand
-- components with.
usedPathBangs :: Maybe BangTrie -> [([Step], [BVar])]
usedPathBangs = foldMap (go [] []) where
  go rpath rbangs (PathTrie (PathBox bv used) lt rt) =
    let rbangs' = bv : rbangs
        here = [(reverse rpath, reverse rbangs') | used]
        sub s = foldMap (go (s : rpath) rbangs')
    in here <> sub SL lt <> sub SR rt

-- | Allocate one frame's env machinery from its body's usage: a box
-- variable per used path and prefix, with duplicated paths forced boxed.
framePathBangs :: String -> Maybe UsageTrie -> WalkM (Maybe BangTrie)
framePathBangs what = mapM (go []) where
  go rpath (PathTrie use lt rt) = do
    bv <- fresh
    forM_ (contractionAt use (isJust lt || isJust rt)) $ \uloc ->
      tellSeed bv . ForcedLevel 1 $
        Blame uloc (what <> " path " <> showSteps (reverse rpath)
          <> " duplicated")
    PathTrie (PathBox bv (isJust use))
      <$> mapM (go (SL : rpath)) lt
      <*> mapM (go (SR : rpath)) rt

-- | Tags of a node in a frozen flow graph.
tagsIn :: FlowGraph -> NodeId -> Set FlowTag
tagsIn fg n = Map.findWithDefault Set.empty n (fgTags fg)

-- | Walk one term: give each node its level variable @L = parent level +
-- edge boxes@, record leaves and env occurrence level equations, tag
-- constructors with their abstract values, and collect application and
-- projection sites for the flow fixpoint. The @proj@ argument accumulates
-- the projection chain directly above the node (innermost first, mirroring
-- 'envUsageL'), so an env occurrence knows which path's boxes it sits
-- under.
walkNode :: WalkCtx -> BVar -> [Step] -> Term3Lifting -> WalkM NodeId
walkNode ctx parentL proj (_ :< Term3LCheckingWrapper loc tc c) = do
  -- mirror 'removeRefinementWrappers': the wrapper becomes an application
  -- of the check function to the wrapped value whose result is aborted on
  -- and discarded, with the wrapped value passing through as the result —
  -- a virtual (function, operand) pair fed to a virtual app site
  ntc <- walkNode ctx parentL [] tc
  nc <- walkNode ctx parentL proj c
  p <- freshNode
  s <- freshNode
  fresh >>= tellLevel p
  fresh >>= tellLevel s
  tellTag p (FPair p ntc nc)
  tellApp (AppSite s p loc)
  pure nc
walkNode ctx parentL proj (anno :< tt) = do
  n <- freshNode
  w <- fresh
  l <- fresh
  tellSumEq (Blame anno "node depth = parent depth + edge boxes")
    [parentL, w] l
  tellLevel n l
  let leaf = tellLeaf l 0
      tag = tellTag n
      envOccurrence = do
        -- the env value (and the projections peeling it) arrives at least
        -- at frame entry plus the boxes on the env itself (extra unopened
        -- boxes are weakening, harmless for termination — hence the slack);
        -- the extracted component sits at its full path's box sum, which is
        -- a leaf for the nesting bound but must not constrain this node's
        -- chain: the intermediate pairs are opened at their own depths.
        pvars <- prefixBangs (wcPathBangs ctx) proj
        dv <- fresh
        tellSumEq
          (Blame anno
            "env component depth = frame entry + its path's boxes")
          (wcEntry ctx : pvars) dv
        tellLeaf dv 0
        rootBang <- prefixBangs (wcPathBangs ctx) []
        slack <- fresh
        tellSumEq
          (Blame anno "env arrives at frame entry + its own boxes or deeper")
          (wcEntry ctx : slack : rootBang) l
        tellEdge (wcEnvNode ctx) n
      projSite step x = do
        nx <- walkNode ctx l (step : proj) x
        tellProj (ProjSite n nx step anno)
  case tt of
    BasicFW ZeroSF -> leaf >> tag FData
    BasicFW (PairSF a b) -> do
      na <- walkNode ctx l [] a
      nb <- walkNode ctx l [] b
      tag $ FPair n na nb
    StuckFW EnvSF -> envOccurrence
    Term3LUnsized _ -> envOccurrence
    StuckFW (DeferSF _ _) -> throwError $
      EALInternal "raw DeferSF in a lifted term"
    Term3LDeferRef h -> do
      tag $ FClo n
      case wcMode ctx of
        -- global mode: walk a fresh copy of the body per reference, so
        -- deduplication never merges distinct call sites' flows
        GlobalMode bodies -> case Map.lookup h bodies of
          Just (fi, body) -> do
            frame <- setupFrame (wcMode ctx)
              ("env of lifted body " <> show fi) body
            tellRegistry n frame
            tellDefer fi (bangVars (diPathBangs frame))
          Nothing -> throwError . EALInternal $
            "lifted defer not in the DeferMap " <> show h
        -- standalone mode: the body's interface is its summary
        StandaloneMode sums -> case Map.lookup h sums of
          Just ds -> tellLeaf l (dsMaxLevel ds)
          -- 'withDeps' put every reachable ref's summary in scope, so a
          -- miss is a bug in the dependency walk, not a failed body
          Nothing -> throwError . EALInternal $
            "no summary in scope for lifted defer " <> show h
    StuckFW (SetEnvSF x) -> do
      nx <- walkNode ctx l [] x
      tellApp (AppSite n nx anno)
    StuckFW GateSF -> leaf >> tag (FGate n)
    StuckFW (LeftSF x) -> projSite SL x
    StuckFW (RightSF x) -> projSite SR x
    AbortFW AbortF -> leaf >> tag (FAbort n)
    AbortFW (AbortedF _) -> leaf >> tag FData
    _ -> throwError $ EALInternal "unhandled term shape"
  pure n

-- * Fixpoint machinery

-- | Run every action (no short-circuiting — each fixpoint round must
-- visit every site, and the fuel accounting relies on it) and report
-- whether any of them changed anything.
anyChanges :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyChanges f = foldM (\acc x -> (acc ||) <$> f x) False

-- | Re-run a step reporting whether it changed anything until it makes no
-- change; throw 'EALSolverGaveUp' with the message if the fuel runs out.
fixpointWithFuel :: MonadError EALError m => Int -> String -> m Bool -> m ()
fixpointWithFuel fuel msg step = go fuel where
  go n = do
    when (n <= 0) . throwError $ EALSolverGaveUp msg
    changed <- step
    when changed $ go (n - 1)

-- * Flow fixpoint

-- | The fixpoint's private monad: the graph being saturated is its whole
-- state.
type FixM = ExceptT EALError (State FlowGraph)

tagsOf :: NodeId -> FixM (Set FlowTag)
tagsOf n = State.gets (Map.findWithDefault Set.empty n . fgTags)

addTagsM :: NodeId -> Set FlowTag -> FixM Bool
addTagsM n ts = do
  old <- tagsOf n
  let new = Set.union old ts
  if Set.size new == Set.size old
    then pure False
    else do
      State.modify $ \fg -> fg { fgTags = Map.insert n new (fgTags fg) }
      pure True

addEdge :: NodeId -> NodeId -> FixM Bool
addEdge src dst = do
  cur <- State.gets (Map.findWithDefault Set.empty src . fgEdges)
  if Set.member dst cur
    then pure False
    else do
      State.modify $ \fg ->
        fg { fgEdges = Map.insert src (Set.insert dst cur) (fgEdges fg) }
      pure True

-- | Saturate a walk's flow graph: propagate abstract values until stable —
-- along subset edges, through applications (wiring operands into callee
-- envs and callee results back to the site), and through projections. The
-- fuel is derived from the node count.
flowFixpoint :: Int -> FlowGraph -> Either EALError FlowGraph
flowFixpoint nodes fg0 =
  case State.runState (runExceptT saturate) fg0 of
    (Left e, _)   -> Left e
    (Right (), fg) -> Right fg
  where
    saturate = fixpointWithFuel (4 * nodes + 64)
      "flow analysis did not converge" $ do
        c1 <- propagateEdges
        c2 <- stepSites stepApp fgApps
        c3 <- stepSites stepProj fgProjs
        pure (c1 || c2 || c3)
    stepSites f sel = State.gets sel >>= anyChanges f
    propagateEdges = State.gets (Map.toList . fgEdges) >>= anyChanges
      (\(src, dsts) -> do
        ts <- tagsOf src
        if Set.null ts
          then pure False
          else anyChanges (`addTagsM` ts) (Set.toList dsts))
    stepApp (AppSite s x _) = do
      tx <- tagsOf x
      anyChanges goOperand (Set.toList tx)
      where
        top = addTagsM s (Set.singleton FTop)
        goOperand = \case
          FTop -> top
          FPair _ fv ev -> do
            tf <- tagsOf fv
            anyChanges (goOperator ev) (Set.toList tf)
          _ -> pure False
        goOperator ev = \case
          FClo o -> State.gets (Map.lookup o . fgRegistry) >>= \case
            Just di -> (||) <$> addEdge ev (diEnvNode di)
                            <*> addEdge (diRoot di) s
            -- summarized body: its result is opaque here
            Nothing -> top
          FGate _ -> addTagsM s (Set.singleton (FGateFn s))
          FGateFn _ -> do
            te <- tagsOf ev
            c1 <- anyChanges
              (\(lb, rb) -> (||) <$> addEdge lb s <*> addEdge rb s)
              [(lb, rb) | FPair _ lb rb <- Set.toList te]
            c2 <- if FTop `Set.member` te then top else pure False
            pure (c1 || c2)
          FAbort _ -> addTagsM s (Set.singleton (FAbortCont s))
          FAbortCont _ -> addEdge ev s
          FTop -> top
          _ -> pure False
    stepProj (ProjSite s x step _) = do
      tx <- tagsOf x
      anyChanges go (Set.toList tx)
      where
        go = \case
          FPair _ a b -> addEdge (case step of SL -> a; SR -> b) s
          FData -> addTagsM s (Set.singleton FData)
          FTop -> addTagsM s (Set.singleton FTop)
          _ -> pure False

-- * Level constraint emission from flows
--
-- The flow graph is final once 'flowFixpoint' returns, so this phase takes
-- it as a plain frozen value. Like the walk it is a Writer: it mints slack
-- variables and emits declarative constraints — level unions and sum
-- equations — and never reads a constraint back. 'solve' interprets them.

-- | The emission monad: fresh-name supply as state, 'EmitOut' as output.
type EmitM = ExceptT EALError (RWS () EmitOut Supply)

-- | The constraints one emission pass produces.
data EmitOut = EmitOut
  { eoUnions :: [(BVar, BVar)] -- ^ level variables forced equal
  , eoSumEqs :: [SumEq BVar]
  }

instance Semigroup EmitOut where
  EmitOut u1 e1 <> EmitOut u2 e2 = EmitOut (u1 <> u2) (e1 <> e2)

instance Monoid EmitOut where
  mempty = EmitOut mempty mempty

tellUnion :: BVar -> BVar -> EmitM ()
tellUnion a b = tell mempty { eoUnions = [(a, b)] }

tellEq :: Blame -> [BVar] -> BVar -> EmitM ()
tellEq blame lhs rhs = tell mempty { eoSumEqs = [SumEq lhs rhs blame] }

-- | Level variable of a node in a frozen flow graph.
levelIn :: FlowGraph -> NodeId -> EmitM BVar
levelIn fg n = case Map.lookup n (fgLevels fg) of
  Just l -> pure l
  Nothing -> throwError . EALInternal $
    "no level variable tracked for node " <> show n

-- | Unify a consumed value's production level with the consumption site's
-- level: the boxes between producer and consumer are exactly the ones
-- opened on the way.
consumeAt :: FlowGraph -> BVar -> FlowTag -> EmitM ()
consumeAt fg siteL t = case tagOrigin t of
  Nothing -> pure ()
  Just o -> levelIn fg o >>= tellUnion siteL

-- | Follow an env path through the flow graph: the nodes whose values can
-- be that component of the value at the start node. Unknown or data values
-- cut the search (they impose no level constraints).
pathNodes :: FlowGraph -> NodeId -> [Step] -> Set NodeId
pathNodes fg n0 = foldl stepInto (Set.singleton n0) where
  stepInto ns step = Set.unions . fmap (comp step) $ Set.toList ns
  comp step n = Set.fromList
    [ case step of SL -> a; SR -> b
    | FPair _ a b <- Set.toList (tagsIn fg n) ]

-- | Require a value to be data all the way down (no functions hiding
-- inside). Data carries no levels, so this is a shape check only.
-- | The must-fail policy for shape errors: a consumer is rejected only
-- when EVERY value that can reach it has the wrong shape. The runtime is
-- lazy (stuckness is a value until demanded), so a wrong-shaped member of
-- a flow union may belong to a path that is never demanded — erroring on
-- it would make the analyzer stricter than the semantics it certifies,
-- and branch-blind 0CFA unions manufacture exactly such members. A site
-- whose flows are exclusively wrong can never execute usefully and is
-- still rejected.
mustFail :: (FlowTag -> Bool) -> Set FlowTag -> Bool
mustFail ok ts = not (Set.null ts) && not (any ok ts)

-- | A gate inspects only its scrutinee's top constructor (any pair selects
-- the right branch, closures included), so the shape requirement is
-- zero-or-pair at the top — never a bare function value. Abort messages
-- need no check at all: the runtime truncates non-data message components
-- to Zero.
forceGateScrutinee :: FlowGraph -> LocTag -> NodeId -> EmitM ()
forceGateScrutinee fg loc n =
  when (mustFail switchable (tagsIn fg n)) . throwError . EALTypeMismatch loc $
    "gate scrutinee is never zero or a pair"
  where
    switchable = \case
      FData     -> True
      FTop      -> True
      FPair {}  -> True
      _function -> False

-- | Emit the level constraints of one application, once per value the flow
-- analysis proved can be its operator.
emitApp :: FlowGraph -> AppSite -> EmitM ()
emitApp fg (AppSite s x loc) = do
  let tx = tagsIn fg x
      pairish = \case
        FPair {}  -> True
        FTop      -> True
        _notPair  -> False
      callable = \case
        FData     -> False
        FPair {}  -> False
        _possibly -> True
  when (mustFail pairish tx) . throwError . EALTypeMismatch loc $
    "SetEnv operand is never a (function, env) pair: " <> show (Set.toList tx)
  siteL <- levelIn fg s
  -- pairs are passive conduits: opening the (function, env) pair imposes no
  -- level constraint; only the operator's code must level-match the site
  forM_ [(fv, ev) | FPair _ fv ev <- Set.toList tx] $ \(fv, ev) -> do
    let tf = tagsIn fg fv
    when (mustFail callable tf) . throwError . EALTypeMismatch loc $
      "applied value is never a function: " <> show (Set.toList tf)
    forM_ (filter callable (Set.toList tf)) $ \opTag -> do
      consumeAt fg siteL opTag
      case opTag of
        FClo o -> case Map.lookup o (fgRegistry fg) of
          Just di -> do
            -- the callee's body executes at the site's level, and each
            -- used component of the operand sits exactly its path's boxes
            -- deeper (this is the promotion condition: boxed components
            -- really are produced under their boxes)
            tellUnion siteL (diEntry di)
            forM_ (usedPathBangs (diPathBangs di)) $ \(p, pvars) ->
              forM_ (Set.toList (pathNodes fg ev p)) $ \m ->
                forM_ (Set.toList (tagsIn fg m)) $ \t' ->
                  forM_ (tagOrigin t') $ \o' -> do
                    lo <- levelIn fg o'
                    -- at least: extra unopened boxes are weakening
                    slack <- fresh
                    tellEq
                      (Blame loc $ "operand component " <> showSteps p
                        <> " enters the callee at its path's box depth")
                      (diEntry di : slack : pvars) lo
          -- summarized body (standalone mode): its level interface is
          -- unknown here; the global pass supplies the exact constraints
          Nothing -> pure ()
        FGate _ ->
          forceGateScrutinee fg loc ev
        -- abort messages are truncated to data by the runtime, so any
        -- shape may flow there; branch values keep their own producers
        -- (no branch unification)
        _ -> pure ()

-- | Emit the shape constraints of one projection. Pairs are passive
-- conduits: opening one imposes no level constraint (the compiled env
-- encoding re-projects shared pairs at different depths), and the
-- component keeps its own producer.
emitProj :: FlowGraph -> ProjSite -> EmitM ()
emitProj fg (ProjSite _ x _ loc) =
  when (mustFail projectable (tagsIn fg x)) . throwError . EALTypeMismatch loc $
    "projection target is never a pair"
  where
    projectable = \case
      FPair {}  -> True
      FData     -> True
      FTop      -> True
      _function -> False

-- | Emit the level constraints of every application and projection site
-- against a saturated graph.
runEmit :: Supply -> FlowGraph -> Either EALError EmitOut
runEmit supply fg =
  case runRWS (runExceptT emitAll) () supply of
    (Left e, _, _)     -> Left e
    (Right (), _, out) -> Right out
  where
    emitAll = do
      mapM_ (emitApp fg) (fgApps fg)
      mapM_ (emitProj fg) (fgProjs fg)

-- * Constraint solving
--
-- Solving interprets the declarative 'Constraints': it builds the
-- union-find from the union commands, flattens it once (every root lookup
-- after that is pure), and seeds the classes. The classes map is the
-- solver's only mutable state, and it stays local to 'solve'.

type SolveM = ExceptT EALError (State (Map Int ClassInfo))

-- | A solved constraint system: the flattened union-find and the value
-- assigned to each root class.
data Solution = Solution
  { solRoots  :: Map Int Int
  , solValues :: Map Int Int
  }

-- | The solved value of a bang variable (zero if unconstrained).
solvedValue :: Solution -> BVar -> Int
solvedValue (Solution roots vals) (BVar i) =
  fromMaybe 0 $ Map.lookup (Map.findWithDefault i i roots) vals

-- | Interpret the union commands into union-find parent pointers, by size
-- so chains stay logarithmic without incremental compression.
buildUnionFind :: [(BVar, BVar)] -> Map Int Int
buildUnionFind = fst . foldl unite (Map.empty, Map.empty) where
  unite (par, sz) (BVar a, BVar b) =
    let root i = maybe i root (Map.lookup i par)
        ra = root a
        rb = root b
        sa = Map.findWithDefault 1 ra sz
        sb = Map.findWithDefault 1 rb sz
        (small, big) = if sa <= sb then (ra, rb) else (rb, ra)
    in if ra == rb
      then (par, sz)
      else (Map.insert small big par, Map.insert big (sa + sb) sz)

-- | Compress every union-find chain to its root in one pass. The result is
-- defined lazily against itself, so each chain suffix is walked only once
-- (the parent structure is acyclic by construction).
flattenParents :: Map Int Int -> Map Int Int
flattenParents parents = roots where
  roots = fmap (\p -> Map.findWithDefault p p roots) parents

classAt :: Int -> SolveM ClassInfo
classAt r = State.gets (fromMaybe Unrestricted . Map.lookup r)

-- | 'constrainB' for the solver: the class is addressed by its root
-- directly. Returns True if the class changed (the signal 'propagate' uses
-- to detect its fixpoint).
constrainAt :: Int -> ClassInfo -> SolveM Bool
constrainAt r nc = do
  ci <- classAt r
  applyConstraint ci nc >>= \case
    Just rc -> State.modify (Map.insert r rc) >> pure True
    Nothing -> pure False

-- | Solve a constraint system: build and flatten the union-find, merge the
-- seed classes per root, propagate bounds through the sum equations, then
-- search for a satisfying assignment.
solve :: Constraints -> Either EALError Solution
solve cs = do
  let roots = flattenParents (buildUnionFind (cUnions cs))
      rootOf i = Map.findWithDefault i i roots
      eqs = fmap (fmap (rootOf . unBVar)) (cSumEqs cs)
      seed m (BVar i, ci) = let r = rootOf i in case Map.lookup r m of
        Nothing  -> pure (Map.insert r ci m)
        Just old -> (\merged -> Map.insert r merged m)
          <$> mergeClasses old ci
  classes0 <- foldM seed Map.empty (cSeeds cs)
  State.evalState
    (runExceptT (propagate eqs >> Solution roots <$> assignValues eqs))
    classes0

-- | Propagate zero-forcings and lower bounds through the sum equations to a
-- fixpoint.
propagate :: [SumEq Int] -> SolveM ()
propagate eqs = fixpointWithFuel (length eqs * 4 + 64)
  "constraint propagation did not converge" (anyChanges step eqs) where
  step (SumEq lhs rhs blame) = do
    let derived what = let Blame l s = blame in Blame l (what <> ": " <> s)
    ri <- classAt rhs
    c1 <- case ri of
      ForcedZero _ -> anyChanges
        (\l -> constrainAt l $
          ForcedZero (derived "summand of an unboxed total"))
        lhs
      _notZero -> pure False
    lhsIs <- mapM classAt lhs
    c2 <- if all isForcedZero lhsIs
      then constrainAt rhs $ ForcedZero (derived "all summands unboxed")
      else pure False
    let sumLB = sum $ fmap getLowerBound lhsIs
    c3 <- if sumLB > 0
      then constrainAt rhs $
        ForcedLevel sumLB (derived "sum of summand lower bounds")
      else pure False
    ri' <- classAt rhs
    c4 <- case ([l | (l, i) <- zip lhs lhsIs, not $ isForcedZero i], ri') of
      ([lone], ForcedLevel lb _) -> constrainAt lone $
        ForcedLevel lb (derived "only boxable summand")
      _notSingularBoxable -> pure False
    pure $ c1 || c2 || c3 || c4

-- | Find concrete values satisfying every sum equation, starting from the
-- propagated lower bounds and greedily raising free variables.
assignValues :: [SumEq Int] -> SolveM (Map Int Int)
assignValues eqs = do
  classes <- State.get
  let look vals r = fromMaybe 0 $ Map.lookup r vals
      vals0 = fmap getLowerBound classes
      isZeroForced r = maybe False isForcedZero $ Map.lookup r classes
      memberCount :: Map Int Int
      memberCount = Map.fromListWith (+) $
        concatMap (\eq -> [(l, 1) | l <- seLhs eq]) eqs
      adjust (vals, ch) (SumEq lhs rhs blame) =
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
  mapM_ (\(SumEq lhs rhs blame) ->
    when (sum (fmap (look final) lhs) /= look final rhs) .
      throwError . EALSolverGaveUp $
        "assignment verification failed: " <> show blame) eqs
  pure final

-- * Entry points

-- | Walk one top-level frame (the main program, or one lifted body treated
-- as a program over its own env): seed its env with the unknown value,
-- allocate its env path boxes (duplicated paths forced boxed), and
-- generate its constraints.
setupFrame :: AnalysisMode -> String -> Term3Lifting -> WalkM DeferInfo
setupFrame mode what term = do
  let usage = envUsageL term
  ein <- freshNode
  tellTag ein FTop
  entry <- fresh
  bangs <- framePathBangs what usage
  root <- walkNode (WalkCtx ein bangs entry mode) entry [] term
  pure $ DeferInfo ein bangs entry root

-- | Run one walk from a fresh supply: the walked frame, the supply as the
-- later phases must continue it, and everything the walk emitted.
runWalk :: AnalysisMode -> String -> Term3Lifting
        -> Either EALError (DeferInfo, Supply, WalkOut)
runWalk mode what term =
  case runRWS (runExceptT (setupFrame mode what term)) () (Supply 0 0) of
    (Left e, _, _)             -> Left e
    (Right frame, supply, out) -> Right (frame, supply, out)

-- | Run the post-walk phases over one walk's product: saturate the flow
-- graph, emit level constraints against the frozen result, and solve
-- everything both phases produced.
solveWalk :: Supply -> WalkOut -> Either EALError Solution
solveWalk supply out = do
  fg <- flowFixpoint (supNextNode supply) (woFlow out)
  emitted <- runEmit supply fg
  solve Constraints
    { cSeeds  = woSeeds out
    , cUnions = eoUnions emitted
    , cSumEqs = woSumEqs out <> eoSumEqs emitted
    }

-- | Walk one entry point and solve its constraints: the shared spine of
-- the standalone and global passes.
analyze :: AnalysisMode -> String -> Term3Lifting
        -> Either EALError (DeferInfo, WalkOut, Solution)
analyze mode what term = do
  (frame, supply, out) <- runWalk mode what term
  sol <- solveWalk supply out
  pure (frame, out, sol)

-- | Package the standard result fields from a solved system. Per-Defer
-- bangs are reported as the max over the Defer's env path boxes.
finishResult :: Solution -> Reporting -> Maybe BangTrie -> EALResult
finishResult sol rep mainBangs = EALResult
  { ealTopLevelBang = solvedMax (bangVars mainBangs)
  , ealDeferBangs = fmap solvedMax (repDefers rep)
  , ealMaxLevel = maximum (0 : fmap leafDepth (repLeaves rep))
  } where
    solvedMax vs = maximum (0 : fmap (solvedValue sol) vs)
    leafDepth (l, offset) = solvedValue sol l + offset

-- * Lifted inference

-- | Direct DeferRef dependencies of a lifted term.
refsOf :: Term3Lifting -> Set (Digest SHA256)
refsOf (_ :< t) = case t of
  Term3LDeferRef h -> Set.singleton h
  x -> foldMap refsOf x

-- | Infer one lifted body standalone, with summaries for the bodies it
-- references in scope. The verdict localizes intrinsic failures; the solved
-- env bang is a lower bound that the global pass may raise.
summarizeBody :: Map (Digest SHA256) DeferSummary -> FunctionIndex
              -> Term3Lifting -> Either EALError DeferSummary
summarizeBody sums fi body = do
  (frame, out, sol) <- analyze (StandaloneMode sums)
    ("env of lifted body " <> show fi) body
  let r = finishResult sol (woReport out) (diPathBangs frame)
  pure $ DeferSummary fi (ealTopLevelBang r) (ealMaxLevel r)

-- | Infer EAL annotations over a lifted program: each unique Defer body
-- first gets a standalone verdict (which bodies tag, which fail, and why),
-- then main is analyzed globally, walking a fresh copy of the referenced
-- body at every DeferRef, so level flow between bodies is exact and
-- per-site rather than summarized.
inferEALLifted :: DeferMap -> Term3Lifting -> EALLiftedResult
inferEALLifted (DeferMap dm) mainTerm =
  EALLiftedResult bodyResults mainResult where
    bodyResults = Map.mapWithKey summarize dm
    summarize _h (fi, body) = withDeps body $ \sums ->
      summarizeBody sums fi body
    mainResult = withDeps mainTerm (const runMain)
    resultOf d = case Map.lookup d bodyResults of
      Just r  -> r
      Nothing -> Left $ EALDependencyFailed d
    -- The map is a DAG (bodies reference only hashes of subterms), so this
    -- lazy self-reference through bodyResults terminates.
    withDeps :: Term3Lifting
             -> (Map (Digest SHA256) DeferSummary -> Either EALError a)
             -> Either EALError a
    withDeps term k =
      let deps = Set.toList $ refsOf term
      in case [d | d <- deps, Left _ <- [resultOf d]] of
        (d:_) -> Left $ EALDependencyFailed d
        [] -> k $ Map.fromList [(d, s) | d <- deps, Right s <- [resultOf d]]
    -- bodies are walked on demand at their reference sites, so unrelated
    -- failing bodies never taint main (withDeps already covers reachable
    -- ones: a failing dependency fails every body referencing it)
    runMain = do
      (frame, out, sol) <- analyze (GlobalMode dm) "program input" mainTerm
      pure $ finishResult sol (woReport out) (diPathBangs frame)

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
