{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}

-- | An interaction-combinator runtime for 'CompiledExpr'.
--
-- This is the \"abstract algorithm\" flavor of sharing-graph reduction:
-- duplicator nodes carry labels minted fresh at every template
-- instantiation, there are no boxes or brackets at runtime, and dup pairs
-- annihilate only with themselves. That rule set is not sound for arbitrary
-- terms — a duplicator reaching a copy of itself through a term that
-- duplicates its own duplicator computes garbage — and EAL typability
-- ('Telomare.EAL') is the classical sufficient condition under which it is
-- correct. The EAL pass is therefore this runtime's admission certificate:
-- the runtime consumes the verdict and nothing else (no levels, no sharing
-- plan).
--
-- Telomare maps onto interaction agents unusually cleanly because it has no
-- binders: Env is the only variable, so a compiled Defer body is a static
-- net template whose env interface is a single wire (shared through a dup
-- chain when the body uses Env more than once, erased when it doesn't).
-- Every Defer becomes a 'Template' plus an 'ICRef' pointer node; copying a
-- ref is copying a pointer (the code table exists at runtime), and only the
-- instantiated body's wiring is ever duplicated structurally.
--
-- The semantics mirror the reference evaluator ('Telomare.Possible'
-- 'basicStep'\/'stuckStep'\/'abortStep') rule for rule:
--
--   * @SetEnv (Pair (Defer d) e)@ instantiates d's template with env e.
--   * A gate applied to a scrutinee yields one of the reserved selector
--     defers ('doLeft'\/'doRight'); branch selection is then ordinary
--     application of a projection body, and the unselected branch is erased.
--   * Abort applied to Zero yields the reserved identity defer; applied to
--     a pair it becomes an Aborted value that consumers propagate. Aborted
--     values surface as 'AbortRunTime' only if they survive into the
--     result, matching the reference checkError.
--
-- Interaction nets are confluent, so although this runtime fires redexes in
-- worklist order rather than the reference's evaluation order, final
-- results agree on terminating programs; termination itself is what the EAL
-- certificate promises. Templates are not deduplicated (identical bodies
-- compile to separate templates); dedup is an optimization the semantics
-- never observe.
--
-- One discovered subtlety governs the error rules: the reference
-- evaluator, being ordinary lazy Haskell, is effectively call-by-need — a
-- stuck redex sitting in a discarded gate branch is never forced, and
-- compiled sizing machinery really does leave ill-shaped applications in
-- dead branches. The net instead fires every redex it instantiates, so an
-- ill-shaped interaction must produce an 'ICStuckV' poison value rather
-- than abort the run: erasure discards it silently (the net's analogue of
-- an unforced thunk), and only a stuck value surviving into demanded
-- output reports 'ICStuck'. The same speculation means the net eagerly
-- evaluates bounded dead code the reference skips (a cost, not a
-- correctness issue), and dead code that diverges shows up as fuel
-- exhaustion rather than being skipped.
module Telomare.IC where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Except
import Control.Monad.State.Strict (State)
import qualified Control.Monad.State.Strict as State
import Data.Foldable (asum)
import Data.Functor.Foldable (cata, embed, project)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace (trace)
import Telomare.IR.Base (AbortableF (..), BasicExpr, BasicExprF (..),
                         StuckF (..), pattern AbortB, pattern AbortEE,
                         pattern AbortFW, pattern BasicFW, pattern EnvB,
                         pattern GateB, pattern PairB, pattern StuckEE,
                         pattern StuckFW, pattern ZeroB)
import Telomare.IR.Core (CompiledExpr, RunTimeError (..))
import Telomare.Machine (abortInd, deferB, doLeft, doRight)

-- | Temporary debugging switch: trace every interaction and instantiation.
debugIC :: Bool
debugIC = False

dbg :: Monad m => String -> m ()
dbg s = when debugIC $ trace s (pure ())

-- * Net representation

-- | Duplicator label: fresh per instantiated dup, so distinct dups always
-- commute and only the two halves of one dup annihilate.
type Label = Int

type TemplateId = Int

-- | Agent kinds. Slot 0 is always the principal port; value kinds face
-- their consumer with it, consumer kinds face the value they demand.
data ICKind
  = ICRoot             -- ^ 1 port: receives the final result; never interacts
  | ICExt              -- ^ 2 ports: template boundary (0 env in, 1 result
                       --   out); exists only inside templates
  | ICEra              -- ^ 1 port: eraser (affine discard)
  | ICZero             -- ^ 1 port
  | ICGate             -- ^ 1 port
  | ICAbort            -- ^ 1 port
  | ICRef TemplateId   -- ^ 1 port: pointer into the template table, copied
                       --   freely by dups
  | ICPair             -- ^ 3 ports: value, left component, right component
  | ICAborted          -- ^ 2 ports: value, message
  | ICDup Label        -- ^ 3 ports: value to copy, copy, copy
  | ICSetEnv           -- ^ 2 ports: operand (awaits a pair), result
  | ICApply            -- ^ 3 ports: function head, env, result
  | ICScrut            -- ^ 2 ports: gate scrutinee, result
  | ICScrutAbort       -- ^ 2 ports: abort message, result
  | ICLeft             -- ^ 2 ports: projection target, result
  | ICRight            -- ^ 2 ports: projection target, result
  | ICStuckV String    -- ^ 1 port: an ill-shaped interaction's result. The
                       --   reference evaluator is lazy, so a stuck redex in
                       --   a discarded branch is silently skipped there;
                       --   the net fires it eagerly, so stuckness must be a
                       --   value that erasure discards and only demanded
                       --   output reports.
  deriving (Eq, Show)

data Port = Port
  { portNode :: !Int
  , portSlot :: !Int
  } deriving (Eq, Ord, Show)

-- | A node's kind plus, per slot, the port at the far end of its wire.
data Node = Node
  { nodeKind  :: ICKind
  , nodePorts :: IntMap Port
  } deriving Show

-- | One compiled Defer body: its nodes (boundary included), how many local
-- dup labels it mints, and the original defer value for reading refs back.
data Template = Template
  { tplNodes  :: IntMap Node
  , tplExt    :: Int
  , tplLabels :: Int
  , tplSource :: CompiledExpr
  }

data ICError
  -- | A stuck value (data applied as a function, projection of a function,
  -- ...) survived into demanded output. Raised only at readback: a stuck
  -- redex whose result is discarded is not an error, matching the
  -- reference evaluator's laziness.
  = ICStuck String
  -- | The interaction budget ran out; carries interactions performed.
  | ICFuelExhausted Int
  -- | A net invariant was violated: a bug in this module, never a fact
  -- about the program.
  | ICInternal String
  deriving (Eq, Show)

data ICState = ICState
  { icNodes     :: IntMap Node
  , icNextNode  :: !Int
  , icNextLabel :: !Int
  , icActive    :: [(Int, Int)] -- ^ candidate active pairs (may go stale)
  , icEnvQueue  :: [Port]       -- ^ compile-time: env copy ports to consume
  , icTemplates :: IntMap Template
  , icNextTpl   :: !Int
  , icFuel      :: !Int
  , icStats     :: Map String Int
  }

type ICM = ExceptT ICError (State ICState)

emptyState :: Int -> ICState
emptyState fuel = ICState IntMap.empty 0 0 [] [] IntMap.empty 0 fuel Map.empty

-- * Primitive net operations

newNode :: ICKind -> ICM Int
newNode k = do
  n <- State.gets icNextNode
  State.modify' $ \st -> st
    { icNextNode = n + 1
    , icNodes = IntMap.insert n (Node k IntMap.empty) (icNodes st) }
  pure n

nodeAt :: Int -> ICM Node
nodeAt n = State.gets (IntMap.lookup n . icNodes) >>= \case
  Just nd -> pure nd
  Nothing -> throwError . ICInternal $ "no node " <> show n

kindOf :: Int -> ICM ICKind
kindOf = fmap nodeKind . nodeAt

peer :: Port -> ICM Port
peer (Port n s) = do
  nd <- nodeAt n
  case IntMap.lookup s (nodePorts nd) of
    Just q  -> pure q
    Nothing -> throwError . ICInternal $
      "unwired port " <> show n <> "/" <> show s

setHalf :: Port -> Port -> ICM ()
setHalf (Port n s) q = State.modify' $ \st -> st
  { icNodes = IntMap.adjust
      (\nd -> nd { nodePorts = IntMap.insert s q (nodePorts nd) })
      n (icNodes st) }

-- | Wire two ports together. A principal-principal wiring between
-- interacting kinds is enqueued as an active pair.
connect :: Port -> Port -> ICM ()
connect p q = do
  setHalf p q
  setHalf q p
  case (p, q) of
    (Port a 0, Port b 0) -> do
      ka <- kindOf a
      kb <- kindOf b
      when (interactive ka && interactive kb) . State.modify' $ \st ->
        st { icActive = (a, b) : icActive st }
    _notPrincipals -> pure ()
  where interactive = \case
          ICRoot -> False
          ICExt  -> False
          _      -> True

deleteNode :: Int -> ICM ()
deleteNode n = State.modify' $ \st ->
  st { icNodes = IntMap.delete n (icNodes st) }

freshLabel :: ICM Label
freshLabel = do
  l <- State.gets icNextLabel
  State.modify' $ \st -> st { icNextLabel = l + 1 }
  pure l

-- | Count one interaction against the fuel budget and the per-rule stats.
spend :: String -> ICM ()
spend name = do
  f <- State.gets icFuel
  when (f <= 0) $ do
    used <- State.gets (sum . icStats)
    throwError $ ICFuelExhausted used
  State.modify' $ \st -> st
    { icFuel = f - 1
    , icStats = Map.insertWith (+) name 1 (icStats st) }

-- * Compilation

-- | Env occurrences of a body outside nested defers (each nested Defer is
-- closed over its own env and compiles to its own template).
countEnv :: CompiledExpr -> Int
countEnv = cata $ \case
  StuckFW EnvSF         -> 1
  StuckFW (DeferSF _ _) -> 0
  x                     -> sum x

-- | Run a net-building action against a fresh empty net, restoring the
-- current one afterwards; returns the built nodes and their label count.
isolatedNet :: ICM a -> ICM (a, IntMap Node, Int)
isolatedNet act = do
  saved <- State.get
  State.modify' $ \st -> st
    { icNodes = IntMap.empty, icNextNode = 0, icNextLabel = 0
    , icActive = [], icEnvQueue = [] }
  r <- act
  built <- State.get
  State.modify' $ \st -> st
    { icNodes = icNodes saved, icNextNode = icNextNode saved
    , icNextLabel = icNextLabel saved
    , icActive = icActive saved, icEnvQueue = icEnvQueue saved }
  pure (r, icNodes built, icNextLabel built)

-- | Compile one Defer value into a template, keeping the original term for
-- readback. Identical bodies get separate templates (no dedup; harmless).
compileDefer :: CompiledExpr -> ICM TemplateId
compileDefer d = case d of
  StuckEE (DeferSF _ body) -> do
    (ext, nodes, labels) <- isolatedNet (compileBody body)
    tid <- State.gets icNextTpl
    State.modify' $ \st -> st
      { icNextTpl = tid + 1
      , icTemplates =
          IntMap.insert tid (Template nodes ext labels d) (icTemplates st) }
    pure tid
  _notDefer -> throwError $ ICInternal "compileDefer: not a defer value"

-- | Build a body's net: allocate its env sharing, walk the term, and wire
-- the result to the boundary node.
compileBody :: CompiledExpr -> ICM Int
compileBody body = do
  ext <- newNode ICExt
  copies <- envCopies (Port ext 0) (countEnv body)
  State.modify' $ \st -> st { icEnvQueue = copies }
  root <- compileTerm body
  State.gets icEnvQueue >>= \case
    [] -> pure ()
    _  -> throwError $ ICInternal "compileBody: env copies left over"
  connect (Port ext 1) root
  pure ext

-- | The ports producing each env copy, in the order 'compileTerm' consumes
-- them. The incoming env value is delivered at @src@: to an eraser for an
-- unused env, straight through for one use, through a dup chain otherwise.
envCopies :: Port -> Int -> ICM [Port]
envCopies src = \case
  0 -> do
    e <- newNode ICEra
    connect src (Port e 0)
    pure []
  1 -> pure [src]
  n -> do
    d <- newNode . ICDup =<< freshLabel
    connect src (Port d 0)
    rest <- envCopies (Port d 2) (n - 1)
    pure (Port d 1 : rest)

-- | Compile one term, returning the port its value is delivered from.
compileTerm :: CompiledExpr -> ICM Port
compileTerm t = case project t of
  BasicFW ZeroSF -> value ICZero
  BasicFW (PairSF a b) -> do
    p <- newNode ICPair
    connect (Port p 1) =<< compileTerm a
    connect (Port p 2) =<< compileTerm b
    pure (Port p 0)
  StuckFW EnvSF -> State.gets icEnvQueue >>= \case
    (c : rest) -> do
      State.modify' $ \st -> st { icEnvQueue = rest }
      pure c
    [] -> throwError $ ICInternal "compileTerm: env copies exhausted"
  StuckFW (SetEnvSF x) -> consumer ICSetEnv x
  StuckFW (LeftSF x) -> consumer ICLeft x
  StuckFW (RightSF x) -> consumer ICRight x
  StuckFW GateSF -> value ICGate
  d@(StuckFW (DeferSF _ _)) -> value . ICRef =<< compileDefer (embed d)
  AbortFW AbortF -> value ICAbort
  AbortFW (AbortedF m) -> do
    a <- newNode ICAborted
    connect (Port a 1) =<< compileData m
    pure (Port a 0)
  where
    value k = (`Port` 0) <$> newNode k
    consumer k x = do
      n <- newNode k
      connect (Port n 0) =<< compileTerm x
      pure (Port n 1)

compileData :: BasicExpr -> ICM Port
compileData = cata $ \case
  ZeroSF -> (`Port` 0) <$> newNode ICZero
  PairSF ma mb -> do
    p <- newNode ICPair
    connect (Port p 1) =<< ma
    connect (Port p 2) =<< mb
    pure (Port p 0)

-- | Splice a fresh copy of a template into the net: @envSrc@ produces the
-- env value, @resultDst@ awaits the body's value. Dup labels are offset by
-- a fresh base, so every instantiation's dups are distinct from every
-- other's — the discipline the EAL certificate makes sound.
instantiate :: TemplateId -> Port -> Port -> ICM ()
instantiate tid envSrc resultDst = do
  tpl <- State.gets (IntMap.lookup tid . icTemplates) >>= \case
    Just tpl -> pure tpl
    Nothing  -> throwError . ICInternal $ "no template " <> show tid
  base <- State.gets icNextLabel
  dbg $ "instantiate tpl" <> show tid <> " labels@" <> show base
  State.modify' $ \st -> st { icNextLabel = base + tplLabels tpl }
  copies <- fmap IntMap.fromList
    . forM [ (n, nd) | (n, nd) <- IntMap.toList (tplNodes tpl)
                     , n /= tplExt tpl ] $ \(n, nd) ->
      (,) n <$> newNode (relabel base (nodeKind nd))
  let translate (Port n s)
        | n == tplExt tpl = pure $ if s == 0 then envSrc else resultDst
        | otherwise = case IntMap.lookup n copies of
            Just m  -> pure (Port m s)
            Nothing -> throwError $ ICInternal "instantiate: unmapped node"
  -- copy each template wire once (each wire appears from both ends)
  forM_ (IntMap.toList (tplNodes tpl)) $ \(n, nd) ->
    forM_ (IntMap.toList (nodePorts nd)) $ \(s, q) ->
      when (Port n s < q) $ do
        p' <- translate (Port n s)
        q' <- translate q
        connect p' q'
  where
    relabel base = \case
      ICDup l -> ICDup (base + l)
      k       -> k

-- * Reduction

-- | Fire active pairs until quiescence. Entries whose nodes were consumed
-- by earlier interactions are skipped.
reduce :: ICM ()
reduce = State.gets icActive >>= \case
  [] -> pure ()
  ((a, b) : rest) -> do
    State.modify' $ \st -> st { icActive = rest }
    live <- State.gets $ \st ->
      IntMap.member a (icNodes st) && IntMap.member b (icNodes st)
    when live $ do
      pa <- peer (Port a 0)
      pb <- peer (Port b 0)
      when (pa == Port b 0 && pb == Port a 0) $ fire a b
    reduce

fire :: Int -> Int -> ICM ()
fire a b = do
  ka <- kindOf a
  kb <- kindOf b
  dbg $ "fire " <> show a <> ":" <> show ka <> " ~ " <> show b <> ":" <> show kb
  case rule a ka b kb of
    Just act -> act
    Nothing -> case rule b kb a ka of
      Just act -> act
      Nothing -> throwError . ICInternal $
        "no interaction rule for " <> show ka <> " meeting " <> show kb

valueKind :: ICKind -> Bool
valueKind = \case
  ICZero    -> True
  ICPair    -> True
  ICRef _   -> True
  ICGate    -> True
  ICAbort   -> True
  ICAborted -> True
  ICStuckV _ -> True
  _notValue -> False

-- | An ill-shaped interaction: the consumer's result becomes a stuck value
-- and the listed leftover operands are erased. Stuckness must be a value
-- rather than a thrown error because the reference evaluator is lazy — a
-- stuck redex whose result is discarded is no error at all there, and the
-- eager net must agree observationally.
stuckAt :: String -> String -> Port -> [Port] -> ICM ()
stuckAt name msg r extras = do
  spend name
  sv <- newNode (ICStuckV msg)
  connect (Port sv 0) r
  forM_ extras $ \p -> do
    era <- newNode ICEra
    connect (Port era 0) p

-- | The oriented rule table: @rule n nk m mk@ fires the interaction with
-- @n@ in the first role, or Nothing if this orientation has no rule (the
-- caller then tries the flip). Every rule gathers the peers it needs
-- before deleting or rewiring anything.
rule :: Int -> ICKind -> Int -> ICKind -> Maybe (ICM ())
rule n nk m mk = case (nk, mk) of
  -- SetEnv x: x has become a (function, env) pair; go apply the function
  (ICSetEnv, ICPair) -> Just $ do
    spend "setenv-pair"
    f <- peer (Port m 1)
    e <- peer (Port m 2)
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    ap <- newNode ICApply
    connect (Port ap 0) f
    connect (Port ap 1) e
    connect (Port ap 2) r
  (ICSetEnv, ICAborted) -> Just $ passThrough "setenv-aborted" n 1 m
  (ICSetEnv, ICStuckV _) -> Just $ passThrough "setenv-stuck" n 1 m
  (ICSetEnv, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "setenv-nonpair"
      ("SetEnv operand is " <> show mk <> ", not a pair") r []
  -- function dispatch, one rule per applicable head
  (ICApply, ICRef tid) -> Just $ do
    spend "apply-ref"
    e <- peer (Port n 1)
    r <- peer (Port n 2)
    deleteNode n >> deleteNode m
    instantiate tid e r
  (ICApply, ICGate) -> Just $ awaitShape "apply-gate" n m ICScrut
  (ICApply, ICAbort) -> Just $ awaitShape "apply-abort" n m ICScrutAbort
  (ICApply, ICAborted) -> Just $ do
    spend "apply-aborted"
    e <- peer (Port n 1)
    r <- peer (Port n 2)
    deleteNode n
    era <- newNode ICEra
    connect (Port era 0) e
    connect (Port m 0) r
  (ICApply, ICStuckV _) -> Just $ do
    spend "apply-stuck"
    e <- peer (Port n 1)
    r <- peer (Port n 2)
    deleteNode n
    era <- newNode ICEra
    connect (Port era 0) e
    connect (Port m 0) r
  (ICApply, _) | valueKind mk -> Just $ do
    shape <- describeValue 6 m
    e <- peer (Port n 1)
    r <- peer (Port n 2)
    comps <- case mk of
      ICPair -> traverse (peer . Port m) [1, 2]
      _      -> pure []
    deleteNode n >> deleteNode m
    stuckAt "apply-nonfunction"
      ("applied value is " <> show mk <> ", not a function: " <> shape)
      r (e : comps)
  -- gate scrutinee arrived: yield the matching selector defer
  (ICScrut, ICZero) -> Just $ do
    spend "scrut-zero"
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    sel <- newNode (ICRef leftSelTpl)
    connect (Port sel 0) r
  (ICScrut, ICPair) -> Just $ do
    spend "scrut-pair"
    la <- peer (Port m 1)
    rb <- peer (Port m 2)
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    el <- newNode ICEra
    er <- newNode ICEra
    connect (Port el 0) la
    connect (Port er 0) rb
    sel <- newNode (ICRef rightSelTpl)
    connect (Port sel 0) r
  (ICScrut, ICAborted) -> Just $ passThrough "scrut-aborted" n 1 m
  (ICScrut, ICStuckV _) -> Just $ passThrough "scrut-stuck" n 1 m
  (ICScrut, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "scrut-nondata"
      ("gate scrutinee is " <> show mk <> ", not data") r []
  -- abort message arrived: Zero means carry on as the identity
  (ICScrutAbort, ICZero) -> Just $ do
    spend "abort-zero"
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    sel <- newNode (ICRef idSelTpl)
    connect (Port sel 0) r
  (ICScrutAbort, ICPair) -> Just $ do
    spend "abort-pair"
    r <- peer (Port n 1)
    deleteNode n
    ab <- newNode ICAborted
    connect (Port ab 1) (Port m 0) -- the message pair survives underneath
    connect (Port ab 0) r
  (ICScrutAbort, ICAborted) -> Just $ passThrough "abort-aborted" n 1 m
  (ICScrutAbort, ICStuckV _) -> Just $ passThrough "abort-stuck" n 1 m
  (ICScrutAbort, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "abort-nondata"
      ("abort message is " <> show mk <> ", not data") r []
  -- projections
  (ICLeft, ICZero) -> Just $ passThrough "left-zero" n 1 m
  (ICLeft, ICPair) -> Just $ projectPair "left-pair" n m 1 2
  (ICLeft, ICAborted) -> Just $ passThrough "left-aborted" n 1 m
  (ICLeft, ICStuckV _) -> Just $ passThrough "left-stuck" n 1 m
  (ICLeft, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "left-nonpair"
      ("projection target is " <> show mk <> ", not a pair") r []
  (ICRight, ICZero) -> Just $ passThrough "right-zero" n 1 m
  (ICRight, ICPair) -> Just $ projectPair "right-pair" n m 2 1
  (ICRight, ICAborted) -> Just $ passThrough "right-aborted" n 1 m
  (ICRight, ICStuckV _) -> Just $ passThrough "right-stuck" n 1 m
  (ICRight, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "right-nonpair"
      ("projection target is " <> show mk <> ", not a pair") r []
  -- erasure
  (ICEra, ICPair) -> Just $ do
    spend "era-pair"
    la <- peer (Port m 1)
    rb <- peer (Port m 2)
    deleteNode n >> deleteNode m
    el <- newNode ICEra
    er <- newNode ICEra
    connect (Port el 0) la
    connect (Port er 0) rb
  (ICEra, ICAborted) -> Just $ do
    spend "era-aborted"
    msg <- peer (Port m 1)
    deleteNode n >> deleteNode m
    era <- newNode ICEra
    connect (Port era 0) msg
  (ICEra, _) | valueKind mk -> Just $ do
    spend "era-leaf"
    deleteNode n >> deleteNode m
  -- duplication
  (ICDup l, ICPair) -> Just $ do
    spend "dup-pair"
    c1 <- peer (Port n 1)
    c2 <- peer (Port n 2)
    la <- peer (Port m 1)
    rb <- peer (Port m 2)
    deleteNode n >> deleteNode m
    p1 <- newNode ICPair
    p2 <- newNode ICPair
    dl <- newNode (ICDup l)
    dr <- newNode (ICDup l)
    connect (Port dl 0) la
    connect (Port dr 0) rb
    connect (Port p1 1) (Port dl 1)
    connect (Port p1 2) (Port dr 1)
    connect (Port p2 1) (Port dl 2)
    connect (Port p2 2) (Port dr 2)
    connect (Port p1 0) c1
    connect (Port p2 0) c2
  (ICDup l, ICAborted) -> Just $ do
    spend "dup-aborted"
    c1 <- peer (Port n 1)
    c2 <- peer (Port n 2)
    msg <- peer (Port m 1)
    deleteNode n >> deleteNode m
    a1 <- newNode ICAborted
    a2 <- newNode ICAborted
    dm <- newNode (ICDup l)
    connect (Port dm 0) msg
    connect (Port a1 1) (Port dm 1)
    connect (Port a2 1) (Port dm 2)
    connect (Port a1 0) c1
    connect (Port a2 0) c2
  (ICDup l, ICDup l')
    -- the two halves of one dup meet again: the value passed through
    | l == l' -> Just $ do
        spend "dup-annihilate"
        a1 <- peer (Port n 1)
        a2 <- peer (Port n 2)
        b1 <- peer (Port m 1)
        b2 <- peer (Port m 2)
        deleteNode n >> deleteNode m
        connect a1 b1
        connect a2 b2
    -- unrelated dups commute (the standard square)
    | otherwise -> Just $ do
        spend "dup-commute"
        a1 <- peer (Port n 1)
        a2 <- peer (Port n 2)
        b1 <- peer (Port m 1)
        b2 <- peer (Port m 2)
        deleteNode n >> deleteNode m
        m1 <- newNode (ICDup l')
        m2 <- newNode (ICDup l')
        n1 <- newNode (ICDup l)
        n2 <- newNode (ICDup l)
        connect (Port m1 0) a1
        connect (Port m2 0) a2
        connect (Port n1 0) b1
        connect (Port n2 0) b2
        connect (Port m1 1) (Port n1 1)
        connect (Port m1 2) (Port n2 1)
        connect (Port m2 1) (Port n1 2)
        connect (Port m2 2) (Port n2 2)
  (ICDup _, _) | valueKind mk -> Just $ do
    -- leaf values (Zero, refs, gates, aborts) copy by node duplication;
    -- for a ref that is a pointer copy, the code-table payoff
    spend "dup-leaf"
    c1 <- peer (Port n 1)
    c2 <- peer (Port n 2)
    deleteNode n >> deleteNode m
    v1 <- newNode mk
    v2 <- newNode mk
    connect (Port v1 0) c1
    connect (Port v2 0) c2
  _noRule -> Nothing

-- | A bounded structural sketch of the value at a node, for error
-- messages: pairs descend, leaves print their kind, in-flight machinery
-- prints as itself.
describeValue :: Int -> Int -> ICM String
describeValue depth n
  | depth <= 0 = pure "..."
  | otherwise = kindOf n >>= \case
      ICZero -> pure "0"
      ICPair -> do
        a <- peer (Port n 1)
        b <- peer (Port n 2)
        sa <- describeValue (depth - 1) (portNode a)
        sb <- describeValue (depth - 1) (portNode b)
        pure $ "(" <> sa <> "," <> sb <> ")"
      ICRef t  -> pure $ "ref" <> show t
      ICDup l  -> do
        src <- peer (Port n 0)
        s <- describeValue (depth - 1) (portNode src)
        pure $ "dup" <> show l <> "[" <> s <> "]"
      k        -> pure (show k)

-- | Forward the value @m@ to the consumer @n@'s result slot, deleting the
-- consumer: projections of Zero, and Aborted values passing through.
passThrough :: String -> Int -> Int -> Int -> ICM ()
passThrough name n slot m = do
  spend name
  r <- peer (Port n slot)
  deleteNode n
  connect (Port m 0) r

-- | An applied gate or abort must inspect its operand's shape: replace the
-- apply with a shape-awaiting node facing the operand.
awaitShape :: String -> Int -> Int -> ICKind -> ICM ()
awaitShape name n m k = do
  spend name
  e <- peer (Port n 1)
  r <- peer (Port n 2)
  deleteNode n >> deleteNode m
  sc <- newNode k
  connect (Port sc 0) e
  connect (Port sc 1) r

-- | Project one component of a pair to the consumer's result and erase the
-- other.
projectPair :: String -> Int -> Int -> Int -> Int -> ICM ()
projectPair name n m keep drop' = do
  spend name
  kept <- peer (Port m keep)
  dropped <- peer (Port m drop')
  r <- peer (Port n 1)
  deleteNode n >> deleteNode m
  era <- newNode ICEra
  connect (Port era 0) dropped
  connect kept r

-- * Readback

-- | Read a normalized value net back into syntax. Refs read back as their
-- original defer terms, so results compare equal to the reference
-- evaluator's (defer equality is by index).
readback :: Port -> ICM CompiledExpr
readback (Port n _) = kindOf n >>= \case
  ICZero -> pure ZeroB
  ICPair -> PairB <$> (readback =<< peer (Port n 1))
                  <*> (readback =<< peer (Port n 2))
  ICRef tid -> State.gets (IntMap.lookup tid . icTemplates) >>= \case
    Just tpl -> pure (tplSource tpl)
    Nothing  -> throwError . ICInternal $ "readback: no template " <> show tid
  ICGate -> pure GateB
  ICAbort -> pure AbortB
  ICAborted -> AbortEE . AbortedF <$> (readbackData =<< peer (Port n 1))
  -- a stuck value survived into demanded output: only now is it an error
  ICStuckV msg -> throwError $ ICStuck msg
  k -> throwError . ICStuck $ "result contains a non-value: " <> show k

-- | Abort messages are data; anything else truncates to Zero, mirroring
-- the reference evaluator's message truncation.
readbackData :: Port -> ICM BasicExpr
readbackData (Port n _) = kindOf n >>= \case
  ICPair -> PairB <$> (readbackData =<< peer (Port n 1))
                  <*> (readbackData =<< peer (Port n 2))
  ICZero    -> pure ZeroB
  _nonData  -> pure ZeroB

-- * Entry points

-- | Reserved templates for the values the runtime itself mints: the gate
-- selectors and the abort continuation. Registered first, in this order.
leftSelTpl, rightSelTpl, idSelTpl :: TemplateId
leftSelTpl = 0
rightSelTpl = 1
idSelTpl = 2

setupSelectors :: ICM ()
setupSelectors = do
  lt <- compileDefer doLeft
  rt <- compileDefer doRight
  it <- compileDefer (deferB abortInd EnvB)
  unless ([lt, rt, it] == [leftSelTpl, rightSelTpl, idSelTpl])
    . throwError $ ICInternal "selector templates got unexpected ids"

defaultFuel :: Int
defaultFuel = 10 * 1000 * 1000

-- | Evaluate a closed term, also reporting how many interactions each rule
-- fired (the runtime's cost model).
icEvalDetailed :: Int -> CompiledExpr
               -> (Either ICError CompiledExpr, Map String Int)
icEvalDetailed fuel term =
  let (r, st) = State.runState (runExceptT go) (emptyState fuel)
  in (r, icStats st)
  where
    go = do
      when (countEnv term > 0) . throwError $
        ICStuck "unbound Env at top level"
      setupSelectors
      root <- newNode ICRoot
      p <- compileTerm term
      connect (Port root 0) p
      reduce
      readback =<< peer (Port root 0)

-- | Evaluate with the default interaction budget.
icEvalIC :: CompiledExpr -> Either ICError CompiledExpr
icEvalIC = fst . icEvalDetailed defaultFuel

-- | Evaluate under the reference evaluator's contract: an Aborted value
-- surviving anywhere in the result is an 'AbortRunTime' (mirroring the
-- reference checkError); runtime trouble maps onto 'GenericRunTimeError'.
icEval :: CompiledExpr -> Either RunTimeError CompiledExpr
icEval term = case icEvalIC term of
  Left e -> Left $ GenericRunTimeError ("IC runtime: " <> show e) ZeroB
  Right x -> case cata findError x of
    Just msg  -> Left $ AbortRunTime msg
    Nothing   -> Right x
  where
    findError = \case
      AbortFW (AbortedF e) -> Just e
      x                    -> asum x
