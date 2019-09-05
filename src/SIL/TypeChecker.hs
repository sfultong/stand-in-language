{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module SIL.TypeChecker where

import Control.Applicative
import Control.Monad.State.Lazy
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace
import Data.Functor.Foldable
import Prelude hiding (Foldable)

import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL

debug :: Bool
debug = True

{-
data ExprTA a
  = ZeroTA
  | PairTA (ExprTA a) (ExprTA a)
  | EnvTA a
  | AbortTA (ExprTA a) a
  | GateTA (ExprTA a) a
  | PLeftTA (ExprTA a) a
  | PRightTA (ExprTA a) a
  | TraceTA (ExprTA a)
  | SetEnvTA (ExprTA a) a
  | DeferTA (ExprTA a)
  deriving (Eq, Show, Ord, Functor)

-}

type ExprPA = ExprA PartialType

-- f must be type preserving, since type annotation is not changed
{-
instance EndoMapper (ExprTA a) where
  endoMap f ZeroTA = f ZeroTA
  endoMap f (PairTA a b) = f $ PairTA (endoMap f a) (endoMap f b)
  endoMap f (EnvTA t) = f $ EnvTA t
  endoMap f (AbortTA x t) = f $ AbortTA (endoMap f x) t
  endoMap f (GateTA x t) = f $ GateTA (endoMap f x) t
  endoMap f (PLeftTA x t) = f $ PLeftTA (endoMap f x) t
  endoMap f (PRightTA x t) = f $ PRightTA (endoMap f x) t
  endoMap f (TraceTA x) = f $ TraceTA (endoMap f x)
  endoMap f (SetEnvTA x t) = f $ SetEnvTA (endoMap f x) t
  endoMap f (DeferTA x) = f $ DeferTA (endoMap f x)

instance MonoidEndoFolder (ExprTA a) where
  monoidFold f ZeroTA = f ZeroTA
  monoidFold f (PairTA a b) = mconcat [f (PairTA a b), monoidFold f a, monoidFold f b]
  monoidFold f (EnvTA t) = f $ EnvTA t
  monoidFold f (AbortTA x t) = mconcat [f (AbortTA x t), monoidFold f x]
  monoidFold f (GateTA x t) = mconcat [f (GateTA x t), monoidFold f x]
  monoidFold f (PLeftTA x t) = mconcat [f (PLeftTA x t), monoidFold f x]
  monoidFold f (PRightTA x t) = mconcat [f (PRightTA x t), monoidFold f x]
  monoidFold f (TraceTA x) = mconcat [f (TraceTA x), monoidFold f x]
  monoidFold f (SetEnvTA x t) = mconcat [f (SetEnvTA x t), monoidFold f x]
  monoidFold f (DeferTA x) = mconcat [f (DeferTA x), monoidFold f x]
-}

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showExpra :: Int -> Int -> ExprPA -> String
showExpra l i e =
  let (ExprAF a pe) = project e
      prettyType = show (PrettyPartialType a)
      showInnerIndented = (show (const "" <$> pe))
        <> "\n" <> indent i <> foldMap (showExpra l (i + 1)) pe
        <> prettyType
  in if length (show e) > l
     then showInnerIndented else show e

{-
showExpra _ _ (ExprAF _ ZeroF) = "ZeroA"
showExpra _ _ (ExprAF a EnvF) = "EnvA " ++ show (PrettyPartialType a)
showExpra l i p@(ExprAF _ (PairF a b)) = if length (show p) > l
  then concat ["PairA\n", indent i, showExpra l (i + 1) a, "\n", indent i, showExpra l (i + 1) b]
  else show p
showExpra l i (ExprAF a (AbortF x)) =
  let lineShow = concat ["AbortA ", show x, "  ", show (PrettyPartialType a)]
  in if length lineShow > l
  then concat ["AbortA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (ExprAF a (GateF x)) =
  let lineShow = concat ["GateA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["GateA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (ExprAF _ (TraceF x)) = concat ["TraceA ", showExpra l i x]
showExpra l i (ExprAF _ (DeferF x)) = concat ["DeferA ", showExpra l i x]
showExpra l i (ExprAF a (PLeftF x)) =
  let lineShow = concat ["PLeftA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["PLeftA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (ExprAF a (PRightF x)) =
  let lineShow = concat ["PRightA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["PRightA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (ExprAF a (SetEnvF x)) =
  let lineShow = concat ["SetEnvA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["SetEnvA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
-}

newtype DebugTypeMap = DebugTypeMap (Map Int PartialType)

instance Show DebugTypeMap where
  show (DebugTypeMap x) = ("typeMap:\n" ++) .
    concat . map ((++ "\n") . show . (\(i,t) -> (i, PrettyPartialType t))) $ Map.toAscList x

data DebugTypeCheck = DebugTypeCheck ExprPA (Map Int PartialType) Int

instance Show DebugTypeCheck where
  show (DebugTypeCheck expra typeMap lineSize) = concat
    [ "iexpra:\n"
    , showExpra lineSize 1 expra
    , "\n\n"
    , show (DebugTypeMap typeMap)
    ]

{-
getPartialAnnotation :: ExprPA -> PartialType
getPartialAnnotation (EnvTA a) = a
getPartialAnnotation (SetEnvTA _ a) = a
getPartialAnnotation (DeferTA x) = case getUnboundType x of
  Nothing -> ArrTypeP AnyType $ getPartialAnnotation x
  Just t -> ArrTypeP t (getPartialAnnotation x)
getPartialAnnotation ZeroTA = DataOnlyTypeP
getPartialAnnotation (PairTA a b) = PairTypeP (getPartialAnnotation a) (getPartialAnnotation b)
getPartialAnnotation (AbortTA _ a) = a
getPartialAnnotation (GateTA _ a) = a
getPartialAnnotation (PLeftTA _ a) = a
getPartialAnnotation (PRightTA _ a) = a
getPartialAnnotation (TraceTA x) = getPartialAnnotation x
-}

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

-- State is closure environment, map of unresolved types, unresolved type id supply
-- TODO maybe remove Maybe TypeChecker and convert to EitherT TypeCheckError ...
type AnnotateState a = State (PartialType, Map Int PartialType, Int, Maybe TypeCheckError) a

withNewEnv :: AnnotateState a -> AnnotateState (PartialType, a)
withNewEnv action = do
  (env, typeMap, v, err) <- get
  put (TypeVariable v, typeMap, v + 1, err)
  result <- action
  state $ \(_, typeMap, v, err) -> ((), (env, typeMap, v, err))
  pure (TypeVariable v, result)

setEnv :: PartialType -> AnnotateState ()
setEnv env = state $ \(_, typeMap, v, err) ->
  ((), (env, typeMap, v, err))

aliasType :: Int -> PartialType -> AnnotateState ()
aliasType k val = state $ \(env, typeMap, v, err) -> ((), (env, Map.insert k val typeMap, v, err))

noteError :: TypeCheckError -> AnnotateState ()
noteError err = state $ \s -> case s of
  (env, typeMap, v, Nothing) -> ((), (env, typeMap, v, Just err))
  _ -> ((), s)

-- | attempt to unify two types, creating new references if applicable
checkOrAssociate :: PartialType -> PartialType -> Set Int -> Map Int PartialType
  -> Either TypeCheckError (Map Int PartialType)
checkOrAssociate (TypeVariable t) _ resolvedSet typeMap | Set.member t resolvedSet
  = Left $ RecursiveType t
checkOrAssociate _ (TypeVariable t) resolvedSet typeMap | Set.member t resolvedSet
  = Left $ RecursiveType t
checkOrAssociate AnyType _ _ tm = pure tm
checkOrAssociate _ AnyType _ tm = pure tm
checkOrAssociate (TypeVariable ta) (TypeVariable tb) resolvedSet typeMap =
  case (Map.lookup ta typeMap, Map.lookup tb typeMap) of
    (Just ra, Just rb) ->
      checkOrAssociate ra rb (Set.insert ta (Set.insert tb resolvedSet)) typeMap
    (Just ra, Nothing) ->
      checkOrAssociate (TypeVariable tb) ra (Set.insert ta resolvedSet) typeMap
    (Nothing, Just rb) ->
      checkOrAssociate (TypeVariable ta) rb (Set.insert tb resolvedSet) typeMap
    (Nothing, Nothing) | ta == tb -> pure typeMap
    (Nothing, Nothing) -> pure $ Map.insert ta (TypeVariable tb) typeMap
checkOrAssociate (TypeVariable t) x resolvedSet typeMap = case Map.lookup t typeMap of
  Nothing -> pure $ Map.insert t x typeMap
  Just rt -> checkOrAssociate x rt (Set.insert t resolvedSet) typeMap
checkOrAssociate x (TypeVariable t) resolvedSet typeMap =
  checkOrAssociate (TypeVariable t) x resolvedSet typeMap
{-
checkOrAssociate (ArrTypeP a b) (ArrTypeP c d) resolvedSet typeMap =
  checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
checkOrAssociate (PairTypeP a b) (PairTypeP c d) resolvedSet typeMap =
  checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
checkOrAssociate (PairTypeP a b) DataOnlyTypeP resolvedSet typeMap =
  checkOrAssociate a DataOnlyTypeP resolvedSet typeMap >>=
  checkOrAssociate b DataOnlyTypeP resolvedSet
checkOrAssociate DataOnlyTypeP p@(PairTypeP _ _) resolvedSet typeMap =
  checkOrAssociate p DataOnlyTypeP resolvedSet typeMap
-}
checkOrAssociate oa@(Fix (SimpleTypeF a)) ob@(Fix (SimpleTypeF b)) resolvedSet typeMap = case (a, b) of
  (ArrTypeF a b, ArrTypeF c d) -> checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
  (PairTypeF a b, PairTypeF c d) -> checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
  (PairTypeF a b, DataOnlyTypeF) -> checkOrAssociate a DataOnlyTypeP resolvedSet typeMap >>=
                                checkOrAssociate b DataOnlyTypeP resolvedSet
  (DataOnlyTypeF, PairTypeF _ _) -> checkOrAssociate ob oa resolvedSet typeMap
  (a, b) -> if a == b then pure typeMap else Left $ InconsistentTypes oa ob
-- checkOrAssociate a b _ typeMap = if a == b then pure typeMap else Left $ InconsistentTypes a b

getTypeMap :: AnnotateState (Map Int PartialType)
getTypeMap = get >>= \(_, tm, _, _) -> pure tm

traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = if debug
  then trace (concat ["associateVar ", show a, " -- ", show b])
  else id

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = state $ \(env, typeMap, v, err)
  -> case (checkOrAssociate a b Set.empty typeMap, err) of
       (Right tm, _) -> traceAssociate a b $ ((), (env, tm, v, err))
       (Left err1, Just err2) | err1 < err2 -> ((), (env, typeMap, v, err))
       (Left te, _) -> traceAssociate a b $ ((), (env, typeMap, v, Just te))

{-
-- convert a PartialType to a full type, aborting on circular references
fullyResolve :: Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve typeMap x = case mostlyResolved of
  Left _ -> Nothing
  Right mr -> filterTypeVars mr
  where
    filterTypeVars DataOnlyTypeP = pure DataOnlyType
    filterTypeVars (TypeVariable _) = Nothing
    filterTypeVars (ArrTypeP a b) = ArrType <$> filterTypeVars a <*> filterTypeVars b
    filterTypeVars (PairTypeP a b) = PairType <$> filterTypeVars a <*> filterTypeVars b
    mostlyResolved = mostlyResolve typeMap x
-}

-- resolve as much of a partial type as possible, aborting on circular references
mostlyResolve_ :: Set Int -> Map Int PartialType -> PartialType
  -> Either TypeCheckError PartialType
{-
mostlyResolve_ _ _ DataOnlyTypeP = pure DataOnlyTypeP
mostlyResolve_ _ _ AnyType = pure AnyType
mostlyResolve_ resolved typeMap (TypeVariable i) =
  case (Set.member i resolved, Map.lookup i typeMap) of
    (True, _) -> Left $ RecursiveType i
    (_, Just x) -> mostlyResolve_ (Set.insert i resolved) typeMap x
    (_, Nothing) -> pure $ TypeVariable i
mostlyResolve_ resolved typeMap (ArrTypeP a b) =
  ArrTypeP <$> mostlyResolve_ resolved typeMap a <*> mostlyResolve_ resolved typeMap b
mostlyResolve_ resolved typeMap (PairTypeP a b) =
  PairTypeP <$> mostlyResolve_ resolved typeMap a <*> mostlyResolve_ resolved typeMap b
-}
mostlyResolve_ resolved typeMap = cata $ \case
  (TypeVariableF i) -> case (Set.member i resolved, Map.lookup i typeMap) of
    (True, _) -> Left $ RecursiveType i
    (_, Just x) -> mostlyResolve_ (Set.insert i resolved) typeMap x
    (_, Nothing) -> pure $ TypeVariable i
  x -> Fix <$> sequence x

mostlyResolve :: Map Int PartialType -> PartialType -> Either TypeCheckError PartialType
mostlyResolve typeMap x = mergePairTypeP <$> mostlyResolve_ Set.empty typeMap x

-- resolve as much as possible of recursive references, without returning error
mostlyResolveRecursive_ :: Set Int -> Map Int PartialType -> PartialType -> PartialType
{-
mostlyResolveRecursive_ _ _ DataOnlyTypeP = DataOnlyTypeP
mostlyResolveRecursive_ _ _ AnyType = AnyType
mostlyResolveRecursive_ resolved typeMap (TypeVariable i) =
  case (Set.member i resolved, Map.lookup i typeMap) of
    (False, Just x) -> mostlyResolveRecursive_ (Set.insert i resolved) typeMap x
    _ -> TypeVariable i
mostlyResolveRecursive_ resolved typeMap (ArrTypeP a b) = ArrTypeP
  (mostlyResolveRecursive_ resolved typeMap a) (mostlyResolveRecursive_ resolved typeMap b)
mostlyResolveRecursive_ resolved typeMap (PairTypeP a b) = PairTypeP
  (mostlyResolveRecursive_ resolved typeMap a) (mostlyResolveRecursive_ resolved typeMap b)
-}
mostlyResolveRecursive_ resolved typeMap = cata $ \case
  (TypeVariableF i) -> case (Set.member i resolved, Map.lookup i typeMap) of
    (False, Just x) -> mostlyResolveRecursive_ (Set.insert i resolved) typeMap x
    _ -> TypeVariable i
  x -> Fix x

mostlyResolveRecursive :: Map Int PartialType -> PartialType -> PartialType
mostlyResolveRecursive = mostlyResolveRecursive_ Set.empty

-- if there's an unbound environment, get its type
{-
getUnboundType :: ExprPA -> Maybe PartialType
getUnboundType ZeroTA = Nothing
getUnboundType (PairTA a b) = getUnboundType a <|> getUnboundType b
getUnboundType (EnvTA a) = pure a
getUnboundType (SetEnvTA x _) = getUnboundType x
getUnboundType (DeferTA _) = Nothing
getUnboundType (AbortTA x _) = getUnboundType x
getUnboundType (GateTA x _) = getUnboundType x
getUnboundType (PLeftTA x _) = getUnboundType x
getUnboundType (PRightTA x _) = getUnboundType x
getUnboundType (TraceTA x) = getUnboundType x
-}

traceFullAnnotation :: PartialType -> AnnotateState ()
traceFullAnnotation pt = if debug
  then do
    (_, tm, _, _) <- get
    trace (concat [ "tracefullannotation "
                  , show (PrettyPartialType <$> mostlyResolve tm pt)
                  , " ("
                  , show (PrettyPartialType $ mostlyResolveRecursive tm pt)
                  , ")"
                  ])  pure ()
  else pure ()

debugAnnotate :: Expr -> AnnotateState ()
debugAnnotate x = if debug
  then do
    (e, tm, varI, err) <- get
    trace ("debugAnnotate " ++ show x ++ " -- " ++ show e) $ pure ()
  else pure ()

simpleEx :: ExprPA
simpleEx = Fix . ExprAF DataOnlyTypeP $ ZeroF

annotate :: Expr -> AnnotateState ExprPA
{-
annotate Zero = debugAnnotate Zero *> pure ZeroTA
annotate (Pair a b) = debugAnnotate (Pair a b) *> (PairTA <$> annotate a <*> annotate b)
annotate Env = (debugAnnotate Env *>) get >>= \(e, _, _, _) -> pure $ EnvTA e
annotate (SetEnv x) = do
  debugAnnotate (SetEnv x)
  nx <- annotate x
  (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
  associateVar (PairTypeP (ArrTypeP it ot) it) $ getPartialAnnotation nx
  traceFullAnnotation (getPartialAnnotation nx)
  pure $ SetEnvTA nx ot
annotate (Defer x) = do
  debugAnnotate (Defer x)
  (_, nx) <- withNewEnv $ annotate x
  pure $ DeferTA nx
-- abort is polymorphic so that it matches any expression
annotate (Abort x) = do
  nx <- annotate x
  (it, _) <- withNewEnv $ pure ()
  associateVar DataOnlyTypeP (getPartialAnnotation nx)
  pure $ AbortTA nx it
annotate (Gate x) = do
  debugAnnotate (Gate x)
  nx <- annotate x
  associateVar DataOnlyTypeP $ getPartialAnnotation nx
  (ra, _) <- withNewEnv $ pure ()
  pure $ GateTA nx (ArrTypeP (PairTypeP ra ra) ra)
annotate (PLeft x) = do
  debugAnnotate (PLeft x)
  nx <- annotate x
  (la, _) <- withNewEnv $ pure ()
  associateVar (PairTypeP la AnyType) (getPartialAnnotation nx)
  pure $ PLeftTA nx la
annotate (PRight x) = do
  debugAnnotate (PRight x)
  nx <- annotate x
  (ra, _) <- withNewEnv $ pure ()
  associateVar (PairTypeP AnyType ra) (getPartialAnnotation nx)
  pure $ PRightTA nx ra
annotate (Trace x) = debugAnnotate (Trace x) *> (TraceTA <$> annotate x)
-}
annotate = cata $ \orig ->
  let oanno t = ((\e a -> Fix $ ExprAF a e) <$> sequence orig <*> pure t)
      getAnno = fmap (eanno . project)
  in case orig of
    ZeroF -> oanno DataOnlyTypeP
    PairF a b -> (liftA2 PairTypeP (getAnno a) (getAnno b)) >>= oanno
    EnvF -> get >>= \(e, _, _, _) -> oanno e
    SetEnvF x -> do
      xt <- getAnno x
      (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
      associateVar (PairTypeP (ArrTypeP it ot) it) xt
      oanno ot
    DeferF x -> do
      --(vt, nx@(ia :< _)) <- withNewEnv x
      (vt, nx@(Fix (ExprAF ia _))) <- withNewEnv x
      pure . Fix $ ExprAF (ArrTypeP vt ia) (DeferF nx)
    AbortF x -> do -- TODO we're changing the semantics of Abort!
      xt <- getAnno x
      (it, _) <- withNewEnv $ pure ()
      associateVar DataOnlyTypeP xt
      oanno it
    GateF x -> do
      xt <- getAnno x
      associateVar DataOnlyTypeP xt
      (ra, _) <- withNewEnv $ pure ()
      oanno $ ArrTypeP (PairTypeP ra ra) ra
    PLeftF x -> do
      xt <- getAnno x
      (la, _) <- withNewEnv $ pure ()
      associateVar (PairTypeP la AnyType) xt
      oanno $ la
    PRightF x -> do
      xt <- getAnno x
      (ra, _) <- withNewEnv $ pure ()
      associateVar (PairTypeP AnyType ra) xt
      oanno $ ra
    TraceF x -> getAnno x >>= oanno

resolveOrAlt :: Map Int PartialType -> PartialType -> Either TypeCheckError DataType
{-
resolveOrAlt_ _ _ DataOnlyTypeP = pure DataOnlyType
resolveOrAlt_ _ _ AnyType = pure DataOnlyType -- just set any remaining type holes to zero
resolveOrAlt_ resolved typeMap (PairTypeP a b) = PairType
  <$> resolveOrAlt_ resolved typeMap a <*> resolveOrAlt_ resolved typeMap b
resolveOrAlt_ resolved typeMap (ArrTypeP a b) = ArrType
  <$> resolveOrAlt_ resolved typeMap a <*> resolveOrAlt_ resolved typeMap b
resolveOrAlt_ resolved typeMap (TypeVariable i) =
  case (Set.member i resolved, Map.lookup i typeMap) of
    (False, Just nt) -> resolveOrAlt_ (Set.insert i resolved) typeMap nt
    (True, _) -> Left $ RecursiveType i
    _ -> Left $ UnboundType i
-}
resolveOrAlt typeMap = cata $ \case
  (SimpleTypeF x) -> Fix <$> sequence x
  AnyTypeF -> pure DataOnlyType -- just set any remaining type holes to zero
  (TypeVariableF i) -> case Map.lookup i typeMap of
    Just nt -> resolveOrAlt typeMap nt
    _ -> Left $ UnboundType i

{-
resolveOrAlt :: Map Int PartialType -> PartialType -> Either TypeCheckError DataType
resolveOrAlt = resolveOrAlt_ Set.empty
-}

-- apply mostlyAnnotate recursively to exprPA
{-
fullyMostlyAnnotate :: Map Int PartialType -> ExprPA -> (Set Int, ExprPA)
fullyMostlyAnnotate _ ZeroTA = (Set.empty, ZeroTA)
fullyMostlyAnnotate tm (PairTA a b) =
  let (sa, na) = fullyMostlyAnnotate tm a
      (sb, nb) = fullyMostlyAnnotate tm b
  in (Set.union sa sb, PairTA na nb)
fullyMostlyAnnotate tm (EnvTA a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, EnvTA a)
  (Right mra) -> (Set.empty, EnvTA mra)
  x -> error $ concat ["fma: ", show x]
fullyMostlyAnnotate tm (SetEnvTA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, SetEnvTA x a)
  (Right mra) -> SetEnvTA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (DeferTA x) = DeferTA <$> fullyMostlyAnnotate tm x
fullyMostlyAnnotate tm (AbortTA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, AbortTA x a)
  (Right mra) -> AbortTA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (GateTA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, GateTA x a)
  (Right mra) -> GateTA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (PLeftTA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, PLeftTA x a)
  (Right mra) -> PLeftTA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (PRightTA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, PRightTA x a)
  (Right mra) -> PRightTA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (TraceTA x) = TraceTA <$> fullyMostlyAnnotate tm x
-}

tcStart :: (PartialType, Map Int PartialType, Int, Maybe TypeCheckError)
tcStart = (TypeVariable 0, Map.empty, 1, Nothing)

partiallyAnnotate :: Expr -> Either TypeCheckError (Map Int PartialType, ExprPA)
partiallyAnnotate iexpr =
  let (iexpra, (_, typeMap, _, err)) = runState (annotate iexpr) tcStart
      debugT = if debug then trace (show $ DebugTypeCheck iexpra typeMap 80) else id
  in debugT $ case err of
    Nothing -> pure (typeMap, iexpra)
    Just et -> Left et

inferType :: Expr -> Either TypeCheckError PartialType
inferType iexpr = partiallyAnnotate iexpr >>= (\(tm, exp) -> mostlyResolve tm . eanno $ project exp)

debugInferType :: Expr -> Either TypeCheckError PartialType
debugInferType iexpr = partiallyAnnotate iexpr >>=
  (\(tm, exp) -> trace (show $ DebugTypeCheck exp tm 80) . mostlyResolve tm . eanno $ project exp)

typeCheck :: PartialType -> Expr -> Maybe TypeCheckError
typeCheck t iexpr =

  let assocAndAnno :: (Map Int PartialType, ExprPA) -> Either TypeCheckError DataType
      assocAndAnno (tm, exp) = -- trace (show $ DebugTypeCheck exp tm 80) $
        case checkOrAssociate t (eanno $ project exp) Set.empty tm of
          Right ntm -> resolveOrAlt ntm (eanno $ project exp)
          Left x -> Left x
        -- error "whatever"

  in case partiallyAnnotate iexpr >>= assocAndAnno of
    Left x -> Just x
    _ -> Nothing

showTraceTypes :: Expr -> String
{-
showTraceTypes iexpr = showE (partiallyAnnotate iexpr >>= (\(tm, expr) -> pure $ monoidFold (showTrace tm) expr))
  where
  showTrace tm (TraceTA x) = show $ (PrettyPartialType <$> (mostlyResolve tm $ getPartialAnnotation x))
  showTrace _ _ = mempty
  showE l@(Left _) = show l
  showE (Right s) = s
-}
showTraceTypes iexpr = showE (partiallyAnnotate iexpr >>= (\(tm, expr) -> pure $ cata (showTrace tm) expr))
  where
    showTrace tm = \case
      (ExprAF a (TraceF s)) -> s <> show (PrettyPartialType <$> mostlyResolve tm a)
      _ -> mempty
    showE l@(Left _) = show l
    showE (Right s) = s
