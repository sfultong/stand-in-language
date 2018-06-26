{-# LANGUAGE DeriveFunctor #-}
module SIL.TypeChecker where

import Control.Applicative
import Control.Monad.State.Lazy
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL

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

type ExprPA = ExprTA PartialType

-- f must be type preserving, since type annotation is not changed
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

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showExpra :: Int -> Int -> ExprPA -> String
showExpra _ _ ZeroTA = "ZeroA"
showExpra _ _ (EnvTA a) = "VarA " ++ show (PrettyPartialType a)
showExpra l i p@(PairTA a b) = if length (show p) > l
  then concat ["PairA\n", indent i, showExpra l (i + 1) a, "\n", indent i, showExpra l (i + 1) b]
  else show p
showExpra l i (AbortTA x a) =
  let lineShow = concat ["AbortA ", show x, "  ", show (PrettyPartialType a)]
  in if length lineShow > l
  then concat ["AbortA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (GateTA x a) =
  let lineShow = concat ["GateA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["GateA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (TraceTA x) = concat ["TraceA ", showExpra l i x]
showExpra l i (DeferTA x) = concat ["DeferA ", showExpra l i x]
showExpra l i (PLeftTA x a) =
  let lineShow = concat ["PLeftA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["PLeftA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (PRightTA x a) =
  let lineShow = concat ["PRightA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["PRightA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (SetEnvTA x a) =
  let lineShow = concat ["SetEnvA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["SetEnvA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow

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

getPartialAnnotation :: ExprPA -> PartialType
getPartialAnnotation (EnvTA a) = a
getPartialAnnotation (SetEnvTA _ a) = a
getPartialAnnotation (DeferTA x) = case getUnboundType x of
  Nothing -> ArrTypeP AnyType $ getPartialAnnotation x
  Just t -> ArrTypeP t (getPartialAnnotation x)
getPartialAnnotation ZeroTA = ZeroTypeP
getPartialAnnotation (PairTA a b) = PairTypeP (getPartialAnnotation a) (getPartialAnnotation b)
getPartialAnnotation (AbortTA _ a) = a
getPartialAnnotation (GateTA _ a) = a
getPartialAnnotation (PLeftTA _ a) = a
getPartialAnnotation (PRightTA _ a) = a
getPartialAnnotation (TraceTA x) = getPartialAnnotation x

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

-- State is closure environment, map of unresolved types, unresolved type id supply
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

checkOrAssociate :: PartialType -> PartialType -> Set Int -> Map Int PartialType
  -> Either TypeCheckError (Map Int PartialType)
-- do nothing for circular (already resolved) references (not type error until later)
checkOrAssociate (TypeVariable t) _ resolvedSet typeMap | Set.member t resolvedSet
  = trace "recursiveType" $ pure typeMap
checkOrAssociate _ (TypeVariable t) resolvedSet typeMap | Set.member t resolvedSet
  = trace "recursiveType" $ pure typeMap
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
checkOrAssociate (ArrTypeP a b) (ArrTypeP c d) resolvedSet typeMap =
  checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
checkOrAssociate (PairTypeP a b) (PairTypeP c d) resolvedSet typeMap =
  checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
checkOrAssociate (PairTypeP a b) ZeroTypeP resolvedSet typeMap =
  checkOrAssociate a ZeroTypeP resolvedSet typeMap >>=
  checkOrAssociate b ZeroTypeP resolvedSet
checkOrAssociate ZeroTypeP p@(PairTypeP _ _) resolvedSet typeMap =
  checkOrAssociate p ZeroTypeP resolvedSet typeMap
checkOrAssociate a b _ typeMap = if a == b then pure typeMap else Left $ InconsistentTypes a b

getTypeMap :: AnnotateState (Map Int PartialType)
getTypeMap = get >>= \(_, tm, _, _) -> pure tm

-- if second argument is subtype of first, do nothing
-- should probably rewrite to be more annotatestate-esque
checkOrAssociateSubtype :: PartialType -> PartialType -> Set Int -> AnnotateState ()
checkOrAssociateSubtype (TypeVariable _) _ _ = pure ()
checkOrAssociateSubtype AnyType _ _ = pure ()
checkOrAssociateSubtype a AnyType _ = noteError $ InconsistentTypes a AnyType
checkOrAssociateSubtype _ (TypeVariable t) resolvedSet | Set.member t resolvedSet = pure ()
checkOrAssociateSubtype x (TypeVariable t) resolvedSet = getTypeMap >>= \tm -> case (Map.lookup t tm, x) of
  (Just tb, _) -> checkOrAssociateSubtype x tb (Set.insert t resolvedSet)
  (_, ZeroTypeP)  -> aliasType t ZeroTypeP
  (_, PairTypeP a b) -> do
    (c, (d, _)) <- withNewEnv . withNewEnv $ pure ()
    checkOrAssociateSubtype (PairTypeP a b) (PairTypeP c d) resolvedSet
    aliasType t (PairTypeP c d)
  (_, ArrTypeP a b) -> do
    (c, (d, _)) <- withNewEnv . withNewEnv $ pure ()
    checkOrAssociateSubtype (ArrTypeP a b) (ArrTypeP c d) resolvedSet
    aliasType t (ArrTypeP c d)
  _ -> fail "shouldn't get here in checkOrAssociateSubtype"
checkOrAssociateSubtype (PairTypeP a b) (PairTypeP c d) resolvedSet =
  checkOrAssociateSubtype a c resolvedSet >>
  checkOrAssociateSubtype b d resolvedSet
checkOrAssociateSubtype ZeroTypeP (PairTypeP a b) resolvedSet =
  checkOrAssociateSubtype ZeroTypeP a resolvedSet >>
  checkOrAssociateSubtype ZeroTypeP b resolvedSet
checkOrAssociateSubtype (PairTypeP a b) ZeroTypeP resolvedSet =
  checkOrAssociateSubtype a ZeroTypeP resolvedSet >>
  checkOrAssociateSubtype b ZeroTypeP resolvedSet
checkOrAssociateSubtype (ArrTypeP a b) (ArrTypeP c d) resolvedSet =
  checkOrAssociateSubtype c a resolvedSet >>
  checkOrAssociateSubtype b d resolvedSet
checkOrAssociateSubtype a b _ = if a == b then pure () else noteError $ InconsistentTypes a b

traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = id --  trace (concat ["associateVar ", show a, " -- ", show b])

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = state $ \(env, typeMap, v, err)
  -> case (checkOrAssociate a b Set.empty typeMap, err) of
       (Right tm, _) -> traceAssociate a b $ ((), (env, tm, v, err))
       (Left err1, Just err2) | err1 < err2 -> ((), (env, typeMap, v, err))
       (Left te, _) -> traceAssociate a b $ ((), (env, typeMap, v, Just te))

associateSubtypeVar :: PartialType -> PartialType -> AnnotateState ()
associateSubtypeVar a b = checkOrAssociateSubtype a b Set.empty

{-
-- convert a PartialType to a full type, aborting on circular references
fullyResolve :: Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve typeMap x = case mostlyResolved of
  Left _ -> Nothing
  Right mr -> filterTypeVars mr
  where
    filterTypeVars ZeroTypeP = pure ZeroType
    filterTypeVars (TypeVariable _) = Nothing
    filterTypeVars (ArrTypeP a b) = ArrType <$> filterTypeVars a <*> filterTypeVars b
    filterTypeVars (PairTypeP a b) = PairType <$> filterTypeVars a <*> filterTypeVars b
    mostlyResolved = mostlyResolve typeMap x
-}

-- resolve as much of a partial type as possible, aborting on circular references
mostlyResolve_ :: Set Int -> Map Int PartialType -> PartialType
  -> Either TypeCheckError PartialType
mostlyResolve_ _ _ ZeroTypeP = pure ZeroTypeP
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

mostlyResolve :: Map Int PartialType -> PartialType -> Either TypeCheckError PartialType
mostlyResolve typeMap x = mergePairTypeP <$> mostlyResolve_ Set.empty typeMap x

-- resolve as much as possible of recursive references, without returning error
mostlyResolveRecursive_ :: Set Int -> Map Int PartialType -> PartialType -> PartialType
mostlyResolveRecursive_ _ _ ZeroTypeP = ZeroTypeP
mostlyResolveRecursive_ _ _ AnyType = AnyType
mostlyResolveRecursive_ resolved typeMap (TypeVariable i) =
  case (Set.member i resolved, Map.lookup i typeMap) of
    (False, Just x) -> mostlyResolveRecursive_ (Set.insert i resolved) typeMap x
    _ -> TypeVariable i
mostlyResolveRecursive_ resolved typeMap (ArrTypeP a b) = ArrTypeP
  (mostlyResolveRecursive_ resolved typeMap a) (mostlyResolveRecursive_ resolved typeMap b)
mostlyResolveRecursive_ resolved typeMap (PairTypeP a b) = PairTypeP
  (mostlyResolveRecursive_ resolved typeMap a) (mostlyResolveRecursive_ resolved typeMap b)

mostlyResolveRecursive :: Map Int PartialType -> PartialType -> PartialType
mostlyResolveRecursive = mostlyResolveRecursive_ Set.empty

-- if there's an unbound environment, get its type
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

traceFullAnnotation :: PartialType -> AnnotateState ()
traceFullAnnotation _ = pure ()
{-
traceFullAnnotation pt = do
  (_, tm, _, _) <- get
  trace (concat [ "tracefullannotation "
                , show (PrettyPartialType <$> mostlyResolve tm pt)
                , " ("
                , show (PrettyPartialType $ mostlyResolveRecursive tm pt)
                , ")"
                ])  pure ()-}

debugAnnotate :: IExpr -> AnnotateState ()
debugAnnotate _ = pure ()
{-
debugAnnotate x = do
  (e, tm, varI, err) <- get
  trace ("debugAnnotate " ++ show x ++ " -- " ++ show e) $ pure ()
-}

annotate :: IExpr -> AnnotateState ExprPA
annotate Zero = debugAnnotate Zero *> pure ZeroTA
annotate (Pair a b) = debugAnnotate (Pair a b) *> (PairTA <$> annotate a <*> annotate b)
annotate Env = (debugAnnotate Env *>) get >>= \(e, _, _, _) -> pure $ EnvTA e
annotate (SetEnv x) = do
  debugAnnotate (SetEnv x)
  nx <- annotate x
  (_, tm, _, _) <- get
  -- for type unification, we want to treat input as a subtype
  -- but to give this expression the proper type annotation, we need to use the exact input type
  -- to derive the output type
  ot <- case mostlyResolveRecursive tm (getPartialAnnotation nx) of
    (PairTypeP (ArrTypeP it ot) sit) -> do
      associateSubtypeVar it sit
      case checkOrAssociate it sit Set.empty tm of
        -- Left _ -> pure badType
        Left _ -> pure ot
        Right ntm -> pure $ mostlyResolveRecursive ntm ot
    (PairTypeP ft sit) -> do
      (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
      associateVar ft (ArrTypeP it ot)
      associateSubtypeVar it sit
      pure ot
    xt -> do
      (it, (ot, (sit, _))) <- withNewEnv . withNewEnv . withNewEnv $ pure ()
      associateVar (PairTypeP (ArrTypeP it ot) sit) xt
      associateSubtypeVar it sit
      pure ot
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
  associateVar ZeroTypeP (getPartialAnnotation nx)
  pure $ AbortTA nx it
annotate (Gate x) = do
  debugAnnotate (Gate x)
  nx <- annotate x
  associateVar ZeroTypeP $ getPartialAnnotation nx
  (ra, _) <- withNewEnv $ pure ()
  pure $ GateTA nx (ArrTypeP (PairTypeP ra ra) ra)
annotate (PLeft x) = do
  debugAnnotate (PLeft x)
  nx <- annotate x
  (la, (ra, _)) <- withNewEnv . withNewEnv $ pure ()
  associateVar (PairTypeP la ra) (getPartialAnnotation nx)
  pure $ PLeftTA nx la
annotate (PRight x) = do
  debugAnnotate (PRight x)
  nx <- annotate x
  (la, (ra, _)) <- withNewEnv . withNewEnv $ pure ()
  associateVar (PairTypeP la ra) (getPartialAnnotation nx)
  pure $ PRightTA nx ra
annotate (Trace x) = debugAnnotate (Trace x) *> (TraceTA <$> annotate x)

resolveOrAlt_ :: Set Int -> Map Int PartialType -> PartialType
  -> Either TypeCheckError DataType
resolveOrAlt_ _ _ ZeroTypeP = pure ZeroType
resolveOrAlt_ resolved typeMap (PairTypeP a b) = PairType
  <$> resolveOrAlt_ resolved typeMap a <*> resolveOrAlt_ resolved typeMap b
resolveOrAlt_ resolved typeMap (ArrTypeP a b) = ArrType
  <$> resolveOrAlt_ resolved typeMap a <*> resolveOrAlt_ resolved typeMap b
resolveOrAlt_ resolved typeMap (TypeVariable i) =
  case (Set.member i resolved, Map.lookup i typeMap) of
    (False, Just nt) -> resolveOrAlt_ (Set.insert i resolved) typeMap nt
    (True, _) -> Left $ RecursiveType i
    _ -> Left $ UnboundType i

resolveOrAlt :: Map Int PartialType -> PartialType -> Either TypeCheckError DataType
resolveOrAlt = resolveOrAlt_ Set.empty

-- apply mostlyAnnotate recursively to exprPA
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

tcStart :: (PartialType, Map Int PartialType, Int, Maybe TypeCheckError)
tcStart = (TypeVariable 0, Map.empty, 1, Nothing)

partiallyAnnotate :: IExpr -> Either TypeCheckError (Map Int PartialType, ExprPA)
partiallyAnnotate iexpr =
  let (iexpra, (_, typeMap, _, err)) = runState (annotate iexpr) tcStart
      debugT = trace (show $ DebugTypeCheck iexpra typeMap 80)
      debug2 x = trace (concat ["iexpra:\n", show iexpra, "\niexpra2:\n", show x, "\ntypemap:\n", show typeMap]) x
  in case err of
    Nothing -> pure (typeMap, iexpra)
    Just et -> Left et

inferType :: IExpr -> Either TypeCheckError PartialType
inferType iexpr = partiallyAnnotate iexpr >>= (\(tm, exp) -> mostlyResolve tm $ getPartialAnnotation exp)

debugInferType :: IExpr -> Either TypeCheckError PartialType
debugInferType iexpr = partiallyAnnotate iexpr >>= (\(tm, exp) -> trace (show $ DebugTypeCheck exp tm 80) . mostlyResolve tm $ getPartialAnnotation exp)

typeCheck :: PartialType -> IExpr -> Maybe TypeCheckError
typeCheck t iexpr =
  let assocAndAnno (tm, exp) =
        case checkOrAssociate t (getPartialAnnotation exp) Set.empty tm of
          Right ntm -> resolveOrAlt ntm (getPartialAnnotation exp)
          Left x -> Left x
  in case partiallyAnnotate iexpr >>= assocAndAnno of
    Left x -> Just x
    _ -> Nothing
