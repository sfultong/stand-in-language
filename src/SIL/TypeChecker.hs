{-# LANGUAGE DeriveFunctor #-}
module SIL.TypeChecker where

import Control.Monad.State.Lazy
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL
import SIL.RunTime

data IExprA a
  = ZeroA
  | PairA (IExprA a) (IExprA a) a
  | VarA a
  | AppA (IExprA a) (IExprA a) a
  | AnnoA (IExprA a) IExpr
  | GateA (IExprA a)
  | PLeftA (IExprA a) a
  | PRightA (IExprA a) a
  | TraceA (IExprA a)
  | ClosureA (IExprA a) (IExprA a) a
  deriving (Eq, Show, Ord, Functor)

getPartialAnnotation :: IExprA PartialType -> PartialType
getPartialAnnotation (VarA a) = a
getPartialAnnotation (AppA _ _ a) = a
getPartialAnnotation (ClosureA _ _ a) = a
getPartialAnnotation ZeroA = ZeroTypeP
getPartialAnnotation (PairA a b t) = t
getPartialAnnotation (AnnoA x _) = getPartialAnnotation x
getPartialAnnotation (GateA _) = ArrTypeP ZeroTypeP ZeroTypeP
getPartialAnnotation (PLeftA _ a) = a
getPartialAnnotation (PRightA _ a) = a
getPartialAnnotation (TraceA x) = getPartialAnnotation x

unpackPartialType :: IExpr -> Maybe PartialType
unpackPartialType Zero = pure ZeroTypeP
unpackPartialType (Pair a b) = ArrTypeP <$> unpackPartialType a <*> unpackPartialType b
unpackPartialType _ = Nothing

toPartial :: DataType -> PartialType
toPartial ZeroType = ZeroTypeP
toPartial (ArrType a b) = ArrTypeP (toPartial a) (toPartial b)

badType = TypeVariable (-1)

lookupTypeEnv :: [a] -> Int -> Maybe a
lookupTypeEnv env ind = if ind < length env then Just (env !! ind) else Nothing

-- State is closure environment, map of unresolved types, unresolved type id supply
type AnnotateState a = State (PartialType, Map Int PartialType, Int) a

rightPartialType :: PartialType -> PartialType
rightPartialType (PairTypeP _ r) = r
rightPartialType x = error $ concat ["rightPartialType :", show x]

freshVar :: AnnotateState PartialType
freshVar = state $ \(env, typeMap, v) ->
  (TypeVariable v, (PairTypeP (TypeVariable v) env, typeMap, v + 1))

popEnvironment :: AnnotateState ()
popEnvironment = state $ \(env, typeMap, v) -> ((), (rightPartialType env, typeMap, v))

checkOrAssociate :: PartialType -> PartialType -> Set Int -> Map Int PartialType
  -> Maybe (Map Int PartialType)
checkOrAssociate t _ _ _ | t == badType = Nothing
checkOrAssociate _ t _ _ | t == badType = Nothing
-- do nothing for circular (already resolved) references
checkOrAssociate (TypeVariable t) _ resolvedSet _ | Set.member t resolvedSet = Nothing
checkOrAssociate _ (TypeVariable t) resolvedSet _ | Set.member t resolvedSet = Nothing
checkOrAssociate (TypeVariable ta) (TypeVariable tb) resolvedSet typeMap =
  case (Map.lookup ta typeMap, Map.lookup tb typeMap) of
    (Just ra, Just rb) ->
      checkOrAssociate ra rb (Set.insert ta (Set.insert tb resolvedSet)) typeMap
    (Just ra, Nothing) ->
      checkOrAssociate (TypeVariable tb) ra (Set.insert ta resolvedSet) typeMap
    (Nothing, Just rb) ->
      checkOrAssociate (TypeVariable ta) rb (Set.insert tb resolvedSet) typeMap
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
checkOrAssociate a b _ typeMap = if a == b then pure typeMap else Nothing

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = state $ \(env, typeMap, v)
  -> case checkOrAssociate a b Set.empty typeMap of
       Just tm -> ((), (env, tm, v))
       Nothing -> ((), (env, typeMap, v))

-- convert a PartialType to a full type, aborting on circular references
fullyResolve_ :: Set Int -> Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve_ _ _ ZeroTypeP = pure ZeroType
fullyResolve_ resolved typeMap (TypeVariable i) = if Set.member i resolved || i == -1
  then Nothing
  else Map.lookup i typeMap >>= fullyResolve_ (Set.insert i resolved) typeMap
fullyResolve_ resolved typeMap (ArrTypeP a b) =
  ArrType <$> fullyResolve_ resolved typeMap a <*> fullyResolve_ resolved typeMap b
fullyResolve_ resolved typeMap (PairTypeP a b) =
  case (fullyResolve_ resolved typeMap a, fullyResolve_ resolved typeMap b) of
    (Just ZeroType, Just ZeroType) -> pure ZeroType
    (Just na, Just nb) -> pure $ PairType na nb
    _ -> Nothing

fullyResolve :: Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve = fullyResolve_ Set.empty

mostlyResolve_ :: Map Int PartialType -> PartialType -> PartialType
mostlyResolve_ _ ZeroTypeP = ZeroTypeP
mostlyResolve_ typeMap (TypeVariable i) = case Map.lookup i typeMap of
  Just x -> mostlyResolve_ typeMap x
  Nothing -> TypeVariable i
mostlyResolve_ typeMap (ArrTypeP a b) =
  ArrTypeP (mostlyResolve_ typeMap a) (mostlyResolve_ typeMap b)
mostlyResolve_ typeMap (PairTypeP a b) =
  PairTypeP (mostlyResolve_ typeMap a) (mostlyResolve_ typeMap b)

mostlyResolve :: Map Int PartialType -> PartialType -> PartialType
mostlyResolve typeMap x = case fullyResolve typeMap x of
  Just _ -> mostlyResolve_ typeMap x
  _ -> badType

annotate :: IExpr -> AnnotateState (IExprA PartialType)
annotate Zero = pure ZeroA
annotate (Pair a b) = do
  v <- freshVar
  popEnvironment
  na <- annotate a
  nb <- annotate b
  associateVar v (PairTypeP (getPartialAnnotation na) (getPartialAnnotation nb))
  pure $ PairA na nb v
annotate Var = get >>= \(e, _, _) -> pure $ VarA e
annotate (Closure l Zero) = do
  v <- freshVar
  la <- annotate l
  popEnvironment
  pure $ ClosureA la ZeroA (ArrTypeP v (getPartialAnnotation la))
annotate (Closure l x) = fail $ concat ["unexpected closure environment ", show x]
annotate (App g i) = do
  ga <- annotate g
  ia <- annotate i
  case (getPartialAnnotation ga, getPartialAnnotation ia) of
    (ZeroTypeP, _) -> pure $ AppA ga ia badType
    (TypeVariable fv, it) -> do
      (TypeVariable v) <- freshVar
      popEnvironment
      associateVar (TypeVariable fv) (ArrTypeP it (TypeVariable v))
      pure $ AppA ga ia (TypeVariable v)
    (ArrTypeP a b, c) -> do
      associateVar a c
      pure $ AppA ga ia b
    (PairTypeP _ _, _) -> pure $ AppA ga ia badType
annotate (Anno g t) = if fullCheck t ZeroType
  then do
  ga <- annotate g
  let et = pureEval t
  case unpackPartialType et of
    Nothing -> error "bad type signature eval"
    Just evt -> do
      associateVar (getPartialAnnotation ga) evt
      pure $ AnnoA ga et
  else error "annotation problems" -- (`AnnoA` t) <$> annotate g
annotate (Gate x) = GateA <$> annotate x
annotate (PLeft x) = do
  nx <- annotate x
  anno <- case getPartialAnnotation nx of
    ZeroTypeP -> pure ZeroTypeP
    PairTypeP l _ -> pure l
    TypeVariable v -> do
      nl <- freshVar
      nr <- freshVar
      popEnvironment
      popEnvironment
      associateVar (TypeVariable v) (PairTypeP nl nr)
      pure nl
    ArrTypeP _ _ -> pure badType
  pure $ PLeftA nx anno
annotate (PRight x) = do
  nx <- annotate x
  anno <- case getPartialAnnotation nx of
    ZeroTypeP -> pure ZeroTypeP
    PairTypeP _ r -> pure r
    TypeVariable v -> do
      nl <- freshVar
      nr <- freshVar
      popEnvironment
      popEnvironment
      associateVar (TypeVariable v) (PairTypeP nl nr)
      pure nr
    ArrTypeP _ _ -> pure badType
  pure $ PLeftA nx anno
annotate (Trace x) = TraceA <$> annotate x

evalTypeCheck :: IExpr -> IExpr -> Bool
evalTypeCheck g t = fullCheck t ZeroType && case unpackType (pureEval t) of
  Just tt -> fullCheck g tt
  Nothing -> False

checkType_ :: Map Int PartialType -> IExprA PartialType -> DataType -> Bool
checkType_ _ ZeroA ZeroType = True
checkType_ typeMap (PairA l r a) t = case fullyResolve typeMap a of
  Just t2@(PairType lt rt) -> t == t2 && checkType_ typeMap l lt && checkType_ typeMap r rt
  Just ZeroType -> t ==
    ZeroType && checkType_ typeMap l ZeroType && checkType_ typeMap r ZeroType
  _ -> False
checkType_ typeMap (VarA a) t = case fullyResolve typeMap a of
  Nothing -> False
  Just t2 -> t == t2
checkType_ typeMap (AppA g i a) t = fullyResolve typeMap a == Just t &&
  case fullyResolve typeMap (getPartialAnnotation i) of
    Nothing -> False
    Just it -> checkType_ typeMap i it && checkType_ typeMap g (ArrType it t)
checkType_ typeMap (AnnoA g tg) t = packType t == tg && checkType_ typeMap g t
checkType_ typeMap (GateA x) (ArrType ZeroType ZeroType) = checkType_ typeMap x ZeroType
checkType_ typeMap (PLeftA g a) t =
  case (fullyResolve typeMap a, fullyResolve typeMap $ getPartialAnnotation g) of
  (Just t2, Just t3) -> t == t2 && checkType_ typeMap g t3
  _ -> False
checkType_ typeMap (PRightA g a) t =
  case (fullyResolve typeMap a, fullyResolve typeMap $ getPartialAnnotation g) of
  (Just t2, Just t3) -> t == t2 && checkType_ typeMap g t3
  _ -> False
checkType_ typeMap (TraceA g) t = checkType_ typeMap g t
checkType_ typeMap (ClosureA l ZeroA a) ct@(ArrType _ ot) =
  case checkOrAssociate a (toPartial ct) Set.empty typeMap of
    Nothing -> False
    Just t -> checkType_ t l ot
checkType_ _ (ClosureA _ _ _) _ = error "TODO - checkType_ filled closure or non arrow type"
checkType_ _ _ _ = False -- error "unmatched rule"

fullCheck :: IExpr -> DataType -> Bool
fullCheck iexpr t =
  let (iexpra, (_, typeMap, _)) = runState (annotate iexpr) (ZeroTypeP, Map.empty, 0)
      debugT = trace (concat ["iexpra:\n", show iexpra, "\ntypemap:\n", show typeMap])
  in checkType_ typeMap iexpra t

inferType :: IExpr -> PartialType
inferType iexpr =
  let (iexpra, (_, typeMap, _)) = runState (annotate iexpr) (ZeroTypeP, Map.empty, 0)
  in mostlyResolve typeMap $ getPartialAnnotation iexpra
