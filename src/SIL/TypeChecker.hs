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
  | PairA (IExprA a) (IExprA a)
  | VarA a
  | AppA (IExprA a) (IExprA a) a
  | CheckA (IExprA a) (IExprA a)
  | GateA (IExprA a)
  | PLeftA (IExprA a) a
  | PRightA (IExprA a) a
  | TraceA (IExprA a)
  | ClosureA (IExprA a) (IExprA a) a
  deriving (Eq, Show, Ord, Functor)

type ExprPA = IExprA PartialType
type ExprFA = IExprA DataType

-- f must be type preserving, since type annotation is not changed
instance EndoMapper (IExprA a) where
  endoMap f ZeroA = f ZeroA
  endoMap f (PairA a b) = f $ PairA (endoMap f a) (endoMap f b)
  endoMap f (VarA t) = f $ VarA t
  endoMap f (AppA c i t) = f $ AppA (endoMap f c) (endoMap f i) t
  endoMap f (CheckA x tc) = f $ CheckA (endoMap f x) (endoMap f tc)
  endoMap f (GateA x) = f $ GateA (endoMap f x)
  endoMap f (PLeftA x t) = f $ PLeftA (endoMap f x) t
  endoMap f (PRightA x t) = f $ PRightA (endoMap f x) t
  endoMap f (TraceA x) = f $ TraceA (endoMap f x)
  endoMap f (ClosureA c e t) = f $ ClosureA (endoMap f c) (endoMap f e) t

getFullType_ :: ExprFA -> DataType
getFullType_ ZeroA = ZeroType
getFullType_ (PairA a b) = PairType (getFullType_ a) (getFullType_ b)
getFullType_ (VarA t) = t
getFullType_ (AppA _ _ t) = t
getFullType_ (CheckA x _) = getFullType_ x
-- TODO make gate polymorphic?
getFullType_ (GateA x) = ArrType ZeroType ZeroType
getFullType_ (PLeftA _ t) = t
getFullType_ (PRightA _ t) = t
getFullType_ (TraceA x) = getFullType_ x
getFullType_ (ClosureA _ _ t) = t

getFullType :: ExprFA -> DataType
getFullType = mergePairType . getFullType_

fromExprPA :: ExprPA -> IExpr
fromExprPA ZeroA = Zero
fromExprPA (PairA a b) = Pair (fromExprPA a) (fromExprPA b)
fromExprPA (VarA _) = Var
fromExprPA (AppA c i _) = App (fromExprPA c) (fromExprPA i)
-- we can ignore check because it should run separately elsewhere
fromExprPA (CheckA c _) = fromExprPA c
fromExprPA (GateA x) = Gate $ fromExprPA x
fromExprPA (PLeftA x _) = PLeft $ fromExprPA x
fromExprPA (PRightA x _) = PRight $ fromExprPA x
fromExprPA (TraceA x) = Trace $ fromExprPA x
fromExprPA (ClosureA c e _) = Closure (fromExprPA c) (fromExprPA e)

getPartialAnnotation :: ExprPA -> PartialType
getPartialAnnotation (VarA a) = a
getPartialAnnotation (AppA _ _ a) = a
getPartialAnnotation (ClosureA _ _ a) = a
getPartialAnnotation ZeroA = ZeroTypeP
getPartialAnnotation (PairA a b) =
  PairTypeP (getPartialAnnotation a) (getPartialAnnotation b)
getPartialAnnotation (CheckA x _) = getPartialAnnotation x
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

data TypeCheckError
  = UnboundType Int
  | RefinementFailure String
  | InconsistentTypes PartialType PartialType
  | WrongInferredType DataType DataType -- expected, inferred
  | RecursiveType Int
  deriving (Eq, Ord, Show)

-- State is closure environment, map of unresolved types, unresolved type id supply
type AnnotateState a = State (PartialType, Map Int PartialType, Int, Maybe TypeCheckError) a

rightPartialType :: PartialType -> PartialType
rightPartialType (PairTypeP _ r) = r
rightPartialType x = error $ concat ["rightPartialType :", show x]

freshVar :: AnnotateState PartialType
freshVar = state $ \(env, typeMap, v, err) ->
  (TypeVariable v, (PairTypeP (TypeVariable v) env, typeMap, v + 1, err))

popEnvironment :: AnnotateState ()
popEnvironment = state $ \(env, typeMap, v, err) ->
  ((), (rightPartialType env, typeMap, v, err))

checkOrAssociate :: PartialType -> PartialType -> Set Int -> Map Int PartialType
  -> Either TypeCheckError (Map Int PartialType)
checkOrAssociate a b _ _ | a == badType = Left $ InconsistentTypes a b
checkOrAssociate a b _ _ | b == badType = Left $ InconsistentTypes a b
-- do nothing for circular (already resolved) references (not type error until later)
checkOrAssociate (TypeVariable t) _ resolvedSet typeMap | Set.member t resolvedSet = pure
                                                        typeMap
checkOrAssociate _ (TypeVariable t) resolvedSet typeMap | Set.member t resolvedSet = pure
                                                        typeMap
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
checkOrAssociate a b _ typeMap = if a == b then pure typeMap else Left $ InconsistentTypes a b

associateVar :: PartialType -> PartialType -> AnnotateState Bool
associateVar a b = state $ \(env, typeMap, v, err)
  -> case (checkOrAssociate a b Set.empty typeMap, err) of
       (Right tm, _) -> (True, (env, tm, v, err))
       (Left err1, Just err2) | err1 < err2 -> (False, (env, typeMap, v, err))
       (Left te, _) -> (False, (env, typeMap, v, Just te))

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

-- resolve as much of a partial type as possible, aborting on circular references
mostlyResolve_ :: Set Int -> Map Int PartialType -> PartialType
  -> Either TypeCheckError PartialType
mostlyResolve_ _ _ ZeroTypeP = pure ZeroTypeP
mostlyResolve_ resolved typeMap (TypeVariable i) =
  case (Set.member i resolved, Map.lookup i typeMap) of
    (True, _) -> if isRecursivePair Set.empty typeMap (TypeVariable i)
      then pure ZeroTypeP
      else Left $ RecursiveType i
    (_, Just x) -> mostlyResolve_ (Set.insert i resolved) typeMap x
    (_, Nothing) -> pure $ TypeVariable i
mostlyResolve_ resolved typeMap (ArrTypeP a b) =
  ArrTypeP <$> mostlyResolve_ resolved typeMap a <*> mostlyResolve_ resolved typeMap b
mostlyResolve_ resolved typeMap (PairTypeP a b) =
  PairTypeP <$> mostlyResolve_ resolved typeMap a <*> mostlyResolve_ resolved typeMap b

mostlyResolve :: Map Int PartialType -> PartialType -> Either TypeCheckError PartialType
mostlyResolve typeMap x = mergePairTypeP <$> mostlyResolve_ Set.empty typeMap x

annotate :: IExpr -> AnnotateState ExprPA
annotate Zero = pure ZeroA
annotate (Pair a b) = PairA <$> annotate a <*> annotate b
annotate Var = get >>= \(e, _, _, _) -> pure $ VarA e
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
    (TypeVariable fv, it) -> do
      (TypeVariable v) <- freshVar
      popEnvironment
      ta <- associateVar (TypeVariable fv) (ArrTypeP it (TypeVariable v)) >>= \s -> pure $
        if s then TypeVariable v else badType
      pure $ AppA ga ia ta
    (ArrTypeP a b, c) -> do
      ta <- associateVar a c >>= \s -> pure $ if s then b else badType
      pure $ AppA ga ia ta
    _ -> pure $ AppA ga ia badType
annotate (Check g t) = do
  ga <- annotate g
  ta <- annotate t
  associateVar (ArrTypeP (getPartialAnnotation ga) ZeroTypeP) (getPartialAnnotation ta)
  pure $ CheckA ga ta
annotate (Gate x) = do
  xa <- annotate x
  associateVar ZeroTypeP $ getPartialAnnotation xa
  pure $ GateA xa
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
      ta <- associateVar (TypeVariable v) (PairTypeP nl nr) >>= \s -> pure $
        if s then nl else badType
      pure ta
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
      ta <- associateVar (TypeVariable v) (PairTypeP nl nr) >>= \s -> pure $
        if s then nr else badType
      pure ta
    ArrTypeP _ _ -> pure badType
  pure $ PLeftA nx anno
annotate (Trace x) = TraceA <$> annotate x

-- a pair of ZeroType and itself is really just ZeroType
isRecursivePair :: Set Int -> Map Int PartialType -> PartialType -> Bool
isRecursivePair _ _ ZeroTypeP = True
isRecursivePair resolved typeMap (PairTypeP a b) = isRecursivePair resolved typeMap a &&
                                                   isRecursivePair resolved typeMap b
isRecursivePair resolved _ (TypeVariable i) | Set.member i resolved = True
isRecursivePair resolved typeMap (TypeVariable i) = case Map.lookup i typeMap of
  Nothing -> False
  Just x -> isRecursivePair (Set.insert i resolved) typeMap x
isRecursivePair _ _ _ = False

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
    (True, _) -> if isRecursivePair Set.empty typeMap (TypeVariable i)
      then Right ZeroType
      else Left $ RecursiveType i
    _ -> Left $ UnboundType i

resolveOrAlt :: Map Int PartialType -> PartialType -> Either TypeCheckError DataType
resolveOrAlt = resolveOrAlt_ Set.empty

fullyAnnotate :: Map Int PartialType -> ExprPA -> Either TypeCheckError ExprFA
fullyAnnotate _ ZeroA = pure ZeroA
fullyAnnotate typeMap (PairA a b) =
  PairA <$> fullyAnnotate typeMap a <*> fullyAnnotate typeMap b
fullyAnnotate typeMap (VarA t) = VarA <$> resolveOrAlt typeMap t
fullyAnnotate typeMap a@(AppA c i t) =
  AppA <$> fullyAnnotate typeMap c <*> fullyAnnotate typeMap i <*> resolveOrAlt typeMap t
fullyAnnotate typeMap (CheckA c ct) =
  CheckA <$> fullyAnnotate typeMap c <*> fullyAnnotate typeMap ct
fullyAnnotate typeMap (GateA x) = GateA <$> fullyAnnotate typeMap x
fullyAnnotate typeMap pl@(PLeftA x t) =
  PLeftA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap t
fullyAnnotate typeMap pr@(PRightA x t) =
  PRightA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap t
fullyAnnotate typeMap (TraceA x) = TraceA <$> fullyAnnotate typeMap x
fullyAnnotate typeMap l@(ClosureA c i t) = ClosureA
  <$> fullyAnnotate typeMap c <*> fullyAnnotate typeMap i <*> resolveOrAlt typeMap t

-- apply mostlyAnnotate recursively to exprPA
fullyMostlyAnnotate :: Map Int PartialType -> ExprPA -> Either TypeCheckError ExprPA
fullyMostlyAnnotate _ ZeroA = Right ZeroA
fullyMostlyAnnotate tm (PairA a b) =
  PairA <$> fullyMostlyAnnotate tm a <*> fullyMostlyAnnotate tm b
fullyMostlyAnnotate tm (VarA a) = VarA <$> mostlyResolve tm a
fullyMostlyAnnotate tm (AppA c i a) =
  AppA <$> fullyMostlyAnnotate tm c <*> fullyMostlyAnnotate tm i <*> mostlyResolve tm a
fullyMostlyAnnotate tm (CheckA c t) =
  CheckA <$> fullyMostlyAnnotate tm c <*> fullyMostlyAnnotate tm t
fullyMostlyAnnotate tm (GateA x) = GateA <$> fullyMostlyAnnotate tm x
fullyMostlyAnnotate tm (PLeftA x a) =
  PLeftA <$> fullyMostlyAnnotate tm x <*> mostlyResolve tm a
fullyMostlyAnnotate tm (PRightA x a) =
  PRightA <$> fullyMostlyAnnotate tm x <*> mostlyResolve tm a
fullyMostlyAnnotate tm (TraceA x) = TraceA <$> fullyMostlyAnnotate tm x
fullyMostlyAnnotate tm (ClosureA c i a) =
  ClosureA <$> fullyMostlyAnnotate tm c <*> fullyMostlyAnnotate tm i <*> mostlyResolve tm a

tcStart :: (PartialType, Map Int PartialType, Int, Maybe TypeCheckError)
tcStart = (ZeroTypeP, Map.empty, 0, Nothing)

partiallyAnnotate :: IExpr -> Either TypeCheckError (Map Int PartialType, ExprPA)
partiallyAnnotate iexpr =
  let (iexpra, (_, typeMap, _, err)) = runState (annotate iexpr) tcStart
      debugT = trace (concat ["iexpra:\n", show iexpra, "\ntypemap:\n", show typeMap])
      debug2 x = trace (concat ["iexpra:\n", show iexpra, "\niexpra2:\n", show x, "\ntypemap:\n", show typeMap]) x
      fullResolution = fullyMostlyAnnotate typeMap iexpra
      evalCheck (Check c tc) = case pureREval (App tc c) of
        Zero -> Right c
        x -> Left . RefinementFailure $ g2s x
      evalCheck x = pure x
      unifiedAndRefined = case (fullResolution, eitherEndoMap evalCheck iexpr) of
        (Right x, Right _) -> pure (typeMap, x)
        (Left x, _) -> Left x
        (_, Left x) -> Left x
  in case err of
    Nothing -> unifiedAndRefined
    Just et -> Left et

inferType :: IExpr -> Either TypeCheckError PartialType
inferType iexpr = partiallyAnnotate iexpr >>= (\(tm, exp) -> mostlyResolve tm $ getPartialAnnotation exp)

typeCheck :: DataType -> IExpr -> Maybe TypeCheckError
typeCheck t iexpr =
  let assocAndAnno (tm, exp) =
        case checkOrAssociate (toPartial t) (getPartialAnnotation exp) Set.empty tm of
          Right ntm -> fullyAnnotate ntm exp
          Left x -> Left x
  in case partiallyAnnotate iexpr >>= assocAndAnno of
    Left x -> Just x
    _ -> Nothing

-- TODO get rid of this hack
weakCheck :: DataType -> IExpr -> Maybe TypeCheckError
weakCheck t iexpr = typeCheck t iexpr >>= \x -> case x of
  (UnboundType _) -> Nothing
  y -> pure y

-- for legacy type annotations
makeCheck :: IExpr -> IExpr
makeCheck x = if typeCheck ZeroType x == Nothing
              then makeTypeCheckTest . pureEval $ x
              else Zero -- guaranteed to fail
