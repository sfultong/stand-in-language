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
import SIL.RunTime

data IExprA a
  = ZeroA
  | PairA (IExprA a) (IExprA a)
  | VarA a
  | CheckA (IExprA a) (IExprA a)
  | GateA (IExprA a) a
  | PLeftA (IExprA a) a
  | PRightA (IExprA a) a
  | TraceA (IExprA a)
  | SetEnvA (IExprA a) a
  | DeferA (IExprA a)
  | TwiddleA (IExprA a) a
  deriving (Eq, Show, Ord, Functor)

type ExprPA = IExprA PartialType
type ExprFA = IExprA DataType

-- f must be type preserving, since type annotation is not changed
instance EndoMapper (IExprA a) where
  endoMap f ZeroA = f ZeroA
  endoMap f (PairA a b) = f $ PairA (endoMap f a) (endoMap f b)
  endoMap f (VarA t) = f $ VarA t
  endoMap f (CheckA x tc) = f $ CheckA (endoMap f x) (endoMap f tc)
  endoMap f (GateA x t) = f $ GateA (endoMap f x) t
  endoMap f (PLeftA x t) = f $ PLeftA (endoMap f x) t
  endoMap f (PRightA x t) = f $ PRightA (endoMap f x) t
  endoMap f (TraceA x) = f $ TraceA (endoMap f x)
  endoMap f (SetEnvA x t) = f $ SetEnvA (endoMap f x) t
  endoMap f (DeferA x) = f $ DeferA (endoMap f x)
  endoMap f (TwiddleA x t) = f $ TwiddleA (endoMap f x) t

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showExpra :: Int -> Int -> ExprPA -> String
showExpra _ i ZeroA = "ZeroA"
showExpra _ i (VarA a) = "VarA " ++ show (PrettyPartialType a)
showExpra l i p@(PairA a b) = if length (show p) > l
  then concat ["PairA\n", indent i, showExpra l (i + 1) a, "\n", indent i, showExpra l (i + 1) b]
  else show p
showExpra l i k@(CheckA c ct) = if length (show k) > l
  then concat ["CheckA\n", indent i, showExpra l (i + 1) c, "\n", indent i, showExpra l (i + 1) ct]
  else show k
showExpra l i (GateA x a) =
  let lineShow = concat ["GateA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["GateA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (TraceA x) = concat ["TraceA ", showExpra l i x]
showExpra l i (DeferA x) = concat ["DeferA ", showExpra l i x]
showExpra l i (PLeftA x a) =
  let lineShow = concat ["PLeftA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["PLeftA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (PRightA x a) =
  let lineShow = concat ["PRightA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["PRightA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (SetEnvA x a) =
  let lineShow = concat ["SetEnvA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["SetEnvA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
  else lineShow
showExpra l i (TwiddleA x a) =
  let lineShow = concat ["TwiddleA ", show x, "  ", show (PrettyPartialType a)]
  in if length (lineShow) > l
  then concat ["TwiddleA\n", indent i, showExpra l (i + 1) x, "\n", indent i, show (PrettyPartialType a)]
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

fromExprPA :: ExprPA -> IExpr
fromExprPA ZeroA = Zero
fromExprPA (PairA a b) = Pair (fromExprPA a) (fromExprPA b)
fromExprPA (VarA _) = Var
-- we can ignore check because it should run separately elsewhere
fromExprPA (CheckA c _) = fromExprPA c
fromExprPA (GateA x _) = Gate $ fromExprPA x
fromExprPA (PLeftA x _) = PLeft $ fromExprPA x
fromExprPA (PRightA x _) = PRight $ fromExprPA x
fromExprPA (TraceA x) = Trace $ fromExprPA x

getPartialAnnotation :: ExprPA -> PartialType
getPartialAnnotation (VarA a) = a
getPartialAnnotation (SetEnvA _ a) = a
getPartialAnnotation (DeferA x) = case getUnboundType x of
  Nothing -> getPartialAnnotation x
  Just t -> ArrTypeP t (getPartialAnnotation x)
getPartialAnnotation (TwiddleA _ a) = a
getPartialAnnotation ZeroA = ZeroTypeP
getPartialAnnotation (PairA a b) = PairTypeP (getPartialAnnotation a) (getPartialAnnotation b)
getPartialAnnotation (CheckA x _) = getPartialAnnotation x
getPartialAnnotation (GateA _ a) = a
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
toPartial (PairType a b) = PairTypeP (toPartial a) (toPartial b)

badType = TypeVariable (-1)

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

noteError :: TypeCheckError -> AnnotateState ()
noteError err = state $ \s -> case s of
  (env, typeMap, v, Nothing) -> ((), (env, typeMap, v, Just err))
  _ -> ((), s)

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

-- if second argument is subtype of first, do nothing
-- should probably rewrite to be more annotatestate-esque
checkOrAssociateSubtype :: PartialType -> PartialType -> Set Int -> Map Int PartialType
--  -> Either TypeCheckError (Map Int PartialType)
  -> AnnotateState (Map Int PartialType)
checkOrAssociateSubtype (TypeVariable _) _ _ tm = pure tm
checkOrAssociateSubtype _ (TypeVariable t) resolvedSet tm | Set.member t resolvedSet = pure tm
checkOrAssociateSubtype x (TypeVariable t) resolvedSet tm = case Map.lookup t tm of
  Nothing -> case x of
    ZeroTypeP -> pure $ Map.insert t ZeroTypeP tm
    PairTypeP a b -> do
      (c, (d, _)) <- withNewEnv . withNewEnv $ pure ()
      checkOrAssociateSubtype (PairTypeP a b) (PairTypeP c d) resolvedSet $ Map.insert t (PairTypeP c d) tm
    ArrTypeP a b -> do
      (c, (d, _)) <- withNewEnv . withNewEnv $ pure ()
      checkOrAssociateSubtype (ArrTypeP a b) (ArrTypeP c d) resolvedSet $ Map.insert t (ArrTypeP c d) tm
    _ -> fail "shouldn't get here in checkOrAssociateSubtype"
  Just tb -> checkOrAssociateSubtype x tb (Set.insert t resolvedSet) tm
checkOrAssociateSubtype (PairTypeP a b) (PairTypeP c d) resolvedSet typeMap =
  checkOrAssociateSubtype a c resolvedSet typeMap >>= checkOrAssociateSubtype b d resolvedSet
checkOrAssociateSubtype ZeroTypeP (PairTypeP a b) resolvedSet typeMap =
  checkOrAssociateSubtype ZeroTypeP a resolvedSet typeMap >>=
  checkOrAssociateSubtype ZeroTypeP b resolvedSet
checkOrAssociateSubtype (PairTypeP a b) ZeroTypeP resolvedSet typeMap =
  checkOrAssociateSubtype a ZeroTypeP resolvedSet typeMap >>=
  checkOrAssociateSubtype b ZeroTypeP resolvedSet
checkOrAssociateSubtype (ArrTypeP a b) (ArrTypeP c d) resolvedSet typeMap =
  checkOrAssociateSubtype c a resolvedSet typeMap >>=
  checkOrAssociateSubtype b d resolvedSet
checkOrAssociateSubtype a b _ typeMap = if a == b then pure typeMap else do
  noteError $ InconsistentTypes a b
  pure typeMap

traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = id --  trace (concat ["associateVar ", show a, " -- ", show b])

associateVar :: PartialType -> PartialType -> AnnotateState Bool
associateVar a b = state $ \(env, typeMap, v, err)
  -> case (checkOrAssociate a b Set.empty typeMap, err) of
       (Right tm, _) -> traceAssociate a b $ (True, (env, tm, v, err))
       (Left err1, Just err2) | err1 < err2 -> (False, (env, typeMap, v, err))
       (Left te, _) -> (False, (env, typeMap, v, Just te))

associateSubtypeVar :: PartialType -> PartialType -> AnnotateState ()
associateSubtypeVar a b = do
  (_, typeMap, _, _) <- get
  ntm <- checkOrAssociateSubtype a b Set.empty typeMap
  state $ \(env, _, v, err) -> ((), (env, ntm, v, err))

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
getUnboundType ZeroA = Nothing
getUnboundType (PairA a b) = getUnboundType a <|> getUnboundType b
getUnboundType (VarA a) = pure a
getUnboundType (SetEnvA x _) = getUnboundType x
getUnboundType (DeferA _) = Nothing
getUnboundType (TwiddleA x _) = getUnboundType x
getUnboundType (CheckA x _) = getUnboundType x
getUnboundType (GateA x _) = getUnboundType x
getUnboundType (PLeftA x _) = getUnboundType x
getUnboundType (PRightA x _) = getUnboundType x
getUnboundType (TraceA x) = getUnboundType x

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
annotate Zero = debugAnnotate Zero *> pure ZeroA
annotate (Pair a b) = debugAnnotate (Pair a b) *> (PairA <$> annotate a <*> annotate b)
annotate Var = (debugAnnotate Var *>) get >>= \(e, _, _, _) -> pure $ VarA e
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
        Left _ -> pure badType
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
  pure $ SetEnvA nx ot
annotate (Defer x) = do
  debugAnnotate (Defer x)
  (_, nx) <- withNewEnv $ annotate x
  pure $ DeferA nx
annotate (Twiddle x) = do
  debugAnnotate (Twiddle x)
  (aa, (ab, (ac, _))) <- withNewEnv . withNewEnv . withNewEnv $ pure ()
  nx <- annotate x
  associateVar (PairTypeP aa (PairTypeP ab ac)) (getPartialAnnotation nx) >>= \r -> if r
    then pure ()
    else trace ("twiddle associate " ++ show nx) $ pure ()
  debugAnnotate (Twiddle x)
  pure $ TwiddleA nx (PairTypeP ab (PairTypeP aa ac))
annotate (Check g t) = do
  debugAnnotate (Check g t)
  ga <- annotate g
  ta <- annotate t
  associateVar
    (PairTypeP
     (ArrTypeP (getPartialAnnotation ga) ZeroTypeP)
     ZeroTypeP
    )
    (getPartialAnnotation ta)
  pure $ CheckA ga ta
annotate (Gate x) = do
  debugAnnotate (Gate x)
  nx <- annotate x
  associateVar ZeroTypeP $ getPartialAnnotation nx
  (ra, _) <- withNewEnv $ pure ()
  pure $ GateA nx (ArrTypeP (PairTypeP ra ra) ra)
annotate (PLeft x) = do
  debugAnnotate (PLeft x)
  nx <- annotate x
  (la, (ra, _)) <- withNewEnv . withNewEnv $ pure ()
  associateVar (PairTypeP la ra) (getPartialAnnotation nx)
  pure $ PLeftA nx la
annotate (PRight x) = do
  debugAnnotate (PRight x)
  nx <- annotate x
  (la, (ra, _)) <- withNewEnv . withNewEnv $ pure ()
  associateVar (PairTypeP la ra) (getPartialAnnotation nx)
  pure $ PRightA nx ra
annotate (Trace x) = debugAnnotate (Trace x) *> (TraceA <$> annotate x)

-- a fixable recursive type is one where there are no arrows.
-- any undefined typevariables can be filled with ZeroType, and an infinite tree of
-- ZeroTypes is equivalent to ZeroType
isFixableRecursiveType :: Set Int -> Map Int PartialType -> PartialType -> Bool
isFixableRecursiveType _ _ ZeroTypeP = True
isFixableRecursiveType resolved typeMap (PairTypeP a b) =
  isFixableRecursiveType resolved typeMap a && isFixableRecursiveType resolved typeMap b
isFixableRecursiveType resolved _ (TypeVariable i) | Set.member i resolved = True
isFixableRecursiveType resolved typeMap (TypeVariable i) = case Map.lookup i typeMap of
  Nothing -> True
  Just x -> isFixableRecursiveType (Set.insert i resolved) typeMap x
isFixableRecursiveType _ _ _ = False

refsInRecursiveType :: Set Int -> Map Int PartialType -> PartialType -> Set Int
refsInRecursiveType resolved typeMap (PairTypeP a b) = Set.union
  (refsInRecursiveType resolved typeMap a) (refsInRecursiveType resolved typeMap b)
refsInRecursiveType resolved _ (TypeVariable i) | Set.member i resolved = Set.singleton i
refsInRecursiveType resolved typeMap (TypeVariable i) = case Map.lookup i typeMap of
  Nothing -> Set.singleton i
  Just x -> refsInRecursiveType (Set.insert i resolved) typeMap x
refsInRecursiveType _ _ _ = Set.empty

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

fullyAnnotate :: Map Int PartialType -> ExprPA -> Either TypeCheckError ExprFA
fullyAnnotate _ ZeroA = pure ZeroA
fullyAnnotate typeMap (PairA a b) =
  PairA <$> fullyAnnotate typeMap a <*> fullyAnnotate typeMap b
fullyAnnotate typeMap (VarA t) = VarA <$> resolveOrAlt typeMap t
fullyAnnotate typeMap (SetEnvA x a) = SetEnvA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap a
fullyAnnotate typeMap (DeferA x) = DeferA <$> fullyAnnotate typeMap x
fullyAnnotate typeMap (TwiddleA x a) = TwiddleA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap a
fullyAnnotate typeMap (CheckA c ct) =
  CheckA <$> fullyAnnotate typeMap c <*> fullyAnnotate typeMap ct
fullyAnnotate typeMap (GateA x a) = GateA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap a
fullyAnnotate typeMap pl@(PLeftA x t) =
  PLeftA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap t
fullyAnnotate typeMap pr@(PRightA x t) =
  PRightA <$> fullyAnnotate typeMap x <*> resolveOrAlt typeMap t
fullyAnnotate typeMap (TraceA x) = TraceA <$> fullyAnnotate typeMap x

-- apply mostlyAnnotate recursively to exprPA
fullyMostlyAnnotate :: Map Int PartialType -> ExprPA -> (Set Int, ExprPA)
fullyMostlyAnnotate _ ZeroA = (Set.empty, ZeroA)
fullyMostlyAnnotate tm (PairA a b) =
  let (sa, na) = fullyMostlyAnnotate tm a
      (sb, nb) = fullyMostlyAnnotate tm b
  in (Set.union sa sb, PairA na nb)
fullyMostlyAnnotate tm (VarA a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, VarA a)
  (Right mra) -> (Set.empty, VarA mra)
  x -> error $ concat ["fma: ", show x]
fullyMostlyAnnotate tm (SetEnvA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, SetEnvA x a)
  (Right mra) -> SetEnvA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (DeferA x) = DeferA <$> fullyMostlyAnnotate tm x
fullyMostlyAnnotate tm (TwiddleA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, TwiddleA x a)
  (Right mra) -> TwiddleA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (CheckA c t) =
  let (sc, nc) = fullyMostlyAnnotate tm c
      (st, nt) = fullyMostlyAnnotate tm t
  in (Set.union sc st, CheckA nc nt)
fullyMostlyAnnotate tm (GateA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, GateA x a)
  (Right mra) -> GateA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (PLeftA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, PLeftA x a)
  (Right mra) -> PLeftA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (PRightA x a) = case mostlyResolve tm a of
  (Left (RecursiveType i)) -> (Set.singleton i, PRightA x a)
  (Right mra) -> PRightA <$> fullyMostlyAnnotate tm x <*> pure mra
fullyMostlyAnnotate tm (TraceA x) = TraceA <$> fullyMostlyAnnotate tm x

tcStart :: (PartialType, Map Int PartialType, Int, Maybe TypeCheckError)
tcStart = (ZeroTypeP, Map.empty, 0, Nothing)

partiallyAnnotate :: IExpr -> Either TypeCheckError (Map Int PartialType, ExprPA)
partiallyAnnotate iexpr =
  let (iexpra, (_, typeMap, _, err)) = runState (annotate iexpr) tcStart
      debugT = trace (show $ DebugTypeCheck iexpra typeMap 80)
      debug2 x = trace (concat ["iexpra:\n", show iexpra, "\niexpra2:\n", show x, "\ntypemap:\n", show typeMap]) x
      debugT3 pt = trace (show (DebugTypeCheck iexpra typeMap 80) ++ "\nrelevant debug type:\n"
                         ++ show (PrettyPartialType $ mostlyResolveRecursive fixedTypeMap pt))
      (recursiveTypes, fullResolution) = fullyMostlyAnnotate typeMap iexpra
      -- The new type system appears not to generate fixable recursive types. This step might be removable.
      (fixableTypes, unfixableTypes) = Set.partition
        (isFixableRecursiveType Set.empty typeMap . TypeVariable) recursiveTypes
      fixedTypeMap = foldr
        (\i tm -> foldr
                  (\k ntm -> Map.insert k ZeroTypeP ntm)
                  tm
                  $ refsInRecursiveType Set.empty tm (TypeVariable i))
        typeMap fixableTypes
      -- TODO wait, we should remove any checks we can run at compile time
      -- another problem is c (nevermind tc) depending on unbound variables
      {-
      evalCheck (Check c tc) = case pureEval (SetEnv (Pair tc (Pair c Zero))) of
      --evalCheck (Check c tc) = case pureEval (SetEnv (Twiddle (Pair ))) of
        Zero -> Right c
        x -> Left . RefinementFailure $ g2s x-}
      evalCheck x = pure x
      unifiedAndRefined =
        case (null unfixableTypes, eitherEndoMap evalCheck iexpr) of
          (False, _) -> debugT3 (TypeVariable (minimum unfixableTypes)) . Left . RecursiveType $ minimum unfixableTypes
          (_, Right _) -> pure (fixedTypeMap, fullResolution)
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
          Right ntm -> resolveOrAlt ntm (getPartialAnnotation exp)
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
              else trace "makeCheck issue" Zero -- guaranteed to fail
