{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module SIL.TypeChecker where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State (State)
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace

import qualified Control.Monad.State as State
import qualified Data.DList as DList
import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL
import PrettyPrint

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

newtype DebugTypeMap = DebugTypeMap (Map Int PartialType)

instance Show DebugTypeMap where
  show (DebugTypeMap x) = ("typeMap:\n" ++) .
    concat . map ((++ "\n") . show . (\(i,t) -> (i, PrettyPartialType t))) $ Map.toAscList x

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  | UnboundEnvironment
  deriving (Eq, Ord, Show)

-- State is set of associations between type variables and types, unresolved type id supply
--type AnnotateState a = State (PartialType, Map Int PartialType, Int, Maybe TypeCheckError) a
type AnnotateState = ExceptT TypeCheckError (State (Set TypeAssociation, Int))

{-
withNewEnv :: AnnotateState a -> AnnotateState (PartialType, a)
withNewEnv action = do
  (env, typeMap, v) <- State.get
  State.put (TypeVariable v, typeMap, v + 1)
  result <- action
  State.modify $ \(_, typeMap, v) -> (env, typeMap, v)
  pure (TypeVariable v, result)
-}

freshTypeVariable :: AnnotateState PartialType
freshTypeVariable = do
  (assocSet, varIndex) <- State.get
  State.put (assocSet, varIndex + 1)
  pure $ TypeVariable varIndex

data TypeAssociation = TypeAssociation Int PartialType
  deriving (Eq, Ord, Show)

makeAssociations :: PartialType -> PartialType -> Either TypeCheckError (Set TypeAssociation)
makeAssociations ta tb = case (ta, tb) of
  (x, y) | x == y -> pure mempty
  (AnyType, _) -> pure mempty
  (_, AnyType) -> pure mempty
  (TypeVariable i, _) -> pure . Set.singleton $ TypeAssociation i tb
  (_, TypeVariable i) -> pure . Set.singleton $ TypeAssociation i ta
  (ArrTypeP a b, ArrTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, PairTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, ZeroTypeP) -> Set.union <$> makeAssociations a ZeroTypeP <*> makeAssociations b ZeroTypeP
  (ZeroTypeP, PairTypeP a b) -> Set.union <$> makeAssociations a ZeroTypeP <*> makeAssociations b ZeroTypeP
  _ -> Left $ InconsistentTypes ta tb

buildTypeMap :: Set TypeAssociation -> Either TypeCheckError (Map Int PartialType)
buildTypeMap assocSet =
  let multiMap = Map.fromListWith DList.append . map (\(TypeAssociation i t) -> (i, DList.singleton t))
        $ Set.toList assocSet
      getKeys = \case
        TypeVariable i -> DList.singleton i
        ArrTypeP a b -> getKeys a <> getKeys b
        PairTypeP a b -> getKeys a <> getKeys b
        _ -> mempty
      isRecursiveType resolvedSet k = case (Set.member k resolvedSet, Map.lookup k multiMap) of
        (True, _) -> Just k
        (_, Nothing) -> Nothing
        (_, Just t) -> foldr (\nk r -> isRecursiveType (Set.insert k resolvedSet) nk <|> r) Nothing
          $ foldMap getKeys t
      debugShowMap tm = debugTrace (concatMap (\(k, v) -> show k <> ": " <> show v <> "\n") $ Map.toAscList tm)
      buildMap assoc typeMap = case Set.minView assoc of
        Nothing -> debugShowMap typeMap $ pure typeMap
        Just (TypeAssociation i t, newAssoc) -> case Map.lookup i typeMap of
          Nothing -> buildMap newAssoc $ Map.insert i t typeMap
          Just t2 -> makeAssociations t t2 >>= (\assoc2 -> buildMap (newAssoc <> assoc2) typeMap)
  -- if any variables result in lookup cycles, fail with RecursiveType
  in case foldr (\t r -> isRecursiveType Set.empty t <|> r) Nothing (Map.keys multiMap) of
    Just k -> Left $ RecursiveType k
    Nothing -> debugTrace (show multiMap) $ buildMap assocSet mempty

fullyResolve :: (Int -> Maybe PartialType) -> PartialType -> PartialType
fullyResolve resolve = convert where
    convert = endoMap endo
    endo = \case
      TypeVariable i -> case resolve i of
        Nothing -> TypeVariable i
        Just t -> convert t -- debugTrace (show t) $ convert t
      x -> x

traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = if debug
  then trace (concat ["associateVar ", show a, " -- ", show b])
  else id

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = liftEither (makeAssociations a b) >>= \set -> State.modify (changeState set) where
  changeState set (oldSet, v) = (oldSet <> set, v)

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

{--
 - reserve 0 -> n*2 TypeVariables for types of FragExprs
 -}
initState :: Term3 -> (Set TypeAssociation, Int)
initState (Term3 termMap) =
  let startVariable = case Set.maxView (Map.keysSet termMap) of
        Nothing -> 0
        Just (FragIndex i, _) -> (i + 1) * 2
  in (Set.empty, startVariable)

-- reserve first 2n type variables for n frags
getFragType :: FragIndex -> PartialType
getFragType (FragIndex i) = ArrTypeP (TypeVariable $ i * 2) (TypeVariable $ i * 2 + 1)

annotate :: Term3 -> AnnotateState ()
annotate (Term3 termMap) =
  let annotate' :: PartialType -> FragExpr BreakExtras -> AnnotateState PartialType
      annotate' env = let recur = annotate' env in \case
        ZeroF -> pure ZeroTypeP
        PairF a b -> PairTypeP <$> recur a <*> recur b
        EnvF -> pure env
        SetEnvF x -> do
          xt <- recur x
          it <- freshTypeVariable
          ot <- freshTypeVariable
          associateVar (PairTypeP (ArrTypeP it ot) it) xt
          pure ot
        DeferF ind -> pure $ getFragType ind
        AbortF -> do
          it <- freshTypeVariable
          pure (ArrTypeP ZeroTypeP (ArrTypeP it it))
        GateF l r -> do
          lt <- recur l
          rt <- recur r
          associateVar lt rt
          pure $ ArrTypeP ZeroTypeP lt
        LeftF x -> do
          xt <- recur x
          la <- freshTypeVariable
          associateVar (PairTypeP la AnyType) xt
          pure la
        RightF x -> do
          xt <- recur x
          ra <- freshTypeVariable
          associateVar (PairTypeP AnyType ra) xt
          pure ra
        TraceF -> pure env
        --(v8 -> ((A,(((v17,v19) -> v7,A),A)) -> v7,v8),Z)
        AuxF UnsizedRecursion -> do -- ugh... just trust this?
          ta <- freshTypeVariable
          tb <- freshTypeVariable
          tc <- freshTypeVariable
          td <- freshTypeVariable
          let it = PairTypeP AnyType (PairTypeP (PairTypeP (ArrTypeP (PairTypeP tc td) ta) AnyType) AnyType)
          pure $ PairTypeP (ArrTypeP tb (PairTypeP (ArrTypeP it ta) tb)) ZeroTypeP
      getInputType fi = let (ArrTypeP it _) = getFragType fi in it
      associateOutType fi ot = let (ArrTypeP _ ot2) = getFragType fi in associateVar ot ot2
  in sequence_ (Map.mapWithKey (\k v -> annotate' (getInputType k) v >>= associateOutType k) termMap)

rootFragType :: PartialType
--rootFragType = PairTypeP (getFragType (FragIndex 0)) ZeroTypeP
rootFragType = TypeVariable 1

partiallyAnnotate :: Term3 -> Either TypeCheckError (Int -> Maybe PartialType)
partiallyAnnotate term@(Term3 termMap) =
  let runner :: State (Set TypeAssociation, Int) (Either TypeCheckError ())
      runner = runExceptT $ annotate term
      (_, (s, _)) = State.runState runner (initState term)
      nakedEnv = \case
        EnvF -> True
        PairF a b -> nakedEnv a || nakedEnv b
        SetEnvF x -> nakedEnv x
        GateF l r -> nakedEnv l || nakedEnv r
        LeftF x -> nakedEnv x
        RightF x -> nakedEnv x
        _ -> False
  in if False -- nakedEnv (rootFrag termMap) -- Not sure if there's value in this. Leave commented out for now
     then Left UnboundEnvironment
     else flip Map.lookup <$> buildTypeMap s

inferType :: Term3 -> Either TypeCheckError PartialType
inferType tm = lookupFully <$> partiallyAnnotate tm where
  lookupFully resolver = fullyResolve resolver rootFragType

typeCheck :: PartialType -> Term3 -> Maybe TypeCheckError
typeCheck t tm@(Term3 typeMap) = convert (partiallyAnnotate tm >>= associate) where
  associate resolver =
    let ty = rootFragType in
      debugTrace ("COMPARING TYPES " <> show (t, fullyResolve resolver ty) <> "\n" <> debugMap ty resolver)
      . traceAgain $ makeAssociations (fullyResolve resolver ty) t
  debugMap ty resolver = showTypeDebugInfo (TypeDebugInfo tm (fullyResolve resolver . getFragType)
                                            (fullyResolve resolver ty))
  traceAgain s = debugTrace ("Resulting thing " <> show s) s
  convert = \case
    Left er -> Just er
    _ -> Nothing

