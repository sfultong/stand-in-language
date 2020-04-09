{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
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
  deriving (Eq, Ord, Show)

-- State is closure environment, set of associations between type variables and types, unresolved type id supply
--type AnnotateState a = State (PartialType, Map Int PartialType, Int, Maybe TypeCheckError) a
type AnnotateStateV a = ExceptT TypeCheckError (State (a, Set (TypeAssociationV a), Int))
type AnnotateState = AnnotateStateV PartialType

withNewEnv :: VariableTyped t => AnnotateStateV t a -> AnnotateStateV t (t, a)
withNewEnv action = do
  (env, typeMap, v) <- State.get
  State.put (typeVariable v, typeMap, v + 1)
  result <- action
  State.modify $ \(_, typeMap, v) -> (env, typeMap, v)
  pure (typeVariable v, result)

data TypeAssociationV a = TypeAssociationV Int a
  deriving (Eq, Ord, Show)

type TypeAssociation = TypeAssociationV PartialType

buildTypeMap :: (Show v, Ord v, VariableTyped v) =>
  Set (TypeAssociationV v) -> (v -> v -> Either TypeCheckError (Set (TypeAssociationV v)))
  -> Either TypeCheckError (Map Int v)
buildTypeMap assocSet assocF =
  let multiMap = Map.fromListWith DList.append . map (\(TypeAssociationV i t) -> (i, DList.singleton t))
        $ Set.toList assocSet
      isRecursiveType resolvedSet k = case (Set.member k resolvedSet, Map.lookup k multiMap) of
        (True, _) -> Just k
        (_, Nothing) -> Nothing
        (_, Just t) -> foldr (\nk r -> isRecursiveType (Set.insert k resolvedSet) nk <|> r) Nothing
          $ foldMap getChildVariableIndices t
      debugShowMap tm = debugTrace (concatMap (\(k, v) -> show k <> ": " <> show v <> "\n") $ Map.toAscList tm)
      buildMap assoc typeMap = case Set.minView assoc of
        Nothing -> debugShowMap typeMap $ pure typeMap
        Just (TypeAssociationV i t, newAssoc) -> case Map.lookup i typeMap of
          Nothing -> buildMap newAssoc $ Map.insert i t typeMap
          Just t2 -> assocF t t2 >>= (\assoc2 -> buildMap (newAssoc <> assoc2) typeMap)
  -- if any variables result in lookup cycles, fail with RecursiveType
  in case foldr (\t r -> isRecursiveType Set.empty t <|> r) Nothing (Map.keys multiMap) of
    Just k -> Left $ RecursiveType k
    Nothing -> debugTrace (show multiMap) $ buildMap assocSet mempty

fullyResolve :: (EndoMapper v, VariableTyped v) => (Int -> Maybe v) -> v -> v
fullyResolve resolve = convert where
  convert = endoMap endo
  endo x = case getVariableIndex x >>= resolve of
    Just t -> convert t
    _ -> x

traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = if debug
  then trace (concat ["associateVar ", show a, " -- ", show b])
  else id

associateVar :: Ord v => TypingSupport v -> v -> v -> AnnotateStateV v ()
associateVar ts a b = liftEither (makeAssociations ts a b) >>= \set -> State.modify (changeState set) where
  changeState set (curVar, oldSet, v) = (curVar, oldSet <> set, v)

{--
 - reserve 0 -> n*2 TypeVariables for types of FragExprs
 -}
initState :: Term3 -> (PartialType, Set TypeAssociation, Int)
initState (Term3 termMap) =
  let startVariable = case Set.maxView (Map.keysSet termMap) of
        Nothing -> 0
        Just (FragIndex i, _) -> (i + 1) * 2
  in (TypeVariable 0, Set.empty, startVariable)

data TypingSupport v =
  TypingSupport { fragInputType :: FragIndex -> v
                , fragOutputType :: FragIndex -> v
                , getType :: FragExpr BreakExtras -> AnnotateStateV v v
                , makeAssociations :: v -> v -> Either TypeCheckError (Set (TypeAssociationV v))
                }

terminationTyping :: TypingSupport PartialType
terminationTyping = TypingSupport
  { fragInputType = \(FragIndex i) -> TypeVariable $ i * 2
  , fragOutputType = \(FragIndex i) -> TypeVariable $ i * 2 + 1
  , getType = let recur = getType terminationTyping
                  associate = associateVar terminationTyping in \case
      ZeroF -> pure ZeroTypeP
      PairF a b -> PairTypeP <$> recur a <*> recur b
      EnvF -> (\(t, _, _) -> t) <$> State.get
      SetEnvF x -> do
        xt <- recur x
        (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
        associate (PairTypeP (ArrTypeP it ot) it) xt
        pure ot
      DeferF ind -> pure $ ArrTypeP (fragInputType terminationTyping ind) (fragOutputType terminationTyping ind)
      AbortF -> do
        (it, _) <- withNewEnv $ pure ()
        pure (ArrTypeP ZeroTypeP (ArrTypeP it it))
      GateF l r -> do
        lt <- recur l
        rt <- recur r
        associate lt rt
        pure $ ArrTypeP ZeroTypeP lt
      LeftF x -> do
        xt <- recur x
        (la, _) <- withNewEnv $ pure ()
        associate (PairTypeP la AnyType) xt
        pure la
      RightF x -> do
        xt <- recur x
        (ra, _) <- withNewEnv $ pure ()
        associate (PairTypeP AnyType ra) xt
        pure ra
      TraceF -> (\(t, _, _) -> t) <$> State.get
      --(v8 -> ((A,(((v17,v19) -> v7,A),A)) -> v7,v8),Z)
      AuxF UnsizedRecursion -> do -- ugh... just trust this?
        (ta, (tb, (tc, (td, _)))) <- withNewEnv . withNewEnv . withNewEnv . withNewEnv $ pure ()
        let it = PairTypeP AnyType (PairTypeP (PairTypeP (ArrTypeP (PairTypeP tc td) ta) AnyType) AnyType)
        pure $ PairTypeP (ArrTypeP tb (PairTypeP (ArrTypeP it ta) tb)) ZeroTypeP
  , makeAssociations = let recur = makeAssociations terminationTyping in \ta tb -> case (ta, tb) of
    (x, y) | x == y -> pure mempty
    (AnyType, _) -> pure mempty
    (_, AnyType) -> pure mempty
    (TypeVariable i, _) -> pure . Set.singleton $ TypeAssociationV i tb
    (_, TypeVariable i) -> pure . Set.singleton $ TypeAssociationV i ta
    (ArrTypeP a b, ArrTypeP c d) -> Set.union <$> recur a c <*> recur b d
    (PairTypeP a b, PairTypeP c d) -> Set.union <$> recur a c <*> recur b d
    (PairTypeP a b, ZeroTypeP) -> Set.union <$> recur a ZeroTypeP <*> recur b ZeroTypeP
    (ZeroTypeP, PairTypeP a b) -> Set.union <$> recur a ZeroTypeP <*> recur b ZeroTypeP
    _ -> Left $ InconsistentTypes ta tb
  }

annotate :: Ord v => TypingSupport v -> Term3 -> AnnotateStateV v v
annotate ts (Term3 termMap) =
  let initInputType fi = let it = fragInputType ts fi in State.modify (\(_, s, i) -> (it, s, i))
      associateOutType fi ot = let ot2 = fragOutputType ts fi in associateVar ts ot ot2
      rootType = initInputType (FragIndex 0) >> getType ts (rootFrag termMap)
  in sequence_ (Map.mapWithKey (\k v -> initInputType k >> getType ts v >>= associateOutType k) termMap) >> rootType

partiallyAnnotate :: Term3 -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
partiallyAnnotate term =
  let runner :: State (PartialType, Set TypeAssociation, Int) (Either TypeCheckError PartialType)
      runner = runExceptT $ annotate terminationTyping term
      (rt, (_, s, _)) = State.runState runner (initState term)
      associate = makeAssociations terminationTyping
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap s associate)

inferType :: Term3 -> Either TypeCheckError PartialType
inferType tm = lookupFully <$> partiallyAnnotate tm where
  lookupFully (ty, resolver) = fullyResolve resolver ty

typeCheck :: PartialType -> Term3 -> Maybe TypeCheckError
typeCheck t tm@(Term3 typeMap) = convert (partiallyAnnotate tm >>= associate) where
  associate (ty, resolver) = debugTrace ("COMPARING TYPES " <> show (t, fullyResolve resolver ty) <> "\n" <> debugMap ty resolver)
    . traceAgain $ makeAssociations terminationTyping (fullyResolve resolver ty) t
  getFragType fi = ArrTypeP (fragInputType terminationTyping fi) (fragOutputType terminationTyping fi)
  debugMap ty resolver = showTypeDebugInfo (TypeDebugInfo tm (fullyResolve resolver . getFragType)
                                            (fullyResolve resolver ty))
  traceAgain s = debugTrace ("Resulting thing " <> show s) s
  convert = \case
    Left er -> Just er
    _ -> Nothing

