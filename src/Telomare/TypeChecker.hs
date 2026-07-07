{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{- HLINT ignore "Use tuple-section" -}

module Telomare.TypeChecker where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens.Plated (transform)
import Control.Monad (foldM)
import Control.Monad.Except
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Bifunctor (second)
import Data.Fix (Fix (..))
import Data.Foldable (fold)
import Data.Functor.Foldable
import Data.List (nub, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import PrettyPrint
import Telomare (AbortableF (..), BasicExprF (..),
                 FunctionIndex (FunctionIndex), LocTag (..), PartialType,
                 PartialTypeF (..), StuckF (..), Term3, Term3F (..),
                 TypeCheckError (..), pattern AbortFW, pattern BasicFW,
                 pattern StuckFW)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

newtype DebugTypeMap = DebugTypeMap (Map Int PartialType)

instance Show DebugTypeMap where
  show (DebugTypeMap x) = ("typeMap:\n" ++) .
    concatMap ((++ "\n") . show . second PrettyPartialType) $ Map.toAscList x

-- State is closure environment, set of associations between type variables and types, unresolved type id supply
type AnnotateState = ExceptT TypeCheckError (State (PartialType, Set TypeAssociation, Int))

withNewEnv :: LocTag -> AnnotateState a -> AnnotateState (PartialType, a)
withNewEnv anno action = do
  (env, typeMap, v) <- State.get
  State.put (embed $ TypeVariable anno v, typeMap, v + 1)
  result <- action
  State.modify $ \(_, typeMap, v) -> (env, typeMap, v)
  pure (embed $ TypeVariable anno v, result)

setEnv :: PartialType -> AnnotateState ()
setEnv env = State.modify $ \(_, typeMap, v) -> (env, typeMap, v)

data TypeAssociation = TypeAssociation Int PartialType
  deriving (Eq, Ord, Show)

makeAssociations :: PartialType -> PartialType -> Either TypeCheckError (Set TypeAssociation)
makeAssociations ta tb = debugTrace ("making type association: " <> show (ta,tb)) $ case (project ta, project tb) of
  (x, y) | x == y -> pure mempty
  (AnyType, _) -> pure mempty
  (_, AnyType) -> pure mempty
  (TypeVariable _ i, _) -> pure . Set.singleton $ TypeAssociation i tb
  (_, TypeVariable _ i) -> pure . Set.singleton $ TypeAssociation i ta
  (ArrTypeP a b, ArrTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, PairTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, ZeroTypeP) -> Set.union <$> makeAssociations a (embed ZeroTypeP) <*> makeAssociations b (embed ZeroTypeP)
  (ZeroTypeP, PairTypeP a b) -> Set.union <$> makeAssociations a (embed ZeroTypeP) <*> makeAssociations b (embed ZeroTypeP)
  _ -> Left $ InconsistentTypes ta tb

-- | Unification state: a union-find forest over type variables plus, for each
-- class root, the structural type (if any) the class has been unified with.
data UnifyState = UnifyState
  { unifyParents :: Map Int Int
  , unifyStructs :: Map Int PartialType
  }

findRoot :: UnifyState -> Int -> Int
findRoot us i = case Map.lookup i (unifyParents us) of
  Nothing -> i
  Just p  -> findRoot us p

typeVars :: PartialType -> [Int]
typeVars = \case
  Fix (TypeVariable _ i) -> [i]
  Fix (ArrTypeP a b)     -> typeVars a <> typeVars b
  Fix (PairTypeP a b)    -> typeVars a <> typeVars b
  _                      -> []

-- | The combined structure of two unified types: concrete structure wins over
-- AnyType wildcards and bare variables.
meetTypes :: PartialType -> PartialType -> PartialType
meetTypes a b = case (project a, project b) of
  (AnyType, _) -> b
  (_, AnyType) -> a
  (TypeVariable _ _, _) -> b
  (_, TypeVariable _ _) -> a
  (PairTypeP c d, PairTypeP e f) -> embed $ PairTypeP (meetTypes c e) (meetTypes d f)
  (ArrTypeP c d, ArrTypeP e f) -> embed $ ArrTypeP (meetTypes c e) (meetTypes d f)
  _ -> a

-- | How a class occurs within a type: not at all; only under pair structure, in
-- which case the type equation collapses to Zero (since Zero ≅ (Zero, Zero) any
-- pure-pair recursive equation is solved by Zero); or under a function arrow,
-- which is a genuinely infinite type (unbounded self-application)
data SelfOccurrence = NoSelfOccurrence | PairSelfOccurrence | ArrSelfOccurrence
  deriving (Eq, Ord, Show)

selfOccurrence :: Int -> PartialType -> UnifyState -> SelfOccurrence
selfOccurrence r t us = fst $ go Set.empty False t where
  go visited underArr ty = case project ty of
    TypeVariable _ j ->
      let rj = findRoot us j
      in if rj == r
         then (if underArr then ArrSelfOccurrence else PairSelfOccurrence, visited)
         else if Set.member (rj, underArr) visited
           then (NoSelfOccurrence, visited)
           else case Map.lookup rj (unifyStructs us) of
             Nothing -> (NoSelfOccurrence, Set.insert (rj, underArr) visited)
             Just s  -> go (Set.insert (rj, underArr) visited) underArr s
    ArrTypeP a b ->
      let (o1, v1) = go visited True a
          (o2, v2) = go v1 True b
      in (max o1 o2, v2)
    PairTypeP a b ->
      let (o1, v1) = go visited underArr a
          (o2, v2) = go v1 underArr b
      in (max o1 o2, v2)
    _ -> (NoSelfOccurrence, visited)

unifyVar :: Int -> PartialType -> UnifyState -> Either TypeCheckError UnifyState
unifyVar i t us =
  let r = findRoot us i
  in case project t of
    AnyType -> pure us
    TypeVariable _ j ->
      let rj = findRoot us j
      in if r == rj then pure us else unionClasses r rj us
    _ -> bindStruct r t us

-- | Force a class (and everything unified with its structure) down to Zero: the
-- resolution of a pure-pair recursive type equation.
collapseToZero :: Int -> [PartialType] -> UnifyState -> Either TypeCheckError UnifyState
collapseToZero r ts us =
  let zero = embed ZeroTypeP
      us' = us { unifyStructs = Map.insert r zero (unifyStructs us) }
  in foldM (\s t -> unifyTypes t zero s) us' ts

unionClasses :: Int -> Int -> UnifyState -> Either TypeCheckError UnifyState
unionClasses r rj us =
  let linked = UnifyState (Map.insert r rj (unifyParents us)) (Map.delete r (unifyStructs us))
  in case (Map.lookup r (unifyStructs us), Map.lookup rj (unifyStructs us)) of
    (Nothing, _) -> pure linked
    (Just s, Nothing) -> pure $ linked { unifyStructs = Map.insert rj s (unifyStructs linked) }
    (Just s1, Just s2) -> case max (selfOccurrence rj s1 linked) (selfOccurrence rj s2 linked) of
      ArrSelfOccurrence -> Left $ RecursiveType rj
      PairSelfOccurrence -> collapseToZero rj [s1, s2] linked
      NoSelfOccurrence ->
        let merged = linked { unifyStructs = Map.insert rj (meetTypes s1 s2) (unifyStructs linked) }
        in unifyTypes s1 s2 merged

bindStruct :: Int -> PartialType -> UnifyState -> Either TypeCheckError UnifyState
bindStruct r t us = case selfOccurrence r t us of
  ArrSelfOccurrence -> Left $ RecursiveType r
  PairSelfOccurrence -> collapseToZero r (t : foldMap pure (Map.lookup r (unifyStructs us))) us
  NoSelfOccurrence -> case Map.lookup r (unifyStructs us) of
    Nothing -> pure $ us { unifyStructs = Map.insert r t (unifyStructs us) }
    Just s -> unifyTypes s t $ us { unifyStructs = Map.insert r (meetTypes s t) (unifyStructs us) }

unifyTypes :: PartialType -> PartialType -> UnifyState -> Either TypeCheckError UnifyState
unifyTypes a b us = case (project a, project b) of
  (x, y) | x == y -> pure us
  (AnyType, _) -> pure us
  (_, AnyType) -> pure us
  (TypeVariable _ i, _) -> unifyVar i b us
  (_, TypeVariable _ j) -> unifyVar j a us
  (ArrTypeP c d, ArrTypeP e f) -> unifyTypes c e us >>= unifyTypes d f
  (PairTypeP c d, PairTypeP e f) -> unifyTypes c e us >>= unifyTypes d f
  (PairTypeP c d, ZeroTypeP) -> unifyTypes c (embed ZeroTypeP) us >>= unifyTypes d (embed ZeroTypeP)
  (ZeroTypeP, PairTypeP c d) -> unifyTypes c (embed ZeroTypeP) us >>= unifyTypes d (embed ZeroTypeP)
  _ -> Left $ InconsistentTypes a b

buildTypeMap :: Set TypeAssociation -> Either TypeCheckError (Map Int PartialType)
buildTypeMap assocSet = do
  us <- foldM (\s (TypeAssociation i t) -> unifyVar i t s) (UnifyState Map.empty Map.empty)
    $ Set.toList assocSet
  let allVars = Set.fromList $ Map.keys (unifyParents us) <> Map.keys (unifyStructs us)
        <> concatMap typeVars (Map.elems (unifyStructs us))
  pure $ Map.fromList [(i, s) | i <- Set.toList allVars, Just s <- [Map.lookup (findRoot us i) (unifyStructs us)]]

fullyResolve :: (Int -> Maybe PartialType) -> PartialType -> Either TypeCheckError PartialType
fullyResolve resolve = ($ Set.empty) . cata f where
  f :: PartialTypeF (Set Int -> Either TypeCheckError PartialType) -> Set Int -> Either TypeCheckError PartialType
  f x alreadySeen = case x of
    t@(TypeVariable anno i) -> case resolve i of
      Nothing -> pure . embed $ TypeVariable anno i
      Just t -> if Set.member i alreadySeen
        then Left $ RecursiveType i
        else cata f t $ Set.insert i alreadySeen
    x -> fmap embed (mapM ($ alreadySeen) x)


traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = if debug
  then trace (concat ["associateVar ", show a, " -- ", show b])
  else id

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = liftEither (makeAssociations a b) >>= \set -> State.modify (changeState set) where
  changeState set (curVar, oldSet, v) = (curVar, oldSet <> set, v)

initState :: Term3 -> (PartialType, Set TypeAssociation, Int)
initState t = (embed $ TypeVariable (GeneratedLoc "TypeChecking initial var" Nothing) 0, Set.empty, 1)

annotate :: Term3 -> AnnotateState PartialType
annotate term =
  let annotate' :: Term3 -> AnnotateState PartialType
      annotate' = \case
        anno :< g -> case g of
          BasicFW ZeroSF -> pure $ embed ZeroTypeP
          -- a defer paired with the environment is a closure; its captured environment
          -- is opaque (existentially typed), otherwise closures over environments
          -- containing functions receiving them would have recursive types
          BasicFW (PairSF a@(_ :< StuckFW (DeferSF _ _)) (_ :< StuckFW EnvSF)) ->
            embed . flip PairTypeP (embed AnyType) <$> annotate' a
          BasicFW (PairSF a b) -> embed <$> (PairTypeP <$> annotate' a <*> annotate' b)
          StuckFW EnvSF -> State.gets (\(t, _, _) -> t)
          StuckFW (SetEnvSF x) -> do
            xt <- annotate' x
            (it, (ot, _)) <- withNewEnv anno . withNewEnv anno $ pure ()
            associateVar (debugTrace ("setenv result " <> show xt <> " -- and out type " <> show ot) . embed $ PairTypeP (embed $ ArrTypeP it ot) it) xt
            pure ot
          StuckFW (DeferSF fi x) -> withNewEnv anno (annotate' x)
                                       >>= \(it, ot) -> pure . embed $ ArrTypeP it ot
          AbortFW AbortF -> do
            (it, _) <- withNewEnv anno $ pure ()
            pure $ embed (ArrTypeP (embed ZeroTypeP) (embed $ ArrTypeP it it))
          StuckFW (GateSF l r) -> do
            lt <- annotate' l
            rt <- annotate' r
            associateVar lt rt
            pure . embed $ ArrTypeP (embed ZeroTypeP) lt
          StuckFW (LeftSF x) -> do
            xt <- annotate' x
            (la, _) <- withNewEnv anno $ pure ()
            associateVar (embed $ PairTypeP la (embed AnyType)) xt
            pure la
          StuckFW (RightSF x) -> do
            xt <- annotate' x
            (ra, _) <- withNewEnv anno $ pure ()
            associateVar (embed $ PairTypeP (embed AnyType) ra) xt
            pure ra
          Term3CheckingWrapper _ _ c -> annotate' c
          -- a sizing placeholder later replaced by a church numeral, so its type is
          -- unconstrained here; sizing checks it separately
          Term3Unsized _ -> pure $ embed AnyType
  in annotate' term

partiallyAnnotate :: Term3 -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
partiallyAnnotate term =
  let runner :: State (PartialType, Set TypeAssociation, Int) (Either TypeCheckError PartialType)
      runner = runExceptT $ annotate term
      (rt, (_, s, _)) = State.runState runner (initState term)
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap s)
  {-
  in do
    tm <- buildTypeMap s
    let resolver = flip Map.lookup tm
    mapM_ (fullyResolve resolver . embed . TypeVariable RuntimeLoc) (Set.toList $ Map.keysSet tm)
      -- >> pure (rt, resolver)
      >> (\t -> (t, resolver)) <$> rt
-}

inferType :: Term3 -> Either TypeCheckError PartialType
inferType tm = partiallyAnnotate tm >>= lookupFully where
  lookupFully (ty, resolver) = fullyResolve resolver ty

typeCheck :: PartialType -> Term3 -> Maybe TypeCheckError
typeCheck t tm = convert (partiallyAnnotate tm >>= associate) where
  associate (ty, resolver) = debugTrace ("typechecking term:\n" <> prettyPrint tm <> "\nCOMPARING TYPES " <> show (t, fullyResolve resolver ty))
     $ fullyResolve resolver ty >>= makeAssociations t
  convert = \case
    Left er -> Just er
    _       -> Nothing
