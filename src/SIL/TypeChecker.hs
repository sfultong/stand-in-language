{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module SIL.TypeChecker where

import Control.Applicative
import Control.Monad (foldM)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State (State)
import Data.Foldable
import Data.Functor.Compose
import Data.Map (Map)
import Data.Monoid (Any(..))
import Data.Set (Set)
import Debug.Trace
import GHC.Exts (fromList)

import qualified Control.Monad.State as State
import qualified Data.DList as DList
import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL
import SIL.Possible
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

data AnnotateData v a
  = AnnotateData { envType :: v
                 , varIndex :: Int
                 , associations :: Set (TypeAssociationV v)
                 , miscAnnotation :: a
                 }

-- State is closure environment, set of associations between type variables and types, unresolved type id supply
--type AnnotateState a = State (PartialType, Map Int PartialType, Int, Maybe TypeCheckError) a
-- type AnnotateStateV a = ExceptT TypeCheckError (State (a, Set (TypeAssociationV a), Int))
type AnnotateStateV a = ExceptT TypeCheckError (State (AnnotateData a ()))
type AnnotateState = AnnotateStateV PartialType

withNewEnv :: VariableTyped t => AnnotateStateV t a -> AnnotateStateV t (t, a)
withNewEnv action = do
  (AnnotateData env v assocs _) <- State.get
  State.put (AnnotateData (typeVariable v) (v + 1) assocs ())
  result <- action
  State.modify $ \(AnnotateData _ v typeMap o) -> (AnnotateData env v typeMap o)
  pure (typeVariable v, result)

getEnv :: VariableTyped t => AnnotateStateV t t
getEnv = State.get >>= (\(AnnotateData v _ _ _) -> pure v)

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
  changeState set (AnnotateData curVar v oldSet extra) = AnnotateData curVar v (oldSet <> set) extra

{--
 - reserve 0 -> n*2 TypeVariables for types of FragExprs
 -}
initState :: VariableTyped v => Term3 -> AnnotateData v ()
initState (Term3 termMap) =
  let startVariable = case Set.maxView (Map.keysSet termMap) of
        Nothing -> 0
        Just (FragIndex i, _) -> (i + 1) * 2
  in AnnotateData (typeVariable 0) startVariable Set.empty ()

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
      EnvF -> getEnv
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
      TraceF -> getEnv
      --(v8 -> ((A,(((v17,v19) -> v7,A),A)) -> v7,v8),Z)
      AuxF (UnsizedRecursion _) -> do -- ugh... just trust this?
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

{-
type AnnotateStateV a = ExceptT TypeCheckError (State (a, Set (TypeAssociationV a), Int))
type AnnotateState = AnnotateStateV PartialType
                 getType :: FragExpr BreakExtras -> AnnotateStateV v v
-}
type AnnotateStateP = ExceptT TypeCheckError
  (State (PossibleType, Set (TypeAssociationV PossibleType), Int, Map Int PossibleType))

possibleTyping :: TypingSupport PossibleType
possibleTyping = TypingSupport
  { fragInputType = \(FragIndex i) -> typeVariable $ i * 2
  , fragOutputType = \(FragIndex i) -> typeVariable $ i * 2 + 1
  , getType = let recur = getType possibleTyping
                  associate = associateVar possibleTyping in \case
      ZeroF -> pure ZeroTypeO
      PairF a b -> PairTypeO <$> recur a <*> recur b
      EnvF -> getEnv
      SetEnvF x -> do
        xt <- recur x
        (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
        associate (PairTypeO (ArrTypeO it ot) it) xt
        pure ot
      DeferF ind -> pure $ ArrTypeO (fragInputType possibleTyping ind) (fragOutputType possibleTyping ind)
      AbortF -> do
        (it, _) <- withNewEnv $ pure ()
        pure (ArrTypeO ZeroTypeO (ArrTypeO it it))
      GateF l r -> do
        lt <- recur l
        rt <- recur r
        pure $ ArrTypeO AnyTypeO (EitherType lt rt)
      LeftF x -> do
        xt <- recur x
        (la, _) <- withNewEnv $ pure ()
        associate (PairTypeO la AnyTypeO) xt
        pure la
      RightF x -> do
        xt <- recur x
        (ra, _) <- withNewEnv $ pure ()
        associate (PairTypeO AnyTypeO ra) xt
        pure ra
      TraceF -> getEnv
      AuxF (UnsizedRecursion _) -> do
        (ta, (tb, (tc, (td, _)))) <- withNewEnv . withNewEnv . withNewEnv . withNewEnv $ pure ()
        let it = PairTypeO AnyTypeO (PairTypeO (PairTypeO (ArrTypeO (PairTypeO tc td) ta) AnyTypeO) AnyTypeO)
        pure $ PairTypeO (ArrTypeO tb (PairTypeO (ArrTypeO it ta) tb)) ZeroTypeO
  , makeAssociations = let recur = makeAssociations possibleTyping in \ta tb -> case (ta, tb) of
      (x, y) | x == y -> pure mempty
      (AnyTypeO, _) -> pure mempty
      (_, AnyTypeO) -> pure mempty
      (EitherType a b, e) -> (<>) <$> recur a e <*> recur b e
      (e, EitherType a b) -> (<>) <$> recur a e <*> recur b e
      (TypeVariableO i, _) -> pure . Set.singleton $ TypeAssociationV i tb
      (_, TypeVariableO i) -> pure . Set.singleton $ TypeAssociationV i ta
      (ArrTypeO a b, ArrTypeO c d) -> Set.union <$> recur a c <*> recur b d
      (PairTypeO a b, PairTypeO c d) -> Set.union <$> recur a c <*> recur b d
      _ -> pure mempty
  }

{-
possibleTypeLookup :: Term3 -> FragExpr BreakExtras -> Either TypeCheckError PossibleType
possibleTypeLookup tm = let resolver = (fullyResolve . snd) <$> partiallyAnnotate possibleTyping tm
                            gt env = let recur = gt env in \case
                              ZeroF -> pure ZeroTypeO
                              PairF a b -> PairTypeO <$> recur a <*> recur b
                              EnvF -> pure env
                              SetEnvF x -> case recur x of
                                (PairTypeO (ArrTypeO _ ot) _) -> pure ot
                                z -> error $ "possibleTypeLookup.setenv bad: " <> show z
                              DeferF ind -> resolver $ ArrTypeO (fragInputType possibleTyping ind)
                                (fragOutputType possibleTyping ind)
                              AbortF
                              
-}

possibleTypeToValue :: PossibleType -> PExpr
possibleTypeToValue = \case
  ZeroTypeO -> PZero
  PairTypeO a b -> PPair (possibleTypeToValue a) (possibleTypeToValue b)
  AnyTypeO -> PAny
  TypeVariableO _ -> PAny
  ArrTypeO _ o -> PDefer $ possibleTypeToValue o
  EitherType a b -> PEither (possibleTypeToValue a) (possibleTypeToValue b)

makePInputMap :: Term3 -> Either TypeCheckError (Map FragIndex PExpr)
makePInputMap term@(Term3 termMap) =
  let resolver = fullyResolve . snd <$> partiallyAnnotate possibleTyping term
      possibleInput = fmap (\f -> possibleTypeToValue . f . fragInputType possibleTyping) resolver
  in (\f -> Map.mapWithKey (\k _ -> f k) termMap) <$> possibleInput

contaminationTyping :: TypingSupport ContaminatedType
contaminationTyping = TypingSupport
  { fragInputType = \(FragIndex i) -> typeVariable $ i * 2
  , fragOutputType = \(FragIndex i) -> typeVariable $ i * 2 + 1
  , getType = let recur = getType contaminationTyping
                  associate = associateVar contaminationTyping in \case
      ZeroF -> pure ZeroTypeC
      PairF a b -> PairTypeC <$> recur a <*> recur b
      EnvF -> getEnv
      SetEnvF x -> do
        xt <- recur x
        (it, (ot, _)) <- withNewEnv . withNewEnv $ pure ()
        associate (PairTypeC (ArrTypeC False it ot) it) xt
        pure ot
      DeferF ind -> pure
        $ ArrTypeC False (fragInputType contaminationTyping ind) (fragOutputType contaminationTyping ind)
      AbortF -> do
        (it, _) <- withNewEnv $ pure ()
        pure (ArrTypeC False ZeroTypeC (ArrTypeC False it it))
      GateF l r -> do
        lt <- recur l
        rt <- recur r
        associate lt rt
        pure $ ArrTypeC False ZeroTypeC lt
      LeftF x -> do
        xt <- recur x
        (la, _) <- withNewEnv $ pure ()
        associate (PairTypeC la AnyTypeC) xt
        pure la
      RightF x -> do
        xt <- recur x
        (ra, _) <- withNewEnv $ pure ()
        associate (PairTypeC AnyTypeC ra) xt
        pure ra
      TraceF -> getEnv
      AuxF (UnsizedRecursion _) -> do
        (ta, (tb, (tc, (td, _)))) <- withNewEnv . withNewEnv . withNewEnv . withNewEnv $ pure ()
        let it = PairTypeC AnyTypeC (PairTypeC (PairTypeC (ArrTypeC False (PairTypeC tc td) ta) AnyTypeC) AnyTypeC)
        pure $ PairTypeC (ArrTypeC True tb (PairTypeC (ArrTypeC False it ta) tb)) ZeroTypeC
  }

data PoisonType
  = ZeroTypeN
  | AnyTypeN
  | PairTypeN PoisonType PoisonType
  | EitherTypeN PoisonType PoisonType
  | ArrTypeN { poisoned :: Set BreakExtras
             , typeFunction :: FragExpr BreakExtras
             }
  deriving (Eq, Ord, Show)

poisoners :: PoisonType -> Set BreakExtras
poisoners = \case
  ArrTypeN pSet _ -> pSet
  EitherTypeN a b -> poisoners a <> poisoners b
  _ -> mempty

infect :: Set BreakExtras -> PoisonType -> PoisonType
infect pSet = \case
  ArrTypeN oldSet tf -> ArrTypeN (oldSet <> pSet) tf
  EitherTypeN a b -> EitherTypeN (infect pSet a) (infect pSet b)
  x -> x

pCombine :: PoisonType -> PoisonType -> PoisonType
pCombine a b = case (a,b) of
  (ZeroTypeN, ZeroTypeN) -> ZeroTypeN
  (AnyTypeN, _) -> AnyTypeN
  (_, AnyTypeN) -> AnyTypeN
  (ArrTypeN sa fa, ArrTypeN sb fb) | fa == fb -> ArrTypeN (sa <> sb) fa
  (PairTypeN a b, PairTypeN c d) | a == c -> PairTypeN a (pCombine b d)
  (PairTypeN a b, PairTypeN c d) | b == d -> PairTypeN (pCombine a c) b
  (EitherTypeN a b, EitherTypeN c d) -> EitherTypeN (pCombine a c) (pCombine b d) -- TODO maybe optimize?
  _ -> EitherTypeN a b

zeroOption :: PoisonType -> Bool
zeroOption = \case
  ZeroTypeN -> True
  EitherTypeN a b -> zeroOption a || zeroOption b
  _ -> False


-- oEval :: PoisonType -> PoisonType -> (Bool, PoisonType)
-- oEval env = \case
  

getContaminatedType :: (FragIndex -> PoisonType) -> PoisonType -> FragExpr BreakExtras -> PoisonType
getContaminatedType getType env = let recur = getContaminatedType getType env in \case
  ZeroF -> ZeroTypeN
  PairF a b -> PairTypeN (recur a) (recur b)
  EnvF -> env
  {-
  SetEnvF x -> case recur x of
    (PairTypeN ft it) -> infect (poisoners it) . infect (poisoners ft) $ typeFunction ft it
    _ -> error "getContaminatedType: bad setenv"
-}
  SetEnvF x -> case recur x of
    (PairTypeN (ArrTypeN fp AbortF) it) -> infect (poisoners it) $ ArrTypeN fp EnvF
    (PairTypeN (ArrTypeN fp (GateF l r)) it) -> infect (poisoners it) . infect fp
      . infect (poisoners $ recur l) $ recur r
    (PairTypeN (ArrTypeN fp (AuxF ur)) it) -> PairTypeN (infect fp it) env
    (PairTypeN (ArrTypeN fp fx) it) -> infect fp . infect (poisoners it) $ getContaminatedType getType it fx
    _ -> error "getContaminatedType: bad setenv"
  DeferF ind -> getType ind
  AbortF -> ArrTypeN mempty AbortF
  {-
  GateF l r -> ArrTypeN mempty $ \case
    ZeroTypeN -> recur l
    AnyTypeN -> infect (poisoners $ recur l) $ recur r
    _ -> recur r
-}
  GateF l r -> ArrTypeN mempty (GateF l r)
  LeftF x -> case recur x of
    PairTypeN l _ -> l
    AnyTypeN -> AnyTypeN
    _ -> ZeroTypeN
  RightF x -> case recur x of
    PairTypeN _ r -> r
    AnyTypeN -> AnyTypeN
    _ -> ZeroTypeN
  TraceF -> env
  AuxF ur -> PairTypeN (ArrTypeN (Set.singleton ur) (AuxF ur)) ZeroTypeN -- warning: weird

makeCInputMap :: Term3 -> FragIndex -> PoisonType
makeCInputMap (Term3 termMap) =
  -- let typeFuns = fmap (\frag f -> ArrTypeN mempty $ \e -> getContaminatedType f e frag) termMap
  let typeFuns = fmap (ArrTypeN mempty) termMap
  -- in fix (flip (typeFuns Map.!))
  in (typeFuns Map.!)

hasContamination :: PoisonType -> Bool
hasContamination = \case
  ArrTypeN s _ | not (null s) -> True
  PairTypeN a b -> hasContamination a || hasContamination b
  EitherTypeN a b -> hasContamination a || hasContamination b
  _ -> False

{--
 - Build a map of functions to convert individual `?` operators to sized church numerals
-}
buildConverterMap :: Term3 -> Map BreakExtras (Term3 -> Int -> Term3)
buildConverterMap (Term3 termMap) =
  let changeMap be (Term3 tm) i =
        let startKey = succ . fst $ Map.findMax tm
            containsUnsized = getAny . monoidFold (\case
              AuxF ur | ur == be -> Any True
              _ -> Any False
              )
            changeIndex = fst . Map.findMax . Map.filter containsUnsized $ tm
            changeTerm = \case
              AuxF ur | ur == be -> partialFixF i
              x -> pure x
            (newFrag, (_,_,newMap)) = State.runState (mMap changeTerm $ tm Map.! changeIndex)
              (0, startKey, tm)
        in Term3 . Map.insert changeIndex newFrag $ newMap
      getUnsized = monoidFold $ \case
        AuxF ur -> Set.singleton ur
        _ -> mempty
      unsizedIndices = fold $ fmap getUnsized termMap
  in Map.fromList . map (\i -> (i, changeMap i)) $ toList unsizedIndices

data SizeTest = SizeTest (FragExpr BreakExtras) PoisonType

type TestMapBuilder = State (Map BreakExtras [SizeTest])

newtype TestMapBuilder' = Compose TestMapBuilder (Reader Int)


fragToPoison :: Monad m => (FragIndex -> FragExpr BreakExtras) -> (PoisonType -> PoisonType -> m PoisonType)
  -> PoisonType -> FragExpr BreakExtras -> m PoisonType
fragToPoison fragLookup setEval env =
  let fragToPoison' = fragToPoison fragLookup setEval
      recur = fragToPoison' env
  in \case
  ZeroF -> pure ZeroTypeN
  PairF a b -> PairTypeN <$> recur a <*> recur b
  EnvF -> pure env
  LeftF x -> let process = \case
                    PairTypeN ln _ -> pure ln
                    z@ZeroTypeN -> pure z
                    a@AnyTypeN -> pure a
                    EitherTypeN a b -> EitherTypeN <$> process a <*> process b
                    z -> error $ "buildTestMap leftF unexpected: " <> show z
              in recur x >>= process
  RightF x -> let process = \case
                    PairTypeN _ rn -> pure rn
                    z@ZeroTypeN -> pure z
                    a@AnyTypeN -> pure a
                    EitherTypeN a b -> EitherTypeN <$> process a <*> process b
                    z -> error $ "buildTestMap rightF unexpected: " <> show z
              in recur x >>= process
  SetEnvF x -> recur x >>= \case
    PairTypeN ft it -> setEval ft it
      -- let setEval = \case
      --       at@(ArrTypeN fp nf) -> case nf of
      --         AbortF -> pure . infect (poisoners it) $ ArrTypeN fp EnvF
      --         GateF l r -> infect (poisoners it) . infect fp <$> case it of -- TODO 'it' can't have poisoners?
      --           ZeroTypeN -> recur l
      --           PairTypeN _ _ -> recur r
      --           AnyTypeN -> pCombine <$> recur l <*> recur r
      --           e@(EitherTypeN _ _) -> if zeroOption e
      --             then pCombine <$> recur l <*> recur r
      --             else recur r
      --           z -> error $ "buildTestMap setenv gate unexpected: " <> show z
      --         AuxF _ -> pure $ PairTypeN (infect fp it) env
      --         -- DeferF _ -> infect (poisoners it) <$> builder it nf
      --         _ -> (infect (poisoners it) <$> fragToPoison' it nf) >>= recordSizeTest (SizeTest nf pt)
      --       EitherTypeN a b -> pCombine <$> setEval a <*> setEval b
      --       z -> error $ "buildTestMap setenv seteval unexpected: " <> show z
      -- in setEval ft
    z -> error $ "buildTestMap setenv not pair: " <> show z
  -- DeferF ind -> case Map.lookup ind termMap of
  --   Just frag -> pure $ ArrTypeN mempty frag
  --   _ -> error "buildTestMap: bad defer index"
  DeferF ind -> pure . ArrTypeN mempty $ fragLookup ind
  g@(GateF _ _) -> pure $ ArrTypeN mempty g
  AbortF -> pure $ ArrTypeN mempty AbortF
  a@(AuxF ur) -> pure $ PairTypeN (ArrTypeN (Set.singleton ur) a) ZeroTypeN
  TraceF -> pure env

buildTestMap :: Term3 -> Map BreakExtras [SizeTest]
buildTestMap term@(Term3 termMap) =
  let poisonType = makeCInputMap term
      possibleTypeMap = buildZInputMap term
      alterSizeTest v = \case
        Nothing -> pure [v]
        Just e -> pure $ v : e
      addSizeTest k v = State.modify $ Map.alter (alterSizeTest v) k
      builder env = let recur = builder env in \case
        ZeroF -> pure ZeroTypeN
        PairF a b -> PairTypeN <$> recur a <*> recur b
        EnvF -> pure env
        LeftF x -> let process = \case
                         PairTypeN ln _ -> pure ln
                         z@ZeroTypeN -> pure z
                         a@AnyTypeN -> pure a
                         EitherTypeN a b -> EitherTypeN <$> process a <*> process b
                         z -> error $ "buildTestMap leftF unexpected: " <> show z
                   in recur x >>= process
        RightF x -> let process = \case
                          PairTypeN _ rn -> pure rn
                          z@ZeroTypeN -> pure z
                          a@AnyTypeN -> pure a
                          EitherTypeN a b -> EitherTypeN <$> process a <*> process b
                          z -> error $ "buildTestMap rightF unexpected: " <> show z
                    in recur x >>= process
        SetEnvF x -> recur x >>= \case
          pt@(PairTypeN ft it) ->
            let setEval = \case
                  at@(ArrTypeN fp nf) -> case nf of
                    AbortF -> pure . infect (poisoners it) $ ArrTypeN fp EnvF
                    GateF l r -> infect (poisoners it) . infect fp <$> case it of -- TODO 'it' can't have poisoners?
                      ZeroTypeN -> recur l
                      PairTypeN _ _ -> recur r
                      AnyTypeN -> pCombine <$> recur l <*> recur r
                      e@(EitherTypeN _ _) -> if zeroOption e
                        then pCombine <$> recur l <*> recur r
                        else recur r
                      z -> error $ "buildTestMap setenv gate unexpected: " <> show z
                    AuxF _ -> pure $ PairTypeN (infect fp it) env -- TODO this needs to be recalculated
                    -- DeferF _ -> infect (poisoners it) <$> builder it nf
                    _ -> (infect (poisoners it) <$> builder it nf) >>=
                      \opt -> (if hasContamination at && not (hasContamination opt)
                               then mapM_ (flip addSizeTest (SizeTest nf pt)) fp
                               else pure ()
                              ) >> pure opt
                  EitherTypeN a b -> pCombine <$> setEval a <*> setEval b
                  z -> error $ "buildTestMap setenv seteval unexpected: " <> show z
            in setEval ft
          z -> error $ "buildTestMap setenv not pair: " <> show z
        DeferF ind -> case Map.lookup ind termMap of
          Just frag -> pure $ ArrTypeN mempty frag
          _ -> error "buildTestMap: bad defer index"
        g@(GateF _ _) -> pure $ ArrTypeN mempty g
        AbortF -> pure $ ArrTypeN mempty AbortF
        a@(AuxF ur) -> pure $ PairTypeN (ArrTypeN (Set.singleton ur) a) ZeroTypeN
        TraceF -> pure env
  in State.execState (builder AnyTypeN (rootFrag termMap)) Map.empty

annotate :: Ord v => TypingSupport v -> Term3 -> AnnotateStateV v v
annotate ts (Term3 termMap) =
  let initInputType fi = let it = fragInputType ts fi in State.modify (\s -> s {envType = it})
      associateOutType fi ot = let ot2 = fragOutputType ts fi in associateVar ts ot ot2
      rootType = initInputType (FragIndex 0) >> getType ts (rootFrag termMap)
  in sequence_ (Map.mapWithKey (\k v -> initInputType k >> getType ts v >>= associateOutType k) termMap) >> rootType

partiallyAnnotate :: (Ord v, VariableTyped v, Show v) =>
  TypingSupport v -> Term3 -> Either TypeCheckError (v, Int -> Maybe v)
partiallyAnnotate ts term =
  let runner = runExceptT $ annotate ts term
      (rt, as) = State.runState runner (initState term)
      associate = makeAssociations ts
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap (associations as) associate)

inferType :: Term3 -> Either TypeCheckError PartialType
inferType tm = lookupFully <$> partiallyAnnotate terminationTyping tm where
  lookupFully (ty, resolver) = fullyResolve resolver ty

typeCheck :: PartialType -> Term3 -> Maybe TypeCheckError
typeCheck t tm@(Term3 typeMap) = convert (partiallyAnnotate terminationTyping tm >>= associate) where
  associate (ty, resolver) = debugTrace ("COMPARING TYPES " <> show (t, fullyResolve resolver ty) <> "\n" <> debugMap ty resolver)
    . traceAgain $ makeAssociations terminationTyping (fullyResolve resolver ty) t
  getFragType fi = ArrTypeP (fragInputType terminationTyping fi) (fragOutputType terminationTyping fi)
  debugMap ty resolver = showTypeDebugInfo (TypeDebugInfo tm (fullyResolve resolver . getFragType)
                                            (fullyResolve resolver ty))
  traceAgain s = debugTrace ("Resulting thing " <> show s) s
  convert = \case
    Left er -> Just er
    _ -> Nothing

