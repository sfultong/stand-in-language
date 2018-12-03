{-#LANGUAGE DeriveGeneric#-}
{-#LANGUAGE DeriveAnyClass#-}
{-#LANGUAGE GeneralizedNewtypeDeriving#-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE EmptyDataDecls #-}
module Naturals where

import Control.Applicative
import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.State.Lazy
import Data.Binary
import Data.Int (Int64)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import Debug.Trace
import Control.DeepSeq
import GHC.Generics

import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Data.Set as Set

import SIL

data NaturalType
  = ZeroTypeN
  | PairTypeN NaturalType NaturalType
  | ArrTypeN FragIndex
  | GateTypeN
  | ChurchType
  | UnknownN
  deriving (Eq, Ord, Show)

{-
typeLeft :: NaturalType -> NaturalType
typeLeft (PairTypeN l _) = l
typeLeft _ = ZeroTypeN

typeRight :: NaturalType -> NaturalType
typeRight (PairTypeN _ r) = r
typeRight _ = ZeroTypeN
-}

newtype FragIndex = FragIndex { unFragIndex :: Int } deriving (Eq, Show, Ord, Enum, NFData, Generic)
newtype TypeIndex = TypeIndex { unTypeIndex :: Int } deriving (Eq, Show, Ord, Enum)

instance Binary FragIndex
{-
strategy:
1. break AST into fragments on Defers
2. generate type for each fragment
3. compute input type for each fragment
4. use fragments and types to generate enhanced AST

-}


data ExprFrag
  = FZero
  | FPair ExprFrag ExprFrag
  | FEnv
  | FSetEnv ExprFrag
  | FDefer FragIndex
  | FAbort ExprFrag
  | FGate ExprFrag
  | FLeft ExprFrag
  | FRight ExprFrag
  | FTrace ExprFrag
  -- complex instructions
  | FITE ExprFrag ExprFrag ExprFrag
  | FApp ExprFrag ExprFrag
  | FNum Int64
  deriving (Eq, Show, Ord)

data FragType
  = ZeroTypeF
  | PairTypeF FragType FragType
  | ArrTypeF [FragIndex] (FragType -> FragType)
  | ChurchTypeF
  | PartialChurchTypeF FragType
  | UnknownTypeF
  | GateTypeF
--  deriving (Eq, Show, Ord)

typeLeft :: FragType -> FragType
typeLeft (PairTypeF l _) = l
typeLeft ZeroTypeF = ZeroTypeF
typeLeft _ = UnknownTypeF

typeRight :: FragType -> FragType
typeRight (PairTypeF _ r) = r
typeRight ZeroTypeF = ZeroTypeF
typeRight _ = UnknownTypeF

getInnerType :: FragType -> FragType
getInnerType (PartialChurchTypeF x) = getInnerType x
getInnerType x = x

unifyArrows :: FragType -> FragType -> FragType
unifyArrows (PairTypeF a b) (PairTypeF c d) = PairTypeF (unifyArrows a c) (unifyArrows b d)
unifyArrows (ArrTypeF indA f) (ArrTypeF indB _) = ArrTypeF (indA ++ indB) f
unifyArrows (PartialChurchTypeF a) (PartialChurchTypeF b) = PartialChurchTypeF (unifyArrows a b)
unifyArrows x _ = x

instance Show FragType where
  show ZeroTypeF = "ZeroTypeF"
  show (PairTypeF a b) = concat ["PairTypeF (", show a, ", ", show b, ")"]
  show (ArrTypeF ind _) = concat ["ArrTypeF ", show ind]
  show ChurchTypeF = "ChurchTypeF"
  show UnknownTypeF = "UnknownTypeF"
  show GateTypeF = "GateTypeF"
  show (PartialChurchTypeF t) = concat ["PartialChurchTypeF ", show t]

isChurchType :: FragType -> Bool
isChurchType ChurchTypeF = True
isChurchType _ = False

isZeroType :: FragType -> Bool
isZeroType ZeroTypeF = True
isZeroType (PairTypeF a b) = isZeroType a && isZeroType b
isZeroType _ = False

{-
isChurchTypePair :: FragType -> Bool
isChurchTypePair (PairTypeF ChurchTypeF _) = True
isChurchTypePair _ = False

isPartialChurchPair :: FragType -> Bool
isPartialChurchPair (PairTypeF (PartialChurchTypeF _) _) = True
isPartialChurchPair _ = False
-}
traceSet inds x = if elem (FragIndex 1) inds
                  then trace ("env at index 1: " ++ show x) x
                  else x

fTypeSetA :: Applicative a => ([FragIndex] -> FragType -> a ()) -> FragType -> FragType -> a (Maybe FragType)
fTypeSetA f (ArrTypeF ind ft) x = f ind (traceSet ind x) *> (pure . pure $ ft x)
fTypeSetA _ GateTypeF (PairTypeF ChurchTypeF x) = pure . pure $ x
fTypeSetA _ GateTypeF (PairTypeF x _) = pure . pure $ x
fTypeSetA _ _ _ = pure Nothing

fTypeApplyA :: Applicative a => ([FragIndex] -> FragType -> a ()) -> FragType -> FragType -> a (Maybe FragType)
fTypeApplyA f (PairTypeF ct et) it = fTypeSetA f ct (PairTypeF it et)
fTypeApplyA _ ChurchTypeF ChurchTypeF = pure $ pure ChurchTypeF
fTypeApplyA _ ChurchTypeF it = pure . pure $ PartialChurchTypeF it
fTypeApplyA f (PartialChurchTypeF ft) it = fTypeApplyA f ft it
fTypeApplyA _ _ _ = pure Nothing

-- type results of setenv
fTypeSet :: FragType -> FragType -> Maybe FragType
fTypeSet a b = runIdentity $ fTypeSetA (\_ _ -> pure ()) a b
--fTypeSet (ArrTypeF _ ft) x = pure $ ft x
--fTypeSet ChurchTypeF ft = pure $ ft
{-
fTypeSet ChurchTypeF (PairTypeF ft _) = pure $ ft
fTypeSet (PartialChurchTypeF f) (PairTypeF x _) = fTypeSet f x
-}
{-
fTypeSet GateTypeF (PairTypeF ChurchTypeF x) = pure $ x
fTypeSet GateTypeF (PairTypeF x _) = pure $ x
fTypeSet _ _ = Nothing
-}

-- type results of app
fTypeApply :: FragType -> FragType -> Maybe FragType
fTypeApply a b = runIdentity $ fTypeApplyA (\_ _ -> pure ()) a b
{-
fTypeApply (PairTypeF ct et) it = fTypeSet ct (PairTypeF it et)
fTypeApply ChurchTypeF ChurchTypeF = pure ChurchTypeF
fTypeApply ChurchTypeF it = pure $ PartialChurchTypeF it
fTypeApply (PartialChurchTypeF ft) it = fTypeApply ft it
fTypeApply _ _ = Nothing
-}

data NExpr
  = NZero
  | NPair NExpr NExpr
  | NEnv
  | NSetEnv NExpr
  | NDefer FragIndex
  | NAbort NExpr
  | NGate NExpr
  | NLeft NExpr
  | NRight NExpr
  | NTrace NExpr
  | NNum Int64
  | NAdd NExpr NExpr
  | NMult NExpr NExpr
  | NPow NExpr NExpr
  {-
  | NConvertSetEnv NExpr -- if we've converted a church numeral to an NNum, we need to convert it back at some point
  | NForLoop Int64 NExpr -- for runtime, function and number of times to apply it
-}
  | NApp NExpr NExpr
  | NChurchAppOne NExpr NExpr
  | NChurchAppTwo NExpr NExpr
  | NITE NExpr NExpr NExpr
  deriving (Eq, Show, Ord, Generic, NFData)

instance Binary NExpr

newtype NExprs = NExprs (Map FragIndex (NExpr, FragType))

instance Show NExprs where
  show (NExprs m) =
    let showInner frag = case frag of
          NZero -> "NZero"
          (NPair a b) -> concat ["{ ", showInner a, ", ", showInner b, " }"]
          NEnv -> "NEnv"
          (NSetEnv x) -> concat ["NSetEnv (", showInner x, ")"]
          (NDefer ind) -> case Map.lookup ind m of
            Just (x, _) -> concat ["NDefer (", showInner x, ")"]
            Nothing -> concat ["ERROR undefined index in showing NExprs: ", show ind]
          (NAbort x) -> concat ["NAbort (", showInner x, ")"]
          (NGate x) -> concat ["NGate (", showInner x, ")"]
          (NLeft x) -> concat ["NLeft (", showInner x, ")"]
          (NRight x) -> concat ["NRight (", showInner x, ")"]
          (NTrace x) -> concat ["NTrace (", showInner x, ")"]
          (NAdd a b) -> concat ["NAdd (", showInner a, " ", showInner b, " )"]
          (NMult a b) -> concat ["NMult (", showInner a, " ", showInner b, " )"]
          (NPow a b) -> concat ["NPow (", showInner a, " ", showInner b, " )"]
          -- (NConvertSetEnv x) -> concat ["NConvertSetEnv (", showInner x, ")"]
          (NITE i t e) -> concat ["if (", showInner i, ") then (", showInner t, ") else (", showInner e, ")"]
          (NChurchAppOne c i) -> concat ["NChurchAppOne (", showInner c, " ", showInner i, " )"]
          (NChurchAppTwo c i) -> concat ["NChurchAppTwo (", showInner c, " ", showInner i, " )"]
          x -> show x
    in case Map.lookup (FragIndex 0) m of
      Just (x, _) -> showInner x
      _ -> "ERROR no root to NExprs tree"

type FragState = State (FragIndex, Map FragIndex ExprFrag)

toFrag :: IExpr -> FragState ExprFrag
-- complex instructions
toFrag (ITE i t e) = FITE <$> toFrag i <*> toFrag t <*> toFrag e
toFrag (App f x) = FApp <$> toFrag f <*> toFrag x
toFrag (ChurchNum x) = pure . FNum $ fromIntegral x
-- simple instructions
toFrag Zero = pure FZero
toFrag (Pair a b) = FPair <$> toFrag a <*> toFrag b
toFrag Env = pure FEnv
toFrag (SetEnv x) = FSetEnv <$> toFrag x
toFrag (Defer x) = do
  nx <- toFrag x
  (ei@(FragIndex i), fragMap) <- State.get
  let td = id -- trace ("adding defer " ++ show i ++ " - " ++ show nx)
  State.put (FragIndex (i + 1), td Map.insert ei nx fragMap)
  pure $ FDefer ei
toFrag (Abort x) = FAbort <$> toFrag x
toFrag (Gate x) = FGate <$> toFrag x
toFrag (PLeft x) = FLeft <$> toFrag x
toFrag (PRight x) = FRight <$> toFrag x
toFrag (Trace x) = FTrace <$> toFrag x

fromFrag :: Map FragIndex ExprFrag -> ExprFrag -> IExpr
fromFrag fragMap frag = let recur = fromFrag fragMap in case frag of
  FZero -> Zero
  (FPair a b) -> Pair (recur a) (recur b)
  FEnv -> Env
  (FSetEnv x) -> SetEnv $ recur x
  (FDefer fi) -> case Map.lookup fi fragMap of
    Nothing -> error ("fromFrag bad index " ++ show fi)
    Just subFrag -> Defer $ recur subFrag
  (FAbort x) -> Abort $ recur x
  (FGate x) -> Gate $ recur x
  (FLeft x) -> PLeft $ recur x
  (FRight x) -> PRight $ recur x
  (FTrace x) -> Trace $ recur x
  z -> error ("fromFrag TODO convert " ++ show z)

matchChurchPlus :: Map FragIndex ExprFrag -> ExprFrag -> Maybe (ExprFrag, ExprFrag)
matchChurchPlus fragMap frag =
  let lam (FPair (FDefer ind) FEnv) = Map.lookup ind fragMap
      lam _ = Nothing
      def (FDefer ind) = Map.lookup ind fragMap
      def _ = Nothing
      firstArg (FLeft FEnv) = Just ()
      firstArg _ = Nothing
      secondArg (FLeft (FRight FEnv)) = Just ()
      secondArg _ = Nothing
      app = matchApp
  in lam frag >>= lam >>= app >>= (\(a, b) -> (,) <$> (app a >>= (\(m, sa) -> secondArg sa >> pure m))
                                              <*> (app b >>= (\(c, fa) -> firstArg fa >> app c
                                                               >>= (\(n, sa) -> secondArg sa >> pure n)))
                                  )

matchChurchMult :: Map FragIndex ExprFrag -> ExprFrag -> Maybe (ExprFrag, ExprFrag)
matchChurchMult fragMap frag =
  let lam (FPair (FDefer ind) FEnv) = Map.lookup ind fragMap
      lam _ = Nothing
      def (FDefer ind) = Map.lookup ind fragMap
      def _ = Nothing
      firstArg (FLeft FEnv) = Just ()
      firstArg _ = Nothing
  in lam frag >>= matchApp >>= (\(m, a) -> (,) <$> pure m <*> (matchApp a >>= (\(n, fa) -> firstArg fa >> pure n)))

matchApp :: ExprFrag -> Maybe (ExprFrag, ExprFrag)
matchApp (FApp c i) = Just (c, i)
matchApp _ = Nothing

matchITE :: ExprFrag -> Maybe (ExprFrag, ExprFrag, ExprFrag)
matchITE (FSetEnv (FPair (FGate i) (FPair e t))) = Just (i, t, e)
matchITE _ = Nothing

getFragType :: (FragIndex -> FragType) -> Map FragIndex ExprFrag -> ExprFrag -> FragType -> FragType
getFragType getFrag fragMap frag envType =
  let recur x = getFragType getFrag fragMap x envType
      envUpOne = PairTypeF UnknownTypeF envType
      envUpTwo = PairTypeF UnknownTypeF envUpOne
      tgt x et = let t = getFragType getFrag fragMap x et in trace ("first type: " ++ show t) t
      tgt2 x et = let t = getFragType getFrag fragMap x et in trace ("second type: " ++ show t) t
      passChurch et (Just (a,b)) =
        if isChurchType (getFragType getFrag fragMap a et) && isChurchType (getFragType getFrag fragMap b et)
        then Just $ ChurchTypeF -- PairTypeF ChurchTypeF envType
        else Nothing
      passChurch _ _ = Nothing
  {-
      passOneChurch et (Just (a,b)) =
        let secondType = getFragType getFrag fragMap b et
        in if isChurchTypePair (getFragType getFrag fragMap a et) && not (isChurchTypePair secondType)
           then Just $ PairTypeF (PartialChurchTypeF secondType) envType
           else Nothing
-}
      passOneChurch _ _ = Nothing
      passPartialChurch et (Just (a,b)) =
        let firstType = getFragType getFrag fragMap a et
        in case firstType of
             (PairTypeF (PartialChurchTypeF pctf) nenv) -> fTypeSet pctf $
               PairTypeF (getFragType getFrag fragMap b et) nenv
             _ -> Nothing
      passPartialChurch _ _ = Nothing

  {-
      bothChurch et (Just (a,b)) = isChurchTypePair (getFragType getFrag fragMap a et)
                                   && isChurchTypePair (getFragType getFrag fragMap b et)
-}
  {-
      bothChurch et (Just (a,b)) = trace "FOFOOFOOO  " isChurchTypePair (tgt a et)
                                   && isChurchTypePair (tgt2 b et)
-}
      bothChurch _ _ = False
      isChurch = (bothChurch envUpTwo $ matchChurchPlus fragMap frag)
        || (bothChurch envUpOne $ matchChurchMult fragMap frag)
        || (bothChurch envType $ matchApp frag)
      complexOptions = [ passChurch envUpTwo $ matchChurchPlus fragMap frag
                       , passChurch envUpOne $ matchChurchMult fragMap frag
                       -- , matchApp frag >>= \(a,b) -> fTypeApply (recur a) (recur b)
                       {-
                       , passChurch envType $ matchApp frag
                       , passOneChurch envType $ matchApp frag
                       , passPartialChurch envType $ matchApp frag
-}
                       ]
      complexMatch = getAlt . mconcat $ map Alt complexOptions
      dumpInfo = concat ["\n", show fragMap, "\n", show frag, "\n", show envType, "\n"]
      simpleInstruction = case frag of
        FZero -> ZeroTypeF
        -- hack to give Abort expressions a type
        (FPair x (FAbort _)) -> let nx = recur x in PairTypeF nx nx
        (FPair (FAbort _) x) -> let nx = recur x in PairTypeF nx nx
        (FPair a b) -> PairTypeF (recur a) (recur b)
        FEnv -> envType
        (FSetEnv x) -> case recur x of
          (PairTypeF f i) -> case fTypeSet f i of
            Just rt -> rt
            --Nothing -> error "getFragType setenv - bad apply"
            _ -> UnknownTypeF
          badX -> error "getFragType setenv - not pair" -- ++ show badX)
        (FDefer ind) -> getFrag ind
        (FAbort _) -> UnknownTypeF
        (FGate _) -> GateTypeF
        (FLeft x) -> typeLeft $ recur x
        (FRight x) -> typeRight $ recur x
        (FTrace x) -> recur x
        (FITE _ t e) -> unifyArrows (recur t) (recur e)
        (FNum _) -> ChurchTypeF -- PairTypeF ChurchTypeF envType
        (FApp c i) -> case fTypeApply (recur c) (recur i) of
          Just t -> t
          _ -> trace ("gettype app unknown " ++ show c ++ " <-- " ++ show i) UnknownTypeF

  {-
          (PairTypeF cc ce, ci) -> case fTypeSet cc (PairTypeF ci ce) of
            Just t -> t
            _ -> UnknownTypeF
          z -> error ("getFragType fapp - not pair " ++ show z)
-}
  in case (complexMatch, simpleInstruction) of
    (Just t, _) -> t
    (_, s) -> s

buildTypeMap :: Map FragIndex ExprFrag -> (ExprFrag -> FragType -> FragType) -> ExprFrag -> FragType
  -> Map FragIndex FragType -> Map FragIndex FragType
buildTypeMap fragMap getType frag envType typeMap =
  let recur x = buildTypeMap fragMap getType x envType in case frag of
  (FPair a b) -> recur a (recur b typeMap)
  (FSetEnv x) -> case getType x envType of
    -- (PairTypeF (ArrTypeF _ _) UnknownTypeF) -> recur x typeMap -- ignore undefined inputs
    -- TODO prefer one input type if one already exists in the map?
    (PairTypeF (ArrTypeF (ind:_) _) it) -> case Map.lookup ind fragMap of
      (Just ifrag) -> buildTypeMap fragMap getType ifrag it $ Map.insert ind it typeMap
      _ -> error ("buildTypeMap fsetenv - looking up function frag failed " ++ show ind)
    _ -> recur x typeMap
  (FAbort x) -> recur x typeMap
  (FGate x) -> recur x typeMap
  (FLeft x) -> recur x typeMap
  (FRight x) -> recur x typeMap
  (FTrace x) -> recur x typeMap
  _ -> typeMap

fragmentExpr :: IExpr -> (Map FragIndex ExprFrag, ExprFrag -> FragType -> FragType)
fragmentExpr iexpr = let (expr, (li, m)) = State.runState (toFrag iexpr) ((FragIndex 1), Map.empty)
                         fragMap = Map.insert (FragIndex 0) expr m
                         -- tt x = trace (show x) x
                         makeType fragIndex frag getFrag = ArrTypeF [fragIndex] $ getFragType getFrag fragMap frag
                         pairedWithFun = Map.mapWithKey makeType fragMap
                         getTypeFun ind = case Map.lookup ind pairedWithFun of
                           (Just tf) -> tf
                           _ -> error ("fragmentExpr - gettypefun bad index " ++ show ind)
                         getFullFragType = fix $ flip getTypeFun
                         getTypeWithEnv = getFragType getFullFragType fragMap
                     -- in (Map.mapWithKey combineWithInputType fragMap, getTypeWithEnv)
                     in (fragMap, getTypeWithEnv)

fragsToNExpr :: Map FragIndex ExprFrag -> (ExprFrag -> FragType -> FragType) -> FragType
  -> Map FragIndex (NExpr, FragType)
fragsToNExpr fragMap getType et =
  let processFrag :: ExprFrag -> FragType -> State (Map FragIndex (NExpr, FragType)) NExpr
      processFrag frag envType =
        let recur x = processFrag x envType
            envUpOne = PairTypeF UnknownTypeF envType
            envUpTwo = PairTypeF UnknownTypeF envUpOne
            traceTypes x = trace ("input types: " ++ show x) x
            passChurch passEnv (Just (a,b)) = trace "passing in the churchiest place" $
              if isChurchType (getType a passEnv) && isChurchType (getType b passEnv)
              then -- trace ("passingChurch " ++ show a ++ " --- " ++ show b)
                Just ((,) <$> processFrag a passEnv <*> processFrag b passEnv)
              else Nothing
            passChurch _ _ = Nothing
  {-
            passChurch2 passEnv (Just (a,b)) =
              if and . map isChurchTypePair $ traceTypes [getType a passEnv, getType b passEnv]
              then Just ((,) <$> processFrag a passEnv <*> processFrag b passEnv)
              else Nothing
            passChurch2 _ _ = Nothing
            passFirstChurch passEnv (Just (a,b)) =
              if isChurchTypePair (getType a passEnv) && not (isChurchTypePair (getType b passEnv))
              then Just ((,) <$> processFrag a passEnv <*> processFrag b passEnv)
              else Nothing
-}
            passFirstChurch _ _ = Nothing
            passPartialChurch passEnv (Just (a,b)) =
              case (getType a passEnv) of
                (PairTypeF (PartialChurchTypeF pctf) nenv) ->
                  let processFirst = do
                        case getInnerType pctf of
                          (PairTypeF (ArrTypeF iind _) ienv) -> -- trace ("capping - " ++ show iind)
                            processInnerDefer iind (PairTypeF (getType b passEnv) nenv)
                          z -> trace ("capping odd - " ++ show z) pure ()
                        processFrag a passEnv
                  in Just ((,) <$> processFirst <*> processFrag b passEnv)
                _ -> Nothing
            passPartialChurch _ _ = Nothing
            complexMatches = [ fmap (uncurry NAdd) <$> (passChurch envUpTwo $ matchChurchPlus fragMap frag)
                             , fmap (uncurry NMult) <$> (passChurch envUpOne $ matchChurchMult fragMap frag)
                             {-
                             , fmap (uncurry $ flip NPow) <$> (passChurch envType $ matchApp frag)
                             , fmap (uncurry NChurchAppOne) <$> (passFirstChurch envType $ matchApp frag)
                             , fmap (uncurry NChurchAppTwo) <$> (passPartialChurch envType $ matchApp frag)
-}
                             ]
            complexMatch = getAlt . mconcat $ map Alt complexMatches
            processInnerDefer ind t =
              let processOne i = case Map.lookup i fragMap of
                    (Just fg) -> do
                      let traceOne = case i of
                            (FragIndex 1) -> trace ("processindef env " ++ show t)
                            _ -> id
                      nMap <- traceOne $ State.get
                      if Map.member i nMap
                        then pure ()
                        else processFrag fg t >>= (\p -> State.modify (Map.insert i (p, t)))
                    Nothing -> error "fragsToNExpr - processFrag - processInnerDefer - index not found"
              in mapM_ processOne ind
        in case complexMatch of
          Just x -> x
          _ -> case frag of
            FZero -> pure NZero
            FEnv -> pure NEnv
            (FPair a b) -> NPair <$> recur a <*> recur b
            {-
            (FSetEnv x) -> case getType x envType of
              (PairTypeF ChurchTypeF _) -> NConvertSetEnv <$> recur x
              (PairTypeF (ArrTypeF ind _) it) -> case Map.lookup ind fragMap of
                Just fg -> do
                  nMap <- State.get
                  if Map.member ind nMap
                    then pure ()
                    else processFrag fg it >>= (\p -> State.modify (\m -> Map.insert ind p))
                  NSetEnv <$> recur x
                Nothing -> error "fragsToNExpr - processFrag - simpleMap - fsetenv - index not found"
              _ -> NSetEnv $ recur x
-}
            (FSetEnv x) -> do
              case getType x envType of
                (PairTypeF ft it) -> fTypeSetA processInnerDefer ft it *> pure ()
                _ -> pure ()
              NSetEnv <$> recur x
            (FGate x) -> NGate <$> recur x
            (FLeft x) -> NLeft <$> recur x
            (FRight x) -> NRight <$> recur x
            (FTrace x) -> NTrace <$> recur x
            (FAbort x) -> NAbort <$> recur x
            (FDefer ind) -> pure $ NDefer ind
            (FNum x) -> pure $ NNum x
            (FITE i t e) -> NITE <$> recur i <*> recur t <*> recur e
            (FApp c i) -> trace ("apping " ++ show c ++ " --- " ++  show (getType c envType) ++ show " --- " ++ show envType) $ case (getType c envType, getType i envType) of
              (ChurchTypeF, ChurchTypeF) -> NPow <$> recur i <*> recur c
              (ChurchTypeF, (PartialChurchTypeF _)) -> NMult <$> recur c <*> recur i
              (ChurchTypeF, _) -> NChurchAppOne <$> recur c <*> recur i
              (ct, it) -> do
                _ <- fTypeApplyA processInnerDefer ct it
                NApp <$> recur c <*> recur i
              {-
              fTypeApplyA processInnerDefer (getType c envType) (getType i envType) >>= \x -> case x of
                Just ChurchTypeF -> NPow <$> recur i <*> recur c
                Just (PartialChurchTypeF _) -> NChurchAppOne <$> recur c <*> recur i
                Just _ -> NApp <$> recur c <*> recur i
                _ -> error ("fragsToNExpr - processFrag - fapp - bad app " ++ show (getType c envType) ++ " -- " ++ show c)
-}
  {-
              case getType c envType of
                (PairTypeF (ArrTypeF ind _) it) -> trace ("apping " ++ show ind) processInnerDefer ind (PairTypeF (getType i envType) it)
                _ -> pure ()
              NApp <$> recur c <*> recur i
-}
  {-
            (FDefer ind) -> case Map.lookup ind fragMap of
              (Just (df, ft)) -> trace ("processing " ++ show ind) processFrag df ft
              _ -> error ("fragsToNExpr simplematch fdefer index not found " ++ show ind)
-}
  in case Map.lookup (FragIndex 0) fragMap of
    (Just x) -> (\(n, m) -> Map.insert (FragIndex 0) (n, et) m) $ State.runState (processFrag x et) Map.empty
    _ -> error "fragsToNExpr top level frag not found"

debugShow x = x -- trace ("toNExpr\n" ++ show x) x

toNExpr :: IExpr -> NExprs
toNExpr = debugShow . (\(m,f) -> NExprs $ fragsToNExpr m f ZeroTypeF) . fragmentExpr

fromNExpr :: NExpr -> IExpr
fromNExpr x = case x of
  NZero -> Zero
  (NPair a b) -> Pair (fromNExpr a) (fromNExpr b)
  NEnv -> Env
  (NSetEnv x) -> SetEnv (fromNExpr x)
  -- (NDefer x) -> Defer (fromNExpr x)
  (NAbort x) -> Abort (fromNExpr x)
  (NGate x) -> Gate (fromNExpr x)
  (NLeft x) -> PLeft (fromNExpr x)
  (NRight x) -> PRight (fromNExpr x)
  (NTrace x) -> Trace (fromNExpr x)
  _ -> error "fromNExpr TODO"
