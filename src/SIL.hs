{-# LANGUAGE DeriveFunctor #-}
module SIL where

import Control.Monad.Fix
import Control.Monad.State.Lazy
import Data.Char
import Data.Map (Map)
import Data.Set (Set)
import Data.Functor.Identity
import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set

data IExpr
  = Zero                     -- no special syntax necessary
  | Pair !IExpr !IExpr       -- {,}
  | Var !IExpr               -- identifier
  | App !IExpr !IExpr        --
  | Anno !IExpr !IExpr       -- :
  | Gate !IExpr
  | PLeft !IExpr             -- left
  | PRight !IExpr            -- right
  | Trace !IExpr             -- trace
  | Closure !IExpr !IExpr
  deriving (Eq, Show, Ord)

data IExprA a
  = ZeroA
  | PairA (IExprA a) (IExprA a)
  | VarA (IExprA a) a
  | AppA (IExprA a) (IExprA a) a
  | AnnoA (IExprA a) IExpr
  | GateA (IExprA a)
  | PLeftA (IExprA a)
  | PRightA (IExprA a)
  | TraceA (IExprA a)
  | ClosureA (IExprA a) (IExprA a) a
  deriving (Eq, Show, Ord, Functor)

lam :: IExpr -> IExpr
lam x = Closure x Zero

ite :: IExpr -> IExpr -> IExpr -> IExpr
ite i t e = App (Gate i) (Pair e t)

getPartialAnnotation :: IExprA PartialType -> PartialType
getPartialAnnotation (VarA _ a) = a
getPartialAnnotation (AppA _ _ a) = a
getPartialAnnotation (ClosureA _ _ a) = a
getPartialAnnotation ZeroA = ZeroTypeP
getPartialAnnotation (PairA _ _) = ZeroTypeP
getPartialAnnotation (AnnoA x _) = getPartialAnnotation x
getPartialAnnotation (GateA _) = ArrTypeP ZeroTypeP ZeroTypeP
getPartialAnnotation (PLeftA _) = ZeroTypeP
getPartialAnnotation (PRightA _) = ZeroTypeP
getPartialAnnotation (TraceA x) = getPartialAnnotation x

data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord)

packType :: DataType -> IExpr
packType ZeroType = Zero
packType (ArrType a b) = Pair (packType a) (packType b)

unpackType :: IExpr -> Maybe DataType
unpackType Zero = pure ZeroType
unpackType (Pair a b) = ArrType <$> unpackType a <*> unpackType b
unpackType _ = Nothing

unpackPartialType :: IExpr -> Maybe PartialType
unpackPartialType Zero = pure ZeroTypeP
unpackPartialType (Pair a b) = ArrTypeP <$> unpackPartialType a <*> unpackPartialType b
unpackPartialType _ = Nothing

data PartialType
  = ZeroTypeP
  | TypeVariable Int
  | ArrTypeP PartialType PartialType
  | PairTypeP PartialType PartialType
  deriving (Eq, Show, Ord)

toPartial :: DataType -> PartialType
toPartial ZeroType = ZeroTypeP
toPartial (ArrType a b) = ArrTypeP (toPartial a) (toPartial b)

badType = TypeVariable (-1)

newtype PrettyIExpr = PrettyIExpr IExpr

instance Show PrettyIExpr where
  show (PrettyIExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["{", show (PrettyIExpr a), ",", show (PrettyIExpr b), "}"]
    Zero -> "0"
    x -> show x

g2i :: IExpr -> Int
g2i Zero = 0
g2i (Pair a b) = 1 + (g2i a) + (g2i b)
g2i x = error $ "g2i " ++ (show x)

i2g :: Int -> IExpr
i2g 0 = Zero
i2g n = Pair (i2g (n - 1)) Zero

ints2g :: [Int] -> IExpr
ints2g = foldr (\i g -> Pair (i2g i) g) Zero

g2Ints :: IExpr -> [Int]
g2Ints Zero = []
g2Ints (Pair n g) = g2i n : g2Ints g
g2Ints x = error $ "g2Ints " ++ show x

s2g :: String -> IExpr
s2g = ints2g . map ord

g2s :: IExpr -> String
g2s = map chr . g2Ints

-- convention is numbers are left-nested pairs with zero on right
isNum :: IExpr -> Bool
isNum Zero = True
isNum (Pair n Zero) = isNum n
isNum _ = False

lookupTypeEnv :: [a] -> Int -> Maybe a
lookupTypeEnv env ind = if ind < length env then Just (env !! ind) else Nothing

-- State is closure environment, map of unresolved types, unresolved type id supply
type AnnotateState a = State ([PartialType], Map Int PartialType, Int) a

freshVar :: AnnotateState PartialType
freshVar = state $ \(env, typeMap, v) ->
  (TypeVariable v, (TypeVariable v : env, typeMap, v + 1))

popEnvironment :: AnnotateState ()
popEnvironment = state $ \(env, typeMap, v) -> ((), (tail env, typeMap, v))

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
checkOrAssociate x (TypeVariable t) resolvedSet typeMap = case Map.lookup t typeMap of
  Nothing -> pure $ Map.insert t x typeMap
  Just rt -> checkOrAssociate x rt (Set.insert t resolvedSet) typeMap
checkOrAssociate (ArrTypeP a b) (ArrTypeP c d) resolvedSet typeMap =
  checkOrAssociate a c resolvedSet typeMap >>= checkOrAssociate b d resolvedSet
checkOrAssociate a b _ typeMap = if a == b then pure typeMap else Nothing

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = state $ \(env, typeMap, v)
  -> case checkOrAssociate a b Set.empty typeMap of
       Just tm -> ((), (env, tm, v))
       Nothing -> ((), (env, typeMap, v))

-- convert a PartialType to a full type, aborting on circular references
fullyResolve_ :: Set Int -> Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve_ _ _ ZeroTypeP = pure ZeroType
fullyResolve_ resolved typeMap (TypeVariable i) = if Set.member i resolved
  then Nothing
  else Map.lookup i typeMap >>= fullyResolve_ (Set.insert i resolved) typeMap
fullyResolve_ resolved typeMap (ArrTypeP a b) =
  ArrType <$> fullyResolve_ resolved typeMap a <*> fullyResolve_ resolved typeMap b

fullyResolve :: Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve = fullyResolve_ Set.empty

annotate :: IExpr -> AnnotateState (IExprA PartialType)
annotate Zero = pure ZeroA
annotate (Pair a b) = PairA <$> annotate a <*> annotate b
annotate (Var v) = do
  (env, _, _) <- get
  va <- annotate v
  case lookupTypeEnv env $ g2i v of
    Nothing -> pure $ VarA va badType
    Just pt -> pure $ VarA va pt
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
annotate (Anno g t) = if fullCheck t ZeroType
  then do
  ga <- annotate g
  let et = pureEval t
  case unpackPartialType et of
    Nothing -> error "bad type signature eval"
    Just evt -> do
      associateVar (getPartialAnnotation ga) evt
      pure $ AnnoA ga et
  else (`AnnoA` t) <$> annotate g
annotate (Gate x) = GateA <$> annotate x
annotate (PLeft x) = PLeftA <$> annotate x
annotate (PRight x) = PRightA <$> annotate x
annotate (Trace x) = TraceA <$> annotate x

evalTypeCheck :: IExpr -> IExpr -> Bool
evalTypeCheck g t = fullCheck t ZeroType && case unpackType (pureEval t) of
  Just tt -> fullCheck g tt
  Nothing -> False

checkType_ :: Map Int PartialType -> IExprA PartialType -> DataType -> Bool
checkType_ _ ZeroA ZeroType = True
checkType_ typeMap (PairA a b) ZeroType =
  checkType_ typeMap a ZeroType && checkType_ typeMap b ZeroType
checkType_ typeMap (VarA v a) t = case fullyResolve typeMap a of
  Nothing -> False
  Just t2 -> t == t2 && checkType_ typeMap v ZeroType
checkType_ typeMap (AppA g i a) t = fullyResolve typeMap a == Just t &&
  case fullyResolve typeMap (getPartialAnnotation i) of
    Nothing -> False
    Just it -> checkType_ typeMap i it && checkType_ typeMap g (ArrType it t)
checkType_ typeMap (AnnoA g tg) t = packType t == tg && checkType_ typeMap g t
checkType_ typeMap (GateA x) (ArrType ZeroType ZeroType) = checkType_ typeMap x ZeroType
checkType_ typeMap (PLeftA g) ZeroType = checkType_ typeMap g ZeroType
checkType_ typeMap (PRightA g) ZeroType = checkType_ typeMap g ZeroType
checkType_ typeMap (TraceA g) t = checkType_ typeMap g t
checkType_ typeMap (ClosureA l ZeroA a) ct@(ArrType _ ot) =
  case checkOrAssociate a (toPartial ct) Set.empty typeMap of
    Nothing -> False
    Just t -> checkType_ t l ot
checkType_ _ (ClosureA _ _ _) _ = error "TODO - checkType_ filled closure or non arrow type"
checkType_ _ _ _ = False -- error "unmatched rule"

fullCheck :: IExpr -> DataType -> Bool
fullCheck iexpr t =
  let (iexpra, (_, typeMap, _)) = runState (annotate iexpr) ([], Map.empty, 0)
      debugT = trace (concat ["iexpra:\n", show iexpra, "\ntypemap:\n", show typeMap])
  in checkType_ typeMap iexpra t

lookupEnv :: IExpr -> Int -> Maybe IExpr
lookupEnv (Pair i _) 0 = Just i
lookupEnv (Pair _ c) n = lookupEnv c (n - 1)
lookupEnv _ _ = Nothing

{-
iEval :: Monad m => ([Result] -> IExpr -> m Result)
  -> [Result] -> IExpr -> m Result
-}
iEval f env g = let f' = f env in case g of
  Zero -> pure Zero
  Pair a b -> do
    na <- f' a
    nb <- f' b
    pure $ Pair na nb
  Var v -> case lookupEnv env $ g2i v of
    Nothing -> error $ "variable not found " ++ show v
    Just var -> pure var
  Anno c t -> f' c
  App g cexp -> do --- given t, type {{a,t},{a,t}}
    ng <- f' g
    i <- f' cexp
    apply f ng i
  Gate x -> f' x >>= \g -> case g of
    Zero -> pure $ Closure (PLeft (Var Zero)) Zero
    _ -> pure $ Closure (PRight (Var Zero)) Zero
  PLeft g -> f' g >>= \g -> case g of
    (Pair a _) -> pure a
    _ -> pure Zero
  PRight g -> f' g >>= \g -> case g of
    (Pair _ x) -> pure x
    _ -> pure Zero
  Trace g -> f' g >>= \g -> pure $ trace (show g) g
  Closure c Zero -> pure $ Closure c env
  Closure _ e -> fail $ concat ["unexpected closure with environment ", show e]

{-
apply :: Monad m => ([Result] -> IExpr -> m Result) -> Result -> Result -> m Result
-}
apply f (Closure g env) v = f (Pair v env) g
apply _ g _ = error $ "not a closure " ++ show g

toChurch :: Int -> IExpr
toChurch x =
  let inner 0 = Var Zero
      inner x = App (Var $ i2g 1) (inner (x - 1))
  in lam (lam (inner x))

simpleEval :: IExpr -> IO IExpr
simpleEval = fix iEval Zero

pureEval :: IExpr -> IExpr
pureEval g = runIdentity $ fix iEval Zero g

showPass :: Show a => IO a -> IO a
showPass a = a >>= print >> a

tEval :: IExpr -> IO IExpr
tEval = fix (\f e g -> showPass $ iEval f e g) Zero

typedEval :: IExpr -> (IExpr -> IO ()) -> IO ()
typedEval iexpr prettyPrint = if fullCheck iexpr ZeroType
  then simpleEval iexpr >>= prettyPrint
  else putStrLn "failed typecheck"

debugEval :: IExpr -> IO ()
debugEval iexpr = if fullCheck iexpr ZeroType
  then tEval iexpr >>= (print . PrettyIExpr)
  else putStrLn "failed typecheck"

fullEval i = typedEval i print

prettyEval i = typedEval i (print . PrettyIExpr)

evalLoop :: IExpr -> IO ()
evalLoop iexpr = if fullCheck iexpr (ArrType ZeroType ZeroType)
  then let mainLoop s = do
             result <- simpleEval $ App iexpr s
             case result of
               Zero -> putStrLn "aborted"
               (Pair disp newState) -> do
                 putStrLn . g2s $ disp
                 case newState of
                   Zero -> putStrLn "done"
                   _ -> do
                     inp <- s2g <$> getLine
                     mainLoop $ Pair inp newState
               r -> putStrLn $ concat ["runtime error, dumped ", show r]
       in mainLoop Zero
  else putStrLn "failed typecheck"
