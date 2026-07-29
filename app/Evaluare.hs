{-# LANGUAGE RecursiveDo #-}

module Main where

import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Exception as Exception
import Control.Monad
import Control.Monad.Fix (MonadFix)
import Data.Bifunctor (bimap, first, second)
import Data.Either (fromLeft)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Zipper as TZ
import qualified Graphics.Vty as V
import PrettyPrint (PrettyCompiledExpr (..))
import Reflex
import Reflex.Vty
import System.Environment (getArgs)
import qualified System.IO.Strict as Strict
import qualified Telomare as Tel
import Telomare (AUPT, AnnotatedUPT (..), BasicExprF (..), CompiledExpr,
                 CompiledExprF (..), StuckF (..))
import qualified Telomare.Eval as TE
import Telomare.Parser (parseModule)
import Text.Read (readMaybe)

type VtyExample t m =
  ( MonadFix m
  , MonadHold t m
  , Reflex t
  , HasInput t m
  , HasImageWriter t m
  , HasDisplayRegion t m
  , HasFocus t m
  , HasFocusReader t m
  , HasTheme t m
  )

type Manager t m =
  ( HasLayout t m
  , HasFocus t m
  )

data Node = Node
  { _node_label    :: Text
  , _node_eval     :: Text
  , _node_selected :: Bool
  }
  deriving (Show, Eq)

data NodeOutput t = NodeOutput
  { _nodeOutput_node   :: Dynamic t Node
  , _nodeOutput_expand :: Event t Bool
  }

node :: forall t m. ( VtyExample t m
                    , HasLayout t m
                    , HasInput t m
                    , HasImageWriter t m
                    )
     => Node
     -> m (NodeOutput t)
node n0 = do
  row $ do
    tile ( fixed . pure . (+1) . T.length . _node_label $ n0) $ do
      grout flex . text . pure . _node_label $ n0
      pure ()
    value :: Dynamic t Bool <- tile (fixed 4) . checkbox def $ _node_selected n0
    pure $ NodeOutput
      { _nodeOutput_node = Node (_node_label n0) (_node_eval n0) <$> value
      , _nodeOutput_expand = updated value
      }

nodes :: forall t m.
         ( MonadHold t m
         , Manager t m
         , VtyExample t m
         , Adjustable t m
         , PostBuild t m
         )
      => [Node]
      -> m (Event t Text)
nodes nodes0 = do
  let nodeMaps0 = Map.fromList $ zip [0..] nodes0
  rec
    listOut :: Dynamic t (Map Int (NodeOutput t))
      <- listHoldWithKey nodeMaps0 updates $ \_ v -> grout (fixed 1) $ node v
    let expandedEvalText :: Event t (Int, Text)
        expandedEvalText = switchDyn $
            leftmost
          . Map.elems
          . Map.mapWithKey (\k -> fmap ((k,) . _node_eval)
                                . updated
                                . _nodeOutput_node)
          <$> listOut
        nodesMap :: Dynamic t (Map Int Node)
        nodesMap = joinDynThroughMap $ fmap _nodeOutput_node <$> listOut
        updates :: Event t (Map Int (Maybe Node))
        updates = justOneChecked <@> (fst <$> expandedEvalText)
        justOneChecked :: Behavior t (Int -> Map Int (Maybe Node))
        justOneChecked = current $
          (\n i -> Map.mapWithKey (\k n' -> if k == i
                                            then Just n' {_node_selected = True}
                                            else Just n' {_node_selected = False})
                                  n
          ) <$> nodesMap
  pure $ snd <$> expandedEvalText

nodeList :: ( VtyExample t m
            , Manager t m
            , MonadHold t m
            , Adjustable t m
            , PostBuild t m
            , HasInput t m
            )
         => Event t Text -> [Node] -> m (Event t Text)
nodeList e nodes0 = col $ do
  grout (fixed 1) $ text ""
  et <- grout flex $ nodes nodes0
  pure $ leftmost [e, et]

nodify :: Cofree CompiledExprF (Int, CompiledExpr) -> [Node]
nodify = removeExtraNumbers . fmap go . allNodes 0 where
  removeExtraNumbers :: [Node] -> [Node]
  removeExtraNumbers = \case
    [] -> []
    (x:xs) -> case (readMaybe . T.unpack . _node_label $ x) :: Maybe Int of
                Nothing -> x : removeExtraNumbers xs
                Just i  -> x : removeExtraNumbers (drop (2 * i) xs)
  go :: (Int, Cofree CompiledExprF (Int, CompiledExpr)) -> Node
  go (i, x@(anno :< _)) =
    Node ( T.pack
         . (join (replicate i "  ") <>)
         . head
         . lines
         . show
         . PrettyCompiledExpr
         . Tel.forget
         $ x
         )
         ( T.pack
         . (join (replicate i "  ") <>)
         . (show . PrettyCompiledExpr)
         . snd
         $ anno
         )
         False
  allNodes :: Int -- * Indentation
           -> Cofree CompiledExprF (Int, CompiledExpr)
           -> [(Int, Cofree CompiledExprF (Int, CompiledExpr))]
  allNodes i = \case
    x@(_ :< CompiledExprB ZeroSF) -> [(i, x)]
    x@(_ :< CompiledExprS EnvSF) -> [(i, x)]
    x@(_ :< CompiledExprS GateSF) -> [(i, x)]
    x@(_ :< CompiledExprS (SetEnvSF a)) -> (i, x) : allNodes (i + 1) a
    x@(_ :< CompiledExprS (DeferSF _ a)) -> (i, x) : allNodes (i + 1) a
    x@(_ :< CompiledExprS (LeftSF a)) -> (i, x) : allNodes (i + 1) a
    x@(_ :< CompiledExprS (RightSF a)) -> (i, x) : allNodes (i + 1) a
    x@(_ :< CompiledExprB (PairSF a b)) -> (i, x) : allNodes (i + 1) a <> allNodes (i + 1) b
    x -> [(i, x)]


-- parseModule :: String -> Either String [Either AnnotatedUPT (String, AnnotatedUPT)]
-- TODO: Load modules qualifed
loadModules :: [String] -> IO [(String, [Either AUPT (String, AUPT)])]
loadModules filenames = do
  filesStrings :: [String] <- mapM Strict.readFile filenames
  case mapM parseModule filesStrings of
    Right p -> pure $ zip filesStrings (fmap convertModule p)
    Left pe -> error pe
  where
    convertModule = fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))

mainWidgetInit
  :: (forall t m.
       ( MonadVtyApp t m
       , HasImageWriter t m
       , MonadNodeId m
       , HasDisplayRegion t m
       , HasFocusReader t m
       , HasTheme t m
       , HasInput t m
       ) => Layout t (Focus t m) (Event t ()))
  -> IO ()
mainWidgetInit w = mainWidget (initManager_ w)

main :: IO ()
main = do
  modules :: [(String, [Either AUPT (String, AUPT)])] <- getArgs >>= loadModules
  let go :: Text -> IO ()
      go textErr =
        mainWidgetInit $ do
          let cfg = def
                { _textInputConfig_initialValue = TZ.fromText . T.pack . unlines $
                    [ "-- Example:"
                    , "(\\x -> 0) 8"
                    ]
                }
              textBox = boxTitle (pure roundedBoxStyle) "Telomare" $
                multilineTextInput cfg
              escOrCtrlcQuit :: (Monad m, HasInput t m, Reflex t) => m (Event t ())
              escOrCtrlcQuit = do
                inp <- input
                pure . fforMaybe inp $ \case
                  V.EvKey (V.KChar 'c') [V.MCtrl] -> Just ()
                  V.EvKey V.KEsc []               -> Just ()
                  _                               -> Nothing
          getout <- escOrCtrlcQuit
          tile flex . box (pure roundedBoxStyle) . row $ do
            rec
              eEitherIExpr :: Event t (Either String CompiledExpr) <- grout flex . col $ do
                telomareTextInput :: TextInput t <- grout flex textBox
                pure . updated $ TE.eval2IExpr modules . T.unpack <$> _textInput_value telomareTextInput
              grout (fixed 2) . col . text $ ""
              let -- telomareNodes :: Event t (Either String [Node])
                  telomareNodes = fmap (nodify . TE.tagIExprWithEval) <$> eEitherIExpr
                  fromRightWith :: (a -> b) -> Either a b -> b
                  fromRightWith f = \case
                    Left x -> f x
                    Right x -> x
              (_, eEventEval :: Event t (Either String (Event t Text)))
                <- runWithReplace (grout flex . col . text $
                                    if T.length textErr > 0
                                    then constant ("\nOops, something went wrong:\n\n" <> textErr <> "\n")
                                    else ""
                                      <>
                                    "\nWrite some Telomare code and interact with the generated AST")
                                  (mapM (nodeList (fromLeft ("Select a node to evaluate" :: Text) . first T.pack <$> eEitherIExpr)) <$> telomareNodes)
              et :: Event t Text <- switchHold (T.pack . fromLeft "woooooot99" <$> eEitherIExpr)
                                               (fromRightWith (\str -> T.pack str <$ telomareNodes) <$> eEventEval)
              bt <- hold "\nSelect nodes from the center pane and that'll evaluate here" $ ("\n" <>) . T.dropWhile (== ' ') <$> et
              grout flex . col . text $ bt
            pure ()
          pure $ void getout
  res :: Either Exception.SomeException () <- Exception.try $ go ""
  case res of
    Left err -> go . T.pack . show $ err
    Right _  -> pure ()
