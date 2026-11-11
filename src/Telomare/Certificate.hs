-- |The static report: everything the compiler knows about a program's
-- recursion without running it.
--
-- Two analyses feed it, and they answer different questions:
--
--   * the sizing pass ("Telomare.Size") says how many times each recursion
--     can iterate. That is the number that makes the program total, and it
--     costs minutes to find.
--   * the structural pass ("Telomare.Levels") says how recursions nest, and
--     which bindings are used below the level they were bound at. That costs
--     milliseconds.
--
-- They are reported together, in one command, but /not/ merged into one table,
-- because they do not index the same thing. Sizing allocates a count per
-- __instantiation__: a `d2c` called from two places is sized separately at
-- each, so @simpleplus.tel@ line 13 holds two sized sites. The structural pass
-- indexes the __triple as written__, so it sees `d2c`'s one `{t, r, b}` where
-- it is defined. Lining the two lists up row by row would be a fiction; the
-- report says so rather than inventing a correspondence.
--
-- The iteration counts are not a new claim. They are the numbers the compiler
-- already bakes into the program, and a program whose counts cannot be found
-- does not compile. The levels are an approximation, and say so.
module Telomare.Certificate
  ( renderStaticReport
  ) where

import qualified Data.Map as Map

import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.Levels (BindingKey, LevelsInfo (..), SiteKey (..), bangs,
                        renderBinding, renderDef, renderLevels, renderSource)
import Telomare.Size (SizingReport (..))
import Telomare.Size.IR (SizedRecursion (..))
import Telomare.Util (padRight, plural)

-- |The whole static report.
--
-- Sizing may be absent — a fast run never sizes — in which case no iteration
-- count is reported rather than a made-up one.
renderStaticReport :: Maybe String -- ^Source hash, when read from an artifact.
                   -> Maybe SizingReport
                   -> Either String LevelsInfo -- ^Levels, or why there are none.
                   -> String
renderStaticReport sourceHash sizing levels = unlines $
  header <> [""] <> sizingSection <> [""] <> structuralSection <> closing
  where
    header =
      "static report: what the compiler knows without running the program"
        : foldMap (\h -> ["source hash: " <> h]) sourceHash

    sizingSection = case sizing of
      Nothing ->
        [ "iterations: not inferred, because this program was not sized."
        , "  Nothing here says it terminates. Compile it without --fast for that." ]
      Just report ->
        ("recursion sites (iterations, over every input):" : sizedRows report)
          <> ["", "sizing budget in force: " <> show (sizingReportBudget report)
                <> " unrollings"]

    structuralSection = case levels of
      Left err -> ["recursion nesting: unavailable (" <> err <> ")"]
      Right info ->
        ("recursion nesting (structural, approximate):" : structuralRows info)
          <> ["", "maximum nesting depth: " <> show (levelsMaxDepth info)]
          <> pressure info

    pressure info
      | null (levelsBangs info) = ["", "no binding is used below the level it was bound at"]
      | otherwise = "" : "bindings used below the level they were bound at:"
          : pressureRows (levelsBangs info)

    closing = [""] <> correspondence <>
      [ "A site at level d has its test, recursion and last one level deeper."
      , "Several levels for one triple mean it is reached from several places."
      , "Levels are structural: a parameter applied as a function whose shape is"
      , "unknown counts as level 0, so a level can be reported too shallow. They"
      , "are not bounds, and not a termination argument -- the counts are."
      ]

    correspondence = case (sizing, levels) of
      (Just _, Right _) ->
        [ "The two lists index differently: a count above is per instantiation (a"
        , "recursion reached from two places is sized separately at each), while a"
        , "row below is one {t, r, b} as written. They do not line up row by row."
        , "" ]
      _ -> []

-- |What sizing found: one row per instantiation, which is what the compiled
-- program actually runs on.
sizedRows :: SizingReport -> [String]
sizedRows report = fmap render counts
  where
    counts = Map.toAscList . unSizedRecursion $ sizingReportCounts report
    render (tok, size) = "  " <> padRight width (place tok) <> "  <= " <> maybe "?" show size
    place tok =
      let named = "#" <> show (unUnsizedRecursionToken tok)
      in case Map.lookup tok (sizingReportLocs report) >>= renderLocTagCompact of
           Just spot -> spot <> " (" <> named <> ")"
           Nothing   -> named
    width = maximum (0 : fmap (length . place . fst) counts)

-- |What the structural pass found: one row per written triple.
structuralRows :: LevelsInfo -> [String]
structuralRows info
  | null rows = ["  none reachable from the entry point"]
  | otherwise = fmap ("  " <>) (render headings : fmap render rows)
  where
    headings = ("triple", "function", "levels")
    rows = [ (renderSource (siteSource site), renderDef (siteOwner site), renderLevels lvls)
           | (site, lvls) <- levelsSites info ]
    width sel = maximum (fmap (length . sel) (headings : rows))
    (w1, w2) = (width fst3, width snd3)
    fst3 (a, _, _) = a
    snd3 (_, b, _) = b
    -- the +2 is the column gutter
    render (a, b, c) = padRight (w1 + 2) a <> padRight (w2 + 2) b <> c

pressureRows :: [(BindingKey, Int)] -> [String]
pressureRows rows = fmap render rows
  where
    width = maximum (fmap (length . renderBinding . fst) rows)
    render (binding, k) =
      let name = renderBinding binding
      in "  " <> padRight (width + 2) name -- the +2 is the column gutter
           <> bangs k <> "  (" <> show k <> " " <> plural "level" k <> " below its binding)"
