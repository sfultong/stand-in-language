-- | The Telomare modules test programs are loaded against: the Prelude, and
-- ChurchArith, which keeps Church-numeral arithmetic out of the Prelude
-- while the tests still exercise it.
module TestModules
  ( churchArithPath
  , libraryModules
  , auxImports
  ) where

import qualified System.IO.Strict as Strict

churchArithPath :: FilePath
churchArithPath = "test/programs/ChurchArith.tel"

-- |Each library module's name and source.
libraryModules :: IO [(String, String)]
libraryModules = do
  prelude <- Strict.readFile "Prelude.tel"
  church <- Strict.readFile churchArithPath
  pure [("Prelude", prelude), ("ChurchArith", church)]

-- |The imports put in front of an inline test program. They share one line,
-- so source locations in the program are off by exactly one line.
auxImports :: String
auxImports = "import Prelude import ChurchArith\n"
