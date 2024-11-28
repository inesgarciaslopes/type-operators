module UnitTests.SpecUtils
  ( module Test.Hspec
  , module Data.List.Split
  , readFromFile
  )
where

import Test.Hspec
import Syntax
import Rename (rename)
import qualified Data.Set as Set
import WeakHeadNormalForm (iswhnf, args)
import qualified Data.Map.Strict as Map
import TypeFormation
import qualified Data.Maybe as Maybe
import Data.Maybe
import TypeToGrammar (word, convertToGrammar)
import Control.Exception (evaluate)
import Normalisation (norm, red)
import Bisimulation (isBisimilar)
import Debug.Trace
import Data.Char
import Data.List.Split ( chunksOf )
--import State      ( Errors )
--import Error
-- import Debug.Trace

readFromFile :: FilePath -> IO [String]
readFromFile filename = do
  str <- readFile filename
  return
    $ filter (not . isComment)
    $ filter (not . null)
    $ map (dropWhile isSpace)
    $ lines str
  where
    isComment ('-' : '-' : _) = True
    isComment _               = False

