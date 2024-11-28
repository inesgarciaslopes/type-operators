module UnitTests.SingleTestSpec where

import Syntax
import Rename
import Bisimulation
import TypeToGrammar
import UnitTests.SpecUtils
import qualified Data.Set as Set
import Control.Monad.IO.Class (liftIO)
import Test.HUnit.Lang (assertFailure)
import Read


matchSpec :: [String] -> Spec
matchSpec [t, u, r] = do
    runIO $ do
        putStrLn $ "t': " ++ show t'
        putStrLn $ "u': " ++ show u'
        --putStrLn $ "Grammar: " ++ show (convertToGrammar [t', u'])
    it (t ++ " ~ " ++ u) $
      isBisimilar (convertToGrammar [t', u']) `shouldBe` read r
      where
        t' = rename Set.empty (read t :: Type)
        u' = rename Set.empty (read u :: Type)


spec :: Spec
spec = describe "Test" $ do
  contents <- runIO $ readFromFile "test/UnitTests/SingleTest.txt"
  -- runIO $ putStrLn $ "File contents: " ++ show contents
  mapM_ (matchSpec) $ chunksOf 3 contents

main :: IO ()
main = hspec spec 
