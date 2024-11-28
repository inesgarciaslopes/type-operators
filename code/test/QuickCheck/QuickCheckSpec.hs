{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module QuickCheck.QuickCheckSpec 
where

import Test.QuickCheck
import Test.Hspec.QuickCheck
import Syntax
import Rename (rename)
import QuickCheck.ArbitraryTypes ()
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import TypeFormation
import Test.QuickCheck.Random (mkQCGen)
import qualified Data.Maybe as Maybe
import Data.Maybe
import TypeToGrammar (convertToGrammar)
import Normalisation ( red)
import Bisimulation (isBisimilar)
import Debug.Trace
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Test.Hspec
import WeakHeadNormalForm (iswhnf)

nodes :: Type -> Int
nodes (Abs _ _ t) = 1 + nodes t
nodes (App t u) = 1 + nodes t + nodes u
nodes _ = 1

treeStruct :: Type -> Int
treeStruct (Var _) = 1
treeStruct (Abs _ _ t) = treeStruct t
treeStruct (App t u) = treeStruct t + treeStruct u
treeStruct _ = 0

typeConstr :: Type -> String
typeConstr Int = "Int"
typeConstr Arrow{} = "Arrow"
typeConstr (Labelled Record _) = "Record"
typeConstr (Labelled Variant _) = "Variant"
typeConstr Rec{} = "Rec"
typeConstr Quantifier{} = "Quantifier"
typeConstr Skip = "Skip"
typeConstr End{} = "End"
typeConstr Message{} = "Message"
typeConstr Semi = "Semi"
typeConstr Choice{} = "Choice"
typeConstr Dual = "Dual"
typeConstr (Var{}) = "Var"
typeConstr (Abs{}) = "Abs"
typeConstr (App{}) = "App"

-- | Distribution
prop_distribution :: Type -> Type  -> Property
prop_distribution t u = collect (nodes t + nodes u) $ tabulate
    "Type constructors"
    [typeConstr t]
    True

-- main :: IO ()
-- main = do
--   let args = stdArgs {replay = Just (mkQCGen 1095646480, 0)}
--   quickCheckWith args prop_distribution

-- | Rename
prop_rename :: Type -> Bool
prop_rename t = nodes t == nodes (rename Set.empty t)

-- main :: IO ()
-- main = do 
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}
--     quickCheckWith args prop_rename

prop_treeStruct :: Type -> Bool
prop_treeStruct t = treeStruct t == treeStruct (rename Set.empty t)

-- main :: IO ()
-- main = do
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}
--     quickCheckWith args prop_treeStruct


prop_rename_idempotent :: Type -> Property
prop_rename_idempotent t =
  counterexample ("T: " ++ show t ++ " rename: " ++ show (rename Set.empty t) ++ show (rename Set.empty (rename Set.empty t))) $
  rename Set.empty (rename Set.empty t) === rename Set.empty t

-- main :: IO ()
-- main = do 
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0) }
--     quickCheckWith args prop_rename_idempotent

-- t = rename(t) && t -> u implies u = rename(u)
prop_reduction_preserves_renaming :: Type -> Property
prop_reduction_preserves_renaming t =
  t == rename Set.empty t && isJust u ==> Maybe.fromJust u == rename Set.empty (Maybe.fromJust u)
    where u = red t

--Passed only 23464 tests;
-- main :: IO ()
-- main = do
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}
--     quickCheckWith args prop_reduction_preserves_renaming

-- rename(t) = rename(u) implies t == u
prop_renaming_preserves_alpha_congruence :: Type -> Type -> Property
prop_renaming_preserves_alpha_congruence t u =
  rename Set.empty t == rename Set.empty u ==>  t == u

-- 5858 tests;
-- main :: IO ()
-- main = do 
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}
--     quickCheckWith args prop_renaming_preserves_alpha_congruence

prop_renaming_reflects_alpha_congruence :: Type -> Type -> Property
prop_renaming_reflects_alpha_congruence t u =
  t == u ==> rename Set.empty t == rename Set.empty u

-- main :: IO ()
-- main = do 
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}
--     quickCheckWith args prop_renaming_reflects_alpha_congruence

prop_whnf_does_not_reduce :: Type -> Property
prop_whnf_does_not_reduce t =
  counterexample ("T: " ++ show t ++ "reduction T: " ++ show (red t)) $
  iswhnf t ==> isNothing (red t)

-- main :: IO ()
-- main = do
--     let args = stdArgs { maxSuccess = 2000000, replay = Just (mkQCGen 1095646480, 0)}
--     startTime <- getCurrentTime
--     quickCheckWith args prop_whnf_does_not_reduce
--     endTime <- getCurrentTime
--     let elapsedTime = diffUTCTime endTime startTime
--     putStrLn $ "Quick check passed in " ++ show elapsedTime

prop_reduces_implies_not_whnf :: Type -> Property
prop_reduces_implies_not_whnf t =
  --counterexample ("T: " ++ show t ++ "reduction T: " ++ show (red t)) 
  isJust (red t) ==> not (iswhnf t)

--If T type && T -> U then U type
prop_preservation :: Type -> Property
prop_preservation t =
  Maybe.isJust (synthetise Map.empty t) && Maybe.isJust u ==> Maybe.isJust (synthetise Map.empty (Maybe.fromJust u))
  where u = red t

-- main :: IO ()
-- main = do
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}
--     startTime <- getCurrentTime
--     quickCheckWith args prop_preservation
--     endTime <- getCurrentTime
--     let elapsedTime = diffUTCTime endTime startTime
--     putStrLn $ "Quick check passed in " ++ show elapsedTime

-- If |T:kT && T -> U then word(T) ~ word(U)
prop_bisimilar :: Type -> Property
prop_bisimilar t =
  Maybe.isJust (synthetise Map.empty t) && isJust u ==>
    isBisimilar (convertToGrammar [rename Set.empty t, rename Set.empty (Maybe.fromJust u)])
    where u = red (trace (show t ++ "\n" ++ show (red t) ++ "\n") t)

-- main :: IO ()
-- main = do
--     let args = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)}  
--     startTime <- getCurrentTime
--     quickCheckWith args prop_bisimilar
--     endTime <- getCurrentTime
--     let elapsedTime = diffUTCTime endTime startTime
--     putStrLn $ "Quick check passed in " ++ show elapsedTime

-- main :: IO ()
-- main = sample reduceGen

-- main :: IO ()
-- main = sample generatePair --whnfGen 

arg = stdArgs { maxSuccess = 200000, replay = Just (mkQCGen 1095646480, 0)} 

spec :: Spec
spec =
  describe "quickCheck" $
    prop "prop_preservation" $
      {-quickCheckWith  verboseCheckWith -} quickCheckWith arg {- prop_bisimilar -} prop_preservation -- prop_distribution


main = hspec spec
