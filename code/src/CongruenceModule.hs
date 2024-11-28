module CongruenceModule 
 (applyRules)
 where

import Control.Monad.State (State, evalState, gets, modify)
import Data.List (isPrefixOf, nub)
import Data.Map.Strict as Map (empty, lookup)
import Data.Set as Set (empty, Set, union, fromList)
import Prelude hiding (Word)
import Grammar
import Syntax

type VisitedState = State VisitedStateData

newtype VisitedStateData = CState
  { visitedP :: Set.Set (Word, Word)
  }

addVisitedVariable :: Set.Set (Word, Word) -> VisitedState ()
addVisitedVariable w = modify (\s -> s {visitedP = Set.union w (visitedP s)})

----------------------------------------------------------------------------------------------------------
-- Check if two words are coinductive congruents
isCongruent :: Basis -> Word -> Word -> Bool
isCongruent _ [] [] = True -- Base case: ε-Ax
isCongruent basis word1 word2 = evalState (isCongruentAux3 basis word1 word2) initState
  where
    initState = CState {visitedP = Set.empty}

isCongruentAux3 :: Basis -> Word -> Word -> VisitedState Bool
isCongruentAux3 _ [] [] = return True
isCongruentAux3 _ _ [] = return False
isCongruentAux3 _ [] _ = return False
isCongruentAux3 basis word1 word2 = do
  let pair = (word1, word2)
      (cutW1, cutW2) = cutWord pair
  visited <- gets visitedP
  if (cutW1, cutW2) `elem` visited || (cutW2, cutW1) `elem` visited || (null cutW1 && null cutW2)
    then return True
    else do
      addVisitedVariable (Set.fromList [(cutW1, cutW2)])
      let x = applyRules basis (cutW1, cutW2)
      if null x
        then do
          let y = applyRules basis (cutW2, cutW1)
          tryRules basis y
        else do
          tryRules basis x

{- outra versao, mais estruturada mas menos eficiente em alguns casos
else do
      addVisitedVariable [(word1, word2), (cutW1, cutW2)]
      let rules1 = applyRules basis (cutW1, cutW2)
      let rules2 = applyRules basis (cutW2, cutW1)
      tryRules basis (if null rules1 then rules2 else rules1)
-}

tryRules :: Basis -> [(Word, Word)] -> VisitedState Bool
tryRules b y = do
  case y of
    [] -> return False
    [(x, y)] -> isCongruentAux3 b x y
    [(x1, y1), (x2, y2)] -> do
      r1 <- isCongruentAux3 b x1 y1
      r2 <- isCongruentAux3 b x2 y2
      return (r1 && r2)

applyRules :: Basis -> (Word, Word) -> [(Word, Word)]
applyRules b ([], _) = []
applyRules b (_, []) = []
applyRules b (x : xs, y : ys) =
  case Map.lookup (x, y) b of
    Just (Bpa1 ws) -> [(ws ++ xs, ys)]
    Just (Bpa2 (ws1, ws2)) -> [(ws1, xs), (ws2, ys)]
    Nothing -> []

-----------------------------------------------------------------------------------------------------------
-- Extra Functions

-- Auxiliary function that cuts the first equal variables of two words
cutWord :: (Word, Word) -> (Word, Word)
cutWord ([], w2) = ([], w2)
cutWord (w1, []) = (w1, [])
cutWord (w : ws, x : xs)
  | x == w = cutWord (ws, xs)
  | otherwise = (w : ws, x : xs)
