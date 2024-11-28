{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Bisimulation 
 ( isBisimilar
  )where

-- import Bisimilarity.BisimilarityPresets ()

import Data.Foldable ()
import Data.Function (on)
import Data.List (sortBy)
import Data.Map.Strict  as Map (empty, insert, lookup, keysSet, findWithDefault, filterWithKey, fromList, assocs)
import Data.Ord (comparing)
import Data.Sequence  as Seq
import Data.Set  as Set (empty, Set, insert, toList, filter)
import Grammar 
import Prelude hiding (Word, log)
import Syntax
import Control.Monad
import Control.Monad.State
import CongruenceModule
import TypeToGrammar ()
import Rename ()
--------------------------------------------------------------------------------------------------------------------------------------
-- Main Function
-- Function that verifies if two words are bisimilar
isBisimilar :: Grammar -> Bool
isBisimilar (Grammar [[],[]] _) = True
isBisimilar (Grammar [[],ys] _) = False
isBisimilar (Grammar [xs,[]] _) = False
isBisimilar g@(Grammar [xs,ys] _) = do evalState (basisUpdating tree [] Set.empty) initState
  where
    node = (xs, ys)
    root = Node {nodeValue = node, parentNode = Nothing }
    tree = Seq.fromList [root]
    b = createBasisForVariables g
    initState = TState {basis = b, visitedPairs = Set.empty, normMap = Map.empty, grammar = g, log = []}

-- Basis updating algorithm, used as a auxiliary function of isBidimilar
basisUpdating :: BranchQueue -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
basisUpdating bq track bpa2Mark = do
  b <- gets basis
  g <- gets grammar
  case Seq.viewl bq of
    Seq.EmptyL -> return True -- caso base, toda a branchQueue percorrida
    node'@(Node { nodeValue = ws'@(x',y'), parentNode = ancestor' }) Seq.:< rest -> do
      node@(Node { nodeValue = ws@(x,y), parentNode = ancestor }) <- case ancestor' of
                                                                          Nothing -> do
                                                                            node'' <- pruneNode node'
                                                                            (orderNode node'')
                                                                          _ -> return node'
       {-(ws@(x, y), ancestors@(ancestor,_))-}
      visited <- gets visitedPairs
      if ws `elem` visited || (y,x) `elem` visited || x == y -- 4.1 e 4.2
        then do
          basisUpdating rest track bpa2Mark
        else do
          let newVisitedPairs = Set.insert ws visited
          replaceVisitedPairs newVisitedPairs
          w1Norm <- normUsingMap Set.empty x
          w2Norm <- normUsingMap Set.empty y
          if w1Norm /= w2Norm -- 4.3
            then do
              partialFail node track rest bpa2Mark



            else checkIfInBasis node rest bq track bpa2Mark

pruneNode :: Node -> GlobalState Node
pruneNode  node@(Node { nodeValue = ws@(x',y'), parentNode = ancestor }) = do
  x <- pruneWord  x'
  y <- pruneWord  y'
  return (Node { nodeValue = (x,y), parentNode = ancestor })

pruneWord :: Word -> GlobalState Word
pruneWord  [] = return []
pruneWord  (x:xs) = do
  normed <- normUsingMap Set.empty [x]
  case normed of
    Nothing -> return [x]
    Just _ ->do
      rest <- pruneWord  xs
      return (x : rest)

partialFail :: Branch -> [(Variable, Variable)] -> BranchQueue -> Set.Set (Variable, Variable) -> GlobalState Bool
partialFail node@(Node { nodeValue = ws@(x,y), parentNode = ancestor }) track rest bpa2Mark = do

  case ancestor of
    (Nothing) -> return False -- caso root Total failure

    Just w@((Node { nodeValue = nodeValue@(x',y'), parentNode = ancestor' }))-> do
      b <- gets basis
      if isBPA1Guess nodeValue b
        then do
          nA1 <- normUsingMap Set.empty (x')
          nA2 <- normUsingMap Set.empty (y')
          case (nA1,nA2) of
            (Nothing, Nothing) -> do
              updateBpa2Pair node track rest bpa2Mark -- partial failure
            _ -> do
              b <- gets basis
              let newB = Map.insert (head (x'), head (y')) (Bpa2 (tail (x'), tail (y'))) b
              replaceBasis newB
              partialFail w track rest bpa2Mark
        else do
          partialFail w track rest bpa2Mark

isBPA1Guess :: (Word, Word) -> Basis -> Bool
isBPA1Guess  (x,y) b =
  case Map.lookup (head x, head y) b of
    Just (Bpa1 _) -> True
    _ -> False



checkIfInBasis :: Branch -> BranchQueue -> BranchQueue -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
checkIfInBasis node@(Node { nodeValue = nodeValue@(x',y'), parentNode = ancestor' }) rest bq track bpa2Mark = do
  b <- gets basis

  case Map.lookup (head x', head y') b of -- caso Variaveis na basis
    Just (Bpa1 w) -> do
      -- 4.4

      addChildrenToBranchQueue node rest  track bpa2Mark
    Just (Bpa2 (w1, w2)) -> do
      -- 4.5
      addChildrenToBranchQueue node rest  track bpa2Mark
    Nothing ->
      checkChildren node rest bq track bpa2Mark

checkChildren :: Branch -> BranchQueue -> BranchQueue -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
checkChildren node@(Node { nodeValue = nodeValue@(x,y), parentNode = ancestor' }) rest bq track bpa2Mark = do
  g <- gets grammar
  if matchTransitions g (head x) (head y)
    then do

      let xNorm = norm g (head x)
          yNorm = norm g (head y)
      case (xNorm, yNorm) of
        (Nothing, Nothing) -> do
          -- 4.7
          addMatchingTransitions node rest [] track bpa2Mark
        (Nothing, Just _) -> do
          -- 4.8
          if isNormed g (tail y)
            then do
              updateBpa2Pair node track bq bpa2Mark -- ver bq or rest
            else do
              addMatchingTransitions node rest (tail y) track bpa2Mark
        (Just nx, Just ny) -> do
          -- 4.9

          handleBpaMarks node rest bq track bpa2Mark
    else return False -- total failure 4.6

handleBpaMarks :: Branch -> BranchQueue -> BranchQueue -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
handleBpaMarks node@(Node { nodeValue = nodeValue@(x,y), parentNode = ancestor' }) rest bq track bpa2Mark = do
  w1Norm <- normUsingMap Set.empty x
  w2Norm <- normUsingMap Set.empty y
  if (head x, head y) `elem` bpa2Mark
    then do
      case (w1Norm, w2Norm) of
        (Nothing, Nothing) -> do
          addPairBpa2ToBasis node rest (tail x, tail y) track bpa2Mark
        _ -> do
          updateBpa2Pair node track bq bpa2Mark
    else do
      beta <- calculateBeta ([head x], [head y])
      case beta of
        Just w -> do
          addPairBpa1ToBasis node rest w track bpa2Mark
        _ -> do
          let newBpa2Mark = Set.insert (head x, head y) bpa2Mark
          case (w1Norm, w2Norm) of
            (Nothing, Nothing) -> do
              addPairBpa2ToBasis node rest (tail x, tail y) track newBpa2Mark
            _ ->
              updateBpa2Pair node track bq newBpa2Mark

enqueuePrunedNode :: Node -> BranchQueue -> (Word, Word) -> GlobalState BranchQueue
enqueuePrunedNode  parentNode queue tuple = do
  prunedNode <- pruneNode  (Node {nodeValue = tuple, parentNode = Just parentNode})
  return $ enqueue prunedNode queue

addChildrenToBranchQueue :: Node -> BranchQueue -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
addChildrenToBranchQueue node@(Node { nodeValue = nodeValue@(x',y'), parentNode = ancestor' }) rest  track bpa2Mark = do
  g <- gets grammar
  b <- gets basis
  let nodes = applyRules b nodeValue
  children <- mapM (orderPairsByNorm ) nodes
  newBQ <- foldM (enqueuePrunedNode  node) rest children
  basisUpdating newBQ track bpa2Mark

addMatchingTransitions :: Node -> BranchQueue -> Word -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
addMatchingTransitions node@(Node { nodeValue = nodeValue@(x,y), parentNode = ancestor }) rest bpa1Word track bpa2Mark = do
  b <- gets basis
  g <- gets grammar
  let newB = Map.insert (head x, head y) (Bpa1 bpa1Word) b
      newTrack = (head x, head y) : track
  children <-if bpa1Word == []
    then getChildren  node
    else do
        childs <- getChildren  node
        modifyNode [] (bpa1Word) childs
  orderedChildren <- mapM orderNode children
  let newBQ = orderedChildren >< rest

  replaceBasis newB
  basisUpdating newBQ newTrack bpa2Mark

orderNode:: Node -> GlobalState Node
orderNode node@(Node { nodeValue = nodeValue, parentNode = ancestor' }) = do
  nodeValue2 <- orderPairsByNorm nodeValue
  return (Node { nodeValue = nodeValue2 , parentNode = ancestor' })



addPairBpa1ToBasis :: Node -> BranchQueue -> Word -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
addPairBpa1ToBasis node@(Node { nodeValue = nodeValue@(x,y), parentNode = ancestor' }) rest bpa1Word track bpa2Mark = do
  b <- gets basis
  g <- gets grammar
  let newB = Map.insert (head x, head y) (Bpa1 bpa1Word) b
      newTrack = (head x, head y) : track
  children <- getChildren  node
  bq'' <- addBetaToPair bpa1Word g (children)
  orderedBq'' <- mapM orderNode bq''
  let bq' = orderedBq'' >< rest
      nodes = applyRules newB nodeValue
  bpa1Children <- mapM (orderPairsByNorm ) nodes
  newBQ <- foldM (enqueuePrunedNode  node) bq' bpa1Children
  replaceBasis newB
  basisUpdating newBQ newTrack bpa2Mark


addBetaToPair:: Word -> Grammar -> BranchQueue ->GlobalState BranchQueue
addBetaToPair x g bq =  traverse (pruneNode  . addToSecond x) bq

addToSecond :: Word -> Node -> Node
addToSecond x node = Node
  { nodeValue = (fst (nodeValue node), snd (nodeValue node) ++ x),
    parentNode = fmap (addToSecond x) (parentNode node)
  }

addPairBpa2ToBasis :: Node -> BranchQueue -> (Word, Word) -> [(Variable, Variable)] -> Set.Set (Variable, Variable) -> GlobalState Bool
addPairBpa2ToBasis node@(Node { nodeValue = nodeValue@(x,y), parentNode = ancestor' }) rest bpa2Word track bpa2Mark = do
  b <- gets basis
  g <- gets grammar
  children <- getChildren  node
  let newB = Map.insert (head x, head y) (Bpa2 bpa2Word) b
      newTrack = (head x, head y) : track
      newBQ' = children >< rest
  newBQ <-  modifyNode  (tail x) (tail y) newBQ'
  replaceBasis newB
  basisUpdating newBQ newTrack bpa2Mark

orderPairsByNorm :: (Word, Word) -> GlobalState (Word, Word)
orderPairsByNorm  ([], ys) = return (ys, [])
orderPairsByNorm  (xs, []) = return (xs, [])
orderPairsByNorm  (v1@(x : xs), v2@(y : ys)) = do
  norm_v1 <- normUsingMap Set.empty [x]
  norm_v2 <- normUsingMap Set.empty [y]
  return $ case (norm_v1,norm_v2) of
    (Nothing, _) -> (v1, v2)
    (_, Nothing) -> (v2, v1)
    (Just n1, Just n2)
      | n1 > n2 -> (v1, v2)
      | n2 > n1 -> (v2, v1)
      | x <= y -> (v1, v2)
      | otherwise -> (v2, v1)
    

getChildren :: Node ->GlobalState BranchQueue
getChildren  node@(Node {nodeValue = nodeValue@(x:xs,y:ys), parentNode = _}) = do
  g@(Grammar _ prods) <- gets grammar
  let transitions1 = transitions x prods
      transitions2 = transitions y prods
      commonLabels = Map.keysSet transitions1
      commonWords = Data.List.sortBy (comparing fst) [(label, (Map.findWithDefault [] label transitions1, Map.findWithDefault [] label transitions2)) | label <- Set.toList commonLabels]
  foldM (\acc (_, pair) -> enqueuePrunedNode node acc pair) Seq.empty commonWords
  --updatedQueue = foldlM (\acc (_, pair) -> enqueuePrunedNode g node acc pair) Seq.empty commonWords



modifyNode :: Word -> Word -> BranchQueue -> GlobalState BranchQueue
modifyNode  xs ys =  mapM modifyAndPrune
  where
    modifyAndPrune :: Node -> GlobalState Node
    modifyAndPrune node@(Node { nodeValue = nodeValue, parentNode = ancestor }) = do
      g <- gets grammar
      newValue <- modifySet g xs ys nodeValue
      pruneNode  (Node { nodeValue = newValue, parentNode = ancestor })
  --fmap (\node@(Node {nodeValue = nodeValue, parentNode = ancestor}) -> pruneNode g (Node {nodeValue =   modifySet g xs ys nodeValue, parentNode = ancestor}))

modifySet :: Grammar -> Word -> Word -> (Word,Word) -> GlobalState (Word,Word)
modifySet g xs' ys' (w1, w2) = orderPairsByNorm (w1 ++ xs', w2 ++ ys')

enqueue :: Branch -> BranchQueue -> BranchQueue
enqueue element queue
  | element `elem` queue = queue -- Se o elemento já estiver na fila, apenas retorne a fila original
  | otherwise = element Seq.<| queue -- Caso contrário, adicione o elemento à frente da fila

updateBpa2Pair :: Node -> [(Variable, Variable)] -> BranchQueue -> Set.Set (Variable, Variable) -> GlobalState Bool
updateBpa2Pair node@(Node {nodeValue = _, parentNode = Nothing}) _ _ _ = return False
updateBpa2Pair node@(Node {nodeValue = _, parentNode = Just ancestor@(Node {nodeValue = nodeValue@(x:xs,y:ys) , parentNode = ancestor'})}) track bq bpa2Mark = do
  g <- gets grammar
  children <- getChildren ancestor
  let
      newTrack = dropWhile (/= (x, y)) track
      bq' = filterBranchQueue node bq
  newBQ <- modifyNode  xs ys (children >< bq')
  updateBasis nodeValue newTrack
  basisUpdating newBQ newTrack bpa2Mark

filterBranchQueue :: Node -> BranchQueue -> BranchQueue
filterBranchQueue x = Seq.filter (\node -> maybeNotEqual (parentNode node) (parentNode x))
  where
    maybeNotEqual :: Maybe Node -> Maybe Node -> Bool
    maybeNotEqual Nothing Nothing = False  -- Caso especial: ambos são Nothing, então são considerados iguais
    maybeNotEqual (Just _) Nothing = True -- Um tem valor e o outro não
    maybeNotEqual Nothing (Just _) = True -- Um tem valor e o outro não
    maybeNotEqual (Just node1) (Just node2) = node1 /= node2  -- Ambos têm valor, então comparamos os nós








updateBasis :: (Word, Word) -> [(Variable, Variable)] -> GlobalState ()
updateBasis ancestor@(x : xs, y : ys) track = do
  b <- gets basis
  visited <- gets visitedPairs
  let b' = filterBasis track b
      newVisited = filterSet track visited
      newB = Map.insert (x, y) (Bpa2 (xs, ys)) b'
  replaceVisitedPairs newVisited
  replaceBasis newB

filterBasis :: [(Variable, Variable)] -> Basis -> Basis
filterBasis filterKeys = Map.filterWithKey (\key _ -> key `elem` filterKeys || uncurry (==) key)

startsWith :: (Variable, Variable) -> (Word, Word) -> Bool
startsWith _ ([], []) = False
startsWith _ ([], _) = False
startsWith _ (_, []) = False
startsWith (k1, k2) (x : _, y : _) = k1 == x && k2 == y

filterSet :: [(Variable, Variable)] -> Set.Set (Word, Word) -> Set.Set (Word, Word)
filterSet filterKeys = Set.filter (\(x, y) -> any (\(k1, k2) -> startsWith (k1, k2) (x, y)) filterKeys)

compareTransitions :: Transitions -> Transitions -> Bool
compareTransitions trans1 trans2 =
  let labels1 = Map.keysSet trans1
      labels2 = Map.keysSet trans2
   in labels1 == labels2

checkWords :: Word -> Word -> Bool
checkWords [] [] = True
checkWords [] _ = False
checkWords _ [] = False
checkWords _ _ = True

matchTransitions :: Grammar -> Variable -> Variable -> Bool
matchTransitions (Grammar _ productions) var1 var2 =
  let transitions1 = transitions var1 productions
      transitions2 = transitions var2 productions
   in compareTransitions transitions1 transitions2

createBasisForVariables :: Grammar -> Basis
createBasisForVariables g = Map.fromList $ map (\v -> ((v, v), Bpa1 [])) (Set.toList $ nonterminals g)

calculateBeta :: (Word, Word) -> GlobalState (Maybe Word)
calculateBeta (x : xs, y : ys) = do
  normX <- normUsingMap Set.empty [x]
  normY <- normUsingMap Set.empty [y]
  case (normX, normY) of
    (Just nX, Just nY) -> do
      (Grammar _ p) <- gets grammar
      map <- gets normMap
      let transX = transitions x p
          transY = transitions y p
          toVisitX = Data.List.sortBy (compare `on` fst) $ Map.assocs transX
          toVisitY = Data.List.sortBy (compare `on` fst) $ Map.assocs transY
      toVisit <- filterTuples2 toVisitX toVisitY map (nX, nY) (xs,ys)
      case toVisit of
        Just (word1, []) -> return (Just (word1))
        Just (word1, word2) -> calculateBeta (word1, word2)
        Nothing -> return Nothing
    _ -> return Nothing

filterTuples2 :: (Eq a, Ord a) => [(a, Word)] -> [(a, Word)] -> NormMap -> (Int, Int) -> (Word, Word) ->GlobalState (Maybe (Word, Word))
filterTuples2 _ [] _ _ _= return Nothing
filterTuples2 [] _ _ _ _= return Nothing
filterTuples2 ((label, word1) : rest1) list2 map (nX, nY) (xs,ys)=
  case findMatchingWord label word1 list2 of
    Just word2 -> do
      word1Norm <- normUsingMap Set.empty word1
      word2Norm <- normUsingMap Set.empty word2
      case (word1Norm,word2Norm) of
        (Just x, Just y) ->
          if reducesNorm nX (x) && reducesNorm nY (y)
            then return (Just (word1++xs, word2++ys))
            else filterTuples2 rest1 list2 map (nX, nY) (xs,ys)
        _-> filterTuples2 rest1 list2 map (nX, nY) (xs,ys)
    Nothing -> filterTuples2 rest1 list2 map (nX, nY) (xs,ys)

findMatchingWord :: Eq a => a -> Word -> [(a, Word)] -> Maybe Word
findMatchingWord _ _ [] = Nothing
findMatchingWord label word ((label2, word2) : rest)
  | label == label2 = Just word2
  | otherwise = findMatchingWord label word rest

{-
main :: IO ()
main = do

    let b = createBasisForVariables g1
        node = orderPairsByNorm g1  (["X", "C"],["Y", "C"])
        root = Node {nodeValue = node, parentNode = Nothing }
        tree = Seq.fromList [root]
        initState = TState { basis = b, visitedPairs = Set.empty, normMap = Map.empty, grammar = g1, log = [] }
        (result, newState) = runState (basisUpdating tree [] Set.empty ) initState
        fullLog = evalState getFullLog newState
    putStrLn "Full Log:"
    mapM_ putStrLn fullLog
    print result
    print (norm g1 ["X"])
-}