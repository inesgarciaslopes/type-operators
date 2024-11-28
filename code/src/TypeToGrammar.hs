{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module TypeToGrammar
  ( word,
    convertToGrammar
  )
where
import Syntax
import Grammar
import Normalisation
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import Prelude hiding (head, Word)
import WeakHeadNormalForm
import qualified Data.Map.Strict as Map
import Control.Monad
import Control.Monad.State
    ( gets, modify, runState, MonadState(get), State )
import Debug.Trace

type TransState = State BState
type Visited = Map.Map Type Variable

data BState = BState {
    productions  :: Productions
  , nextIndex    :: Int
  , visited :: Visited
  }

-- "⊥"
bottom :: Variable
bottom = -1

initial :: BState
initial = BState {
    productions  = Map.empty
  , nextIndex    = 1
  , visited = Map.empty
  }

freshNonTerminal :: TransState Variable
freshNonTerminal = do
  s <- get
  let n = nextIndex s
  modify $ \s -> s { nextIndex = n + 1 }
  return n

getProductions :: TransState Productions
getProductions = gets productions

getTransitions :: Variable -> TransState Transitions
getTransitions x = do
  ps <- getProductions
  return $ ps Map.! x

getVisited :: TransState Visited
getVisited = gets visited

putProductions :: Variable -> Transitions -> TransState ()
putProductions x m =
  modify $ \s -> s { productions = Map.insert x m (productions s) }

putVisited :: Type -> Variable -> TransState ()
putVisited t v =
    modify $ \s -> s {visited = Map.insert t v (visited s)}

addProductions :: Type -> Transitions -> TransState Variable
addProductions t ts = do
  v <- getVisited
  case v Map.!? t  of
    Nothing -> do
      y <- freshNonTerminal
      putProductions y ts
      return y
    Just y -> return y

convertToGrammar :: [Type] -> Grammar
convertToGrammar ts = Grammar w prods
  where
    (w, s) = runState (mapM word ts) initial
    prods         = productions s

word :: Type -> TransState Word
word  t
    | iswhnf t = wordWhnf t
    | normToSkip t = return []
    | otherwise = do
        v <- getVisited
        case v Map.!? t of
          Just y -> return [y]
          Nothing -> do
            let u = Maybe.fromJust (weaknorm Set.empty t)
            y <- freshNonTerminal
            putVisited t y
            ~(z:delta) <- word u
            gamma <- getTransitions z
            _ <- putProductions y (Map.map (++ delta) gamma)
            putVisited t y
            return [y]

normToSkip :: Type -> Bool
normToSkip t = Maybe.fromJust (weaknorm Set.empty t) == Skip

-- put in whnf.hs 
isSkipEnd :: Type -> Bool
isSkipEnd Skip = True
isSkipEnd End{} = True
isSkipEnd _ = False

-- put in whnf.hs
isArrowChoiceRecord :: Type -> Bool
isArrowChoiceRecord Arrow{} = True
-- isArrowChoiceRecord Quantifier{} = True
isArrowChoiceRecord Choice{} = True
isArrowChoiceRecord Labelled{} = True
isArrowChoiceRecord _ = False

-- Requires whnf t
wordWhnf :: Type -> TransState Word
wordWhnf t = do
  v <- getVisited 
  if Map.member t v then return $ [v Map.! t] else wordWhnf' t

wordWhnf' :: Type -> TransState Word
wordWhnf' Skip = return [] -- Skip
wordWhnf' t@(End p) = do -- Wait and Close
    y <- addProductions t (Map.singleton (show p) [bottom])
    --gets productions >>= traceM . show
    putVisited t y
    return [y] --3
wordWhnf' u@(App (Message p _) t) = do -- #T
    w <- word t
    y <- addProductions u (Map.fromList [(show p ++ "_l1", w ++ [bottom]), (show p ++ "_l2", [])])
    putVisited u y
    return [y]
wordWhnf' u@(Abs a k t) = do -- \\a:k.T
    w <- word t
    y <- addProductions u (Map.singleton ("\\" ++ show a ++ ":"++ show k) w)
    --gets productions >>= traceM . show
    putVisited u y
    return [y]
wordWhnf' u@(App (Quantifier p k1 _) t) = do
    w <- word t
    y <- addProductions u (Map.fromList [(show p ++ show k1 ++ "_l1", w ++ [bottom]), (show p ++ show k1 ++ "_l2", [])])
    putVisited u y
    return [y]
wordWhnf' u@(App Semi t) = do -- ;T
    w <- word t
    y <- addProductions u (Map.singleton ";1" w)
    putVisited u y
    return [y]
wordWhnf' (App (App Semi t) u) = do
    w <- word t
    w' <- word u
    return (w ++ w') -- T;U
wordWhnf' u@(App Dual t) = do -- Dual (T)
    w <- word t
    y <- addProductions u (Map.fromList [(show (head t) ++ "_l1", w), (show (head t) ++ "_l2", [])])
    --gets productions >>= traceM . show
    putVisited u y
    return [y] 
wordWhnf' t
    | isVar (head t) = do -- alpha T1...Tm
        ps <- forM (zip [(0::Int)..] $ args t) $ \(j, arg) -> do
            w <- word arg
            return (show (head t) ++ show j, w ++ [bottom])
        y <- addProductions t (Map.fromList ((show (head t) ++ "_0", []):ps))
        putVisited t y
        return [y]
    | isConstant (head t) && not (isSkipEnd (head t)) = do -- iota, iota != Skip, Wait, Close
        y <- addProductions t (Map.singleton (show t) []) 
        putVisited t y
        return [y]
    | isArrowChoiceRecord (head t) = do -- iota T1...Tm, iota = ->, Choice, Records
        ps <- forM (zip [(0::Int)..] $ args t) $ \(j, arg) -> do
            w <- word arg
            return (show (head t) ++ show j, w ++ [bottom])
        y <- addProductions t (Map.fromList ps)
        putVisited t y
        return [y] 
