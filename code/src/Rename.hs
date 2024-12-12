{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Rename
    (rename,
    reachable, --testing only
    absorbing) --testing only
where

import Syntax
import Substitution
import Normalisation
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

first :: Set.Set Variable -> Variable
first s = Prelude.head $ filter (`Set.notMember` s) [0..]

-- | take the set of absorbing vars and returns a set of free and reachable vars. 
reachable :: Set.Set Variable -> Type -> Set.Set Variable
reachable s (Var a) = Set.delete a s
reachable s (Abs x _ t) = Set.delete x (reachable s t)
--reachable s (Choice _ m) = Set.unions (map (\(_, t) -> reachable s t) (Map.toList m))
reachable s (App (Rec{}) (Abs x _ t)) = reachable (x `Set.insert` s) t
reachable s (App t u)
    | pFirst (absorbing s t) = reachable s t
    | otherwise = reachable s t `Set.union` reachable s u
reachable _ _ = Set.empty

pFirst :: (Bool, Set.Set Variable) -> Bool
pFirst (a, _) = a

pSnd :: (Bool, Set.Set Variable) -> Set.Set Variable
pSnd (_,b) = b

--absorbing T implies T is a session type
-- absorbing :: Set.Set Variable -> Type -> Bool
-- absorbing _ End{} = True
-- absorbing s (App Semi t) = absorbing s t
-- absorbing s (Choice _ m) = all (absorbing s ) (Map.elems m)
-- absorbing s (App (App Semi t) u) = absorbing s t || absorbing s u
-- absorbing s (App (Rec{}) (Abs x _ t)) = absorbing (Set.insert x s) t
-- absorbing s (App (Rec{}) t) = absorbing s t
-- absorbing s (App (Quantifier{}) (Abs x _ t)) = absorbing s' t
--     where s' = Set.delete x s
-- absorbing s (App (Quantifier{}) t) = absorbing s t
-- absorbing s (App Dual t) = absorbing s t
-- absorbing s (Var a) = a `Set.member` s
-- absorbing s (Abs x _ t) = absorbing (Set.insert x s) t
-- -- absorbing s w@(App _ _) =
-- --     case weaknorm Set.empty w of
-- --         Just w' -> absorbing s w'
-- --         Nothing -> False
-- absorbing s (App (Abs x _ t) u) = absorbing s t' 
--     where t' = substitution t u x 
-- absorbing _ _ = False

absorbing :: Set.Set Variable -> Type -> (Bool, Set.Set Variable)
absorbing _ End{} = (True, Set.empty)
absorbing s (App Semi t) = absorbing s t
-- absorbing s (Choice _ m) = undefined
absorbing s (App (App Semi t) u) =
    let (bl, sl) = absorbing s t in
    if bl then (bl, sl) else absorbing s u
absorbing s (App (Rec{}) (Abs x _ t)) = absorbing (Set.insert x s) t
absorbing s (App (Rec{}) t) = absorbing s t
absorbing s (App (Quantifier{}) (Abs x _ t)) = absorbing s' t
    where s' = Set.delete x s
absorbing s (App (Quantifier{}) t) = absorbing s t
absorbing s (App Dual t) = absorbing s t
absorbing s (Var a) =
    if a `Set.member` s then (True, Set.singleton a) else (False, Set.empty)
absorbing s (Abs x _ t) = absorbing (Set.insert x s) t
absorbing s (App (Abs x _ t) u) = absorbing s t'
    where t' = substitution t u x
absorbing _ _ = (False, Set.empty)

rename :: Set.Set Variable -> Type -> Type
rename s u@(Abs a k t) = Abs v k (substitution t (Var v) a )
    -- | a `Set.member` reachable s t = Abs v k (substitution t (Var v) a)
    -- | otherwise = Abs 0 k (substitution t (Var 0) a)
    where s' = s `Set.union` reachable s u
          v = first s'
rename s (App t u) = App (rename s' t) (rename s u)
    where s' = s `Set.union` reachable s (App t u)
    --where s' = s `Set.union` reachable u
rename _ t = t



