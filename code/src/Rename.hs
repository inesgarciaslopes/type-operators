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

-- look for alternative
pFirst :: (Bool, Set.Set Variable) -> Bool
pFirst (a, _) = a

pSnd :: (Bool, Set.Set Variable) -> Set.Set Variable
pSnd (_,b) = b

-- | take the set of absorbing vars and returns a set of free and reachable vars. 
reachable :: Set.Set Variable -> Type -> Set.Set Variable
reachable s (Var a) = Set.singleton a
reachable s (Abs x _ t) = Set.delete x (reachable s t)
reachable s (Choice _ m) = Set.unions (map (\(_, t) -> reachable s t) (Map.toList m))
reachable s (App (Rec{}) (Abs x _ t)) = reachable (x `Set.insert` s) t
reachable s (App t u)
    | pFirst (absorbing s t) = reachable s t
    | otherwise = reachable s t `Set.union` reachable s u
reachable _ _ = Set.empty

absorbing :: Set.Set Variable -> Type -> (Bool, Set.Set Variable)
absorbing _ End{} = (True, Set.empty)
absorbing s (App Semi t) = absorbing s t
absorbing s (Choice _ m) =  foldr (join . absorbing s) (True, Set.empty) (Map.elems m)
    where join (bl, sl) (br, sr) = (bl && br, Set.union sl sr)
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
    if a `Set.member` s
        then (True, Set.singleton a)
        else (False, Set.empty)
absorbing s (Abs x _ t) = absorbing (Set.insert x s) t
absorbing s (App (Abs x _ t) u) = absorbing s t'
    where t' = substitution t u x
absorbing _ _ = (False, Set.empty)

rename :: Set.Set Variable -> Type -> Type
rename s u@(Abs a k t) = Abs v k (rename s' (substitution t (Var v) a))
    where s' = if a `Set.member` reachable Set.empty t
                then s `Set.union` reachable Set.empty u
                else Set.empty
          v = first s'
rename s (App t u) = App (rename s' t) (rename s u)
    where s' = s `Set.union` reachable Set.empty (App t u)
rename _ t = t



