{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Rename
    (rename,
    reachable, --testing only
    absorbing,
    first) --testing only
where

import Syntax
import Substitution
import Normalisation
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

first :: Set.Set Variable -> Variable
first s = Prelude.head $ filter (`Set.notMember` s) [0..]

-- | returns the set of free and reachable vars of the type with regards to a set of potentialy absorbing variables.
reachable :: Set.Set Variable -> Type -> Set.Set Variable
reachable s (Var a) 
    | a `Set.member` s = Set.empty
    | otherwise = Set.singleton a
reachable s (Abs x _ t) = Set.delete x (reachable s t)
reachable s (Choice _ m) = Set.unions (map (\(_, t) -> reachable s t) (Map.toList m))
reachable s (App Rec{} (Abs x _ t)) = reachable (x `Set.insert` s) t
reachable s (App t u)
    | absorbing s t = reachable s t
    | otherwise = reachable s t `Set.union` reachable s u
reachable _ _ = Set.empty

absorbing :: Set.Set Variable -> Type -> Bool
absorbing _ End{} = True
absorbing s (App Semi t) = absorbing s t
absorbing s (Choice _ m) =  foldr (join . absorbing s) True (Map.elems m)
    where join bl br = bl && br
absorbing s (App (App Semi t) u) = absorbing s t || absorbing s u
    -- let (bl, sl) = absorbing s t in
    -- if bl then (bl, sl) else absorbing s u
absorbing s (App Rec{} (Abs x _ t)) = absorbing (Set.insert x s) t
absorbing s (App Rec{} t) = absorbing s t
absorbing s (App Quantifier{} (Abs x _ t)) = absorbing (Set.delete x s) t
absorbing s (App Quantifier{} t) = absorbing s t
absorbing s (App Dual t) = absorbing s t
absorbing s (Var a) = a `Set.member` s
absorbing s (Abs x _ t) = absorbing (Set.insert x s) t
absorbing s (App (Abs x _ t) u) = absorbing s (substitution t u x)
absorbing _ _ = False

rename :: Set.Set Variable -> Type -> Type
rename s u@(Abs a k t) = Abs v k (rename s' (substitution t (Var v) a))
    where s' = if a `Set.member` reachable Set.empty t
                then s `Set.union` reachable Set.empty u
                else Set.empty
          v = first s'
rename s w@(App t u) = App (rename s' t) (rename s u)
    where s' = s `Set.union` reachable Set.empty w
rename _ t = t



