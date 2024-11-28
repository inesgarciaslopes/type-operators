{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Rename
    (rename,
    used, --testing only
    absorbing) --testing only
where

import Syntax
import Substitution
import Normalisation
import qualified Data.Set as Set

first :: Set.Set Variable -> Variable
first s = Prelude.head $ filter (`Set.notMember` s) [0..]

-- | freeST
-- used :: Type -> Set.Set Variable
--   -- Functional Types
-- used (Arrow _ _ t u) = used t `Set.union` used u
-- used (Labelled _ _ m) =
--   Map.foldr (\t acc -> used t `Set.union` acc) Set.empty m
--   -- Session Types
-- used (Semi _ t u)
--   | absorbing Set.empty t = used t
--   | otherwise = used t `Set.union` used u
-- used (Message _ _ t) = used t 
--   -- Polymorphism and recursive types
-- used (Forall _ (Bind _ a _ t)) = Set.delete a (used t)
-- used (Rec _ (Bind _ a _ t)) = Set.delete a (used t)
-- used (Var _ a) = Set.singleton a
--   -- Type operators
-- used (Dualof _ t) = used t
--   --Int, Float, Char, String, Skip, End
-- used _ = Set.empty 

-- | The set of type variables used in a type 
used :: Type -> Set.Set Variable
used (Var a) = Set.singleton a
used (Abs x _ t) = Set.delete x (used t)
-- used (App (App Rec{} (Abs x k t)) u) 
--     | absorbing Set.empty t = 
used (App (App Semi t) u)
    | absorbing Set.empty t = used t
    | otherwise = used t `Set.union` used u
used (App t u)  = used t `Set.union` used u
used _ = Set.empty

-- | FreeST
-- absorbing :: Set.Set Variable -> Type -> Bool
-- absorbing _ End{} = True
-- absorbing trefs (Labelled _ Choice{} m) =
--   all (absorbing trefs) (Map.elems m)
-- absorbing trefs (Semi _ t u) =
--   absorbing trefs t || absorbing trefs u
-- -- absorbing (Forall _ (Bind _ a _ t)) = Set.delete a (absorbing t) -- Not a session type do far
-- absorbing trefs (Rec _ (Bind _ a _ t)) = absorbing (Set.insert a trefs) t
-- absorbing trefs (Var _ a) = a `Set.member` trefs
-- absorbing trefs (Dualof _ t) = absorbing trefs t
-- absorbing _ _ = False

-- absorbing T implies T is a session type
absorbing :: Set.Set Variable -> Type -> Bool
absorbing _ End{} = True
absorbing s (App (App Semi t) u) = absorbing s t || absorbing s u
absorbing s (App (Rec{}) t) = absorbing s t
absorbing s (App (Quantifier{}) t) = absorbing s t
absorbing s (App Dual t) = absorbing s t
absorbing s (Var a) = a `Set.member` s
absorbing s (Abs x _ t) = absorbing (Set.insert x s) t
absorbing s w@(App _ _) =
    case weaknorm Set.empty w of
        Just w' -> absorbing s w'
        Nothing -> False
absorbing _ _ = False

rename :: Set.Set Variable  -> Type -> Type
rename _ (Var a) = Var a
rename s u@(Abs a k t) = Abs v k (rename s (substitution t (Var v) a))
    where s' = s `Set.union` used u
          v = first s'
rename s (App t u ) = App (rename s' t) (rename s u)
    where s' = s `Set.union` used u
rename _ t = t

-- minimal :: Type -> Type
-- minimal = minimal' Set.empty

-- minimal' :: Set.Set Variable -> Type -> Type
--   -- Functional Types
-- minimal' set (Arrow s m t u) =
--   Arrow s m (minimal' set t) (minimal' set u)
--   -- Arrow s m (minimal' (set `Set.union` used u) t) (minimal' set u)
-- minimal' set (Labelled s k m) =
--   Labelled s k (Map.map (minimal' set) m)
--   -- Session Types
-- minimal' set (Semi s t u) =
--   Semi s (minimal' (set `Set.union` used u) t) (minimal' set u)
-- minimal' set (Message s p t) =
--   Message s p (minimal' set t)
--   -- Polymorphism and recursive types
-- minimal' set t@(Forall s1 (Bind s2 a k u)) =
--   Forall s1 (Bind s2 b k (minimal' set (subs vb a u)))
--     where b = first (set `Set.union` used t) -- mkNewVar (first t) a
--           vb = Var (getSpan b) b
-- minimal' set (Rec s1 (Bind s2 a k t))
--   | a `isFreeIn` t = Rec s1 (Bind s2 a k (minimal' set t))
--   -- Required by the current translation to grammar. Otherwise:
--   -- uncaught exception: PatternMatchFail
--   --  src/Bisimulation/TypeToGrammar.hs:130:3-39: Non-exhaustive patterns in z : zs  
--   | otherwise = minimal' set t
--   -- Type operators
-- minimal' set (Dualof s t) =
--   Dualof s (minimal' set t)
--   -- Int, Float, Char, String, Skip, End, Var
-- minimal' _ t = t



