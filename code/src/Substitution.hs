module Substitution 
    (
    substitution,
    freeVars
    )
where

import Syntax
import qualified Data.Set as Set

freeVars :: Type -> Set.Set Variable
freeVars (Var a) = Set.singleton a
freeVars (Abs x _ t) = Set.delete x (freeVars t)
freeVars (App t u) = freeVars t `Set.union` freeVars u
freeVars _ = Set.empty

freshVar :: Set.Set Variable -> Variable
freshVar s = Prelude.head [v | v <- [0..], v `Set.notMember` s]

-- | both types are renamed T [U/a]
substitution :: Type -> Type -> Variable -> Type
substitution Int _ _ = Int
substitution t@Arrow{} _ _ = t
substitution t@Labelled{} _ _= t
substitution t@Rec{} _ _= t
substitution t@Quantifier{} _ _= t
substitution Skip _ _= Skip
substitution t@End{} _ _= t
substitution t@Message{} _ _= t
substitution Semi _ _= Semi
substitution t@Choice{} _ _= t
substitution Dual _ _= Dual 
substitution u@(Var a) t b
    | a == b = t   
    | otherwise = u
substitution w@(Abs a k u) t x 
    | a == x = w
    | a /= x && (x `Set.notMember` freeVars t) = Abs a k (substitution u t x)
    | otherwise = Abs y k (substitution (substitution u (Var y) a) t x) 
        where y = freshVar (freeVars t `Set.union` freeVars u)
substitution (App u v) t x = App (substitution u t x) (substitution v t x)
-- substitution t = t