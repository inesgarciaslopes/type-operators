{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Normalisation (
    norm,
    weaknorm,
    red,
    reduceBSD
    )
where
import Syntax
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe as Maybe
import Substitution
import qualified Data.Map.Strict as Map
import Control.Applicative ((<|>))
import WeakHeadNormalForm (isVar, head)
import Prelude hiding (head)

reduceBSD :: Type -> Maybe Type
reduceBSD (App (App Semi Skip) t ) = Just t --R-SEQ1
reduceBSD (App Dual Skip) = Just Skip -- R-DSKIP
reduceBSD (App Dual (End p))= Just (End (dual p)) -- R-DEnd
reduceBSD (App Dual (Message p k)) = Just (Message (dual p) k)
reduceBSD (App Dual (Quantifier p k1 k2)) = Just (Quantifier (dual p) k1 k2) -- Dual (Forall T) -> Exists T && Dual (Exists) -> Forall
reduceBSD (App Dual (App Dual t)) | isVar (head t) = Just t -- R-DDVAR, Modify
--reduceBSD (App Dual (App Dual w@(Var _))) = Just w
reduceBSD (App (Abs x _ t) u) = -- r-beta
    Just (substitution t u x)
reduceBSD (App Dual (Choice v m))= Just (Choice (dual v) m')
        where m' = Map.map (App Dual) m
reduceBSD (App (App Semi (App (App Semi t) u)) v) =
    Just (App (App Semi t) (App (App Semi u) v)) -- R-ASSOC
reduceBSD (App (App Semi t) u) = do --r-seq2
    t' <- reduceBSD t
    Just (App (App Semi t') u)
reduceBSD (App Dual (App (App Semi t) u)) =
    Just (App (App Semi (App Dual t)) (App Dual u)) --R-D;
reduceBSD (App Dual (App Dual t)) = Just t --R-DDual
reduceBSD (App Dual t) = do --r-dctx
    t' <- reduceBSD t
    Just (App Dual t')
reduceBSD (App t v) = do
    t' <- reduceBSD t
    Just (App t' v)
reduceBSD _ = Nothing

reduceMu :: Type -> Maybe Type
reduceMu u@(App (Rec _) t) = -- R-mu
  Just (App t u)
reduceMu (App (App Semi u@(App (Rec _) t)) v) =  -- R-seq2-mu
    Just (App (App Semi (App t u)) v)
reduceMu (App Dual u@(App (Rec _) t)) = -- R-dctx-mu
    Just (App Dual (App t u))
reduceMu (App (App Semi (App Dual u@(App (Rec _) t))) v) = -- ???
    Just (App (App Semi (App Dual (App t u))) v)
reduceMu _ = Nothing

red :: Type -> Maybe Type
red t = reduceBSD t <|> reduceMu t

type MuSet = Set Type -- only contains mu types

-- Does a type reduce to a whnf?
norm :: Type -> Bool
norm t = Maybe.isJust (weaknorm Set.empty t)

weaknorm :: MuSet -> Type -> Maybe Type
weaknorm visited t = 
  case reduceBSD t of
    Just t' -> weaknorm visited t'
    Nothing -> case t of
      (App (Rec _) _) -> weaknorm' visited t
      (App (App Semi u@(App (Rec _) _)) _) -> weaknorm' visited u
      (App Dual u@(App (Rec _) _)) -> weaknorm' visited u
      (App (App Semi (App Dual u@(App (Rec _) _))) _) -> weaknorm' visited u
      _ -> Just t
  where
    weaknorm' s t
      | t `Set.member` s = Nothing -- been here before
      | otherwise = 
        case reduceMu t of
          Just t' -> weaknorm (Set.insert t s) t'
          Nothing -> Just t
