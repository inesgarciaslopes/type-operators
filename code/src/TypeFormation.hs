{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TypeFormation (
    synthetise,
    preSynthetise -- tests only
    )
    where

import Syntax
import Normalisation ( norm )
import qualified Data.Map.Strict as Map

type KindingCtx = Map.Map Variable Kind

synthetise :: KindingCtx -> Type -> Maybe Kind
synthetise c t = do
  k <- preSynthetise c t
  boolToMaybe (valid t) k

-- pre kind
preSynthetise :: KindingCtx -> Type -> Maybe Kind
preSynthetise _ Int = Just (ProperK Top)
preSynthetise _ (Arrow k1 k2) =
  Just (ArrowK (ProperK k1) (ArrowK (ProperK k2) (ProperK Top)))
preSynthetise ctx (Labelled _ m) =
  boolToMaybe (and $ Map.map (\t -> checkAgainst ctx (ProperK Top) t || checkAgainst ctx (ProperK Session) t) m) (ProperK Top)
preSynthetise _ (Rec k) =
  Just (ArrowK (ArrowK (ProperK k) (ProperK k)) (ProperK k))
preSynthetise _ Skip =
  Just (ProperK Session)
preSynthetise _ (End _) =
  Just (ProperK Session)
preSynthetise _ (Message _ k) =
  Just (ArrowK (ProperK k) (ProperK Session))
preSynthetise _ Semi =
  Just (ArrowK (ProperK Session) (ArrowK (ProperK Session) (ProperK Session)))
preSynthetise ctx (Choice _ m) = 
  boolToMaybe ( and $ Map.map (checkAgainst ctx (ProperK Session)) m) (ProperK Session)
preSynthetise _ Dual =
  Just (ArrowK (ProperK Session) (ProperK Session))
preSynthetise ctx (Var a) =
  Map.lookup a ctx -- K-var
preSynthetise ctx (Abs x k t) = do
  k' <- preSynthetise (Map.insert x k ctx) t
  Just (ArrowK k k')
preSynthetise ctx (App t u) = do
    k <- preSynthetise ctx t
    k1' <- preSynthetise ctx u
    case k of
        ArrowK k1 k2 | k1 == k1' -> Just k2
        _ -> Nothing
preSynthetise _ _ = Nothing

checkAgainst :: KindingCtx -> Kind -> Type -> Bool
checkAgainst ctx expected t =
  preSynthetise ctx t == Just expected

valid :: Type -> Bool
valid (Abs _ _ t) = valid t
valid w@(App t u) = norm w && valid t && valid u
valid _ = True

-- | Retain object when tag is 'True'.
-- | https://hackage.haskell.org/package/Agda-2.6.4.3/docs/src/Agda.Utils.Maybe.html#boolToMaybe
boolToMaybe :: Bool -> a -> Maybe a
boolToMaybe b x = if b then Just x else Nothing

