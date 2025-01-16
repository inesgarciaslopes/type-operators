{-# LANGUAGE LambdaCase #-}
module Syntax (
  Type(..)
  , LabelMap
  , Polarity(..)
  , Sort(..)
  , View(..)
  , Variable
  , Kind(..)
  , BaseKind(..)
  , dual
  )
where
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type Variable = Int

type LabelMap = Map.Map Variable Type

data Polarity = Out | In deriving (Ord, Eq)

data View = External | Internal deriving (Ord, Eq)

data Sort = Record | Variant  deriving (Ord, Eq)

-- Kinds
data BaseKind = Session | Top deriving (Ord, Eq)

data Kind = ProperK BaseKind
          | ArrowK Kind Kind
          deriving (Ord, Eq)

-- Types
data Type =
    Int
  | Arrow BaseKind BaseKind
  | Labelled Sort LabelMap -- record, variant
  | Rec BaseKind -- μ a:k . T, Recursive type
  | Quantifier Polarity Kind Kind -- ∀k . T, Universal type (Out) and ∃k. T Existencial type (In)
  | Skip
  | End Polarity
  | Message Polarity BaseKind
  | Semi  -- Seq. composition 
  | Choice View LabelMap -- choice operator
  | Dual  -- dual operator
  | Var Variable -- type variable
  | Abs Variable Kind Type -- type-level abstraction
  | App Type Type -- type-level application
  deriving (Ord)

instance Show View where
  show External = "&"
  show Internal = "+"

instance Show Type where
  show = \case 
    Int -> "Int"
    Arrow bk1 bk2 -> "(->@" ++ show bk1 ++ "@" ++ show bk2++")"
    Labelled s lts -> l ++ showLabelMap lts ++ r
      where (l,r) = case s of Variant -> ("<",">"); Record -> ("{","}")
    Rec bk -> "μ@" ++ show bk
    Quantifier p k1 k2 ->  q ++ "@" ++ show k1 ++ "@" ++ show k2
      where q = case p of Out -> "∀"; In -> "∃"
    Skip -> "Skip"
    End Out -> "Close"
    End In -> "Wait"
    Message p _ -> "("++show p++")"
    Semi -> "(;)"
    Choice v lts -> show v ++ "{" ++ showLabelMap lts ++ "}"
    Dual -> "Dual"
    Var v -> show v
    Abs v k t -> "(λ" ++ show v ++ ":" ++ show k ++ ". " ++ show t++")"
    App t1 t2 -> "(" ++ show t1 ++ " " ++ show t2 ++ ")"
    where 
      showLabelMap = Map.foldrWithKey (\l t s -> show l ++ ": " ++ show t ++ if null s then "" else ", "++s) ""

instance Show Polarity where
  show In  = "?"
  show Out = "!"

instance Show BaseKind where
  show Top = "T"
  show Session = "S"

instance Show Kind where
  show (ProperK k) = show k
  show (ArrowK k1 k2) = "("++show k1 ++ " => " ++ show k2++")"

-- Duality 
class Dual a where
  dual :: a -> a

instance Dual Polarity where
  dual Out = In
  dual In = Out

instance Dual View where
  dual External = Internal
  dual Internal = External

-- == alpha congruent
type VarMap = Set.Set (Variable, Variable)

class Equiv t where
  alphaCongruent :: VarMap -> t -> t -> Bool

instance Eq Type where
  t == u = alphaCongruent Set.empty t u

instance Equiv Type where
  alphaCongruent _ Int Int = True
  alphaCongruent _ (Arrow k1 k2) (Arrow k1' k2') = k1 == k1' && k2 == k2'
  alphaCongruent vm (Labelled s1 m1) (Labelled s2 m2) = 
    s1 == s2 && 
    Map.size m1 == Map.size m2 &&
    Map.isSubmapOfBy (alphaCongruent vm) m1 m2
  alphaCongruent _ (Rec k1) (Rec k2) = k1 == k2
  alphaCongruent _ (Quantifier p1 k1 k2) (Quantifier p2 k1' k2') =
    k1 == k1' && k2 == k2' && p1 == p2
  alphaCongruent _ Skip Skip = True
  alphaCongruent _ (End p1) (End p2) = p1 == p2
  alphaCongruent _ (Message p1 k1) (Message p2 k2) = p1 == p2 && k1 == k2
  alphaCongruent _ Semi Semi = True
  alphaCongruent _ (Choice v1 m1) (Choice v2 m2) =
    v1 == v2 && Map.size m1 == Map.size m2
  alphaCongruent _ Dual Dual = True
  alphaCongruent vm (Var v1) (Var v2) = Set.member (v1,v2) vm
  alphaCongruent vm (Abs v k t) (Abs v2 k2 t2) = 
    k == k2 && alphaCongruent vm' t t2 
      where vm' = Set.insert (v,v2) vm
  alphaCongruent vm (App t1 t2) (App t1' t2') = alphaCongruent vm t1 t1' && alphaCongruent vm t2 t2'
  alphaCongruent _ _ _ = False