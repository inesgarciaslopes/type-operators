module WeakHeadNormalForm
  (
    isVar,
    head,
    isConstant,
    args,
    iswhnf
  )
where

import Syntax
import Prelude hiding (head)

isConstant :: Type -> Bool
isConstant Int = True
isConstant Arrow{} = True
isConstant Labelled{} = True
isConstant Rec{} = True
isConstant Quantifier{} = True
isConstant Skip = True
isConstant End{} = True
isConstant Message{} = True
isConstant Semi = True
isConstant Choice{} = True
isConstant Dual = True
isConstant _ = False

isVar :: Type -> Bool
isVar Var{} = True
isVar _ = False

isSemi :: Type -> Bool
isSemi Semi = True
isSemi _ = False

isDual :: Type -> Bool
isDual Dual = True
isDual _ = False

depth :: Type -> Int
depth (App t _) = 1 + depth t
depth _ = 0

head :: Type -> Type
head (App t _) = head t
head t = t

-- Requires App Type
neck :: Type -> Type
neck (App t u)
  | isConstant t = u
  | otherwise = neck t

args :: Type -> [Type]
args (App w@(App{}) v) = args w ++ [v]
args (App (Var _) t) = [t]
args _ = []

preConst1 :: Type -> Bool
preConst1 Semi = True
preConst1 (Rec _) = True
preConst1 Dual = True
preConst1 _ = False

preSeq2 :: Type -> Bool
preSeq2 (App (App Semi _) _) = True
preSeq2 Skip = True
preSeq2 _ = False

preDual :: Type -> Bool
preDual Skip = True
preDual (Quantifier {}) = True
preDual (End _) = True
preDual (Message _ _) = True
preDual (App (App Semi _) _) = True
preDual (Choice _ _) = True
preDual (App Dual (App (Var _) _)) = True
preDual _ = False

iswhnf :: Type -> Bool
iswhnf (App Semi _) = True -- W-SEQ1
iswhnf Abs{} = True -- W-ABS
iswhnf t =
     isConstant t -- W-CONST0
  || isConstant (head t) && not (preConst1 (head t)) && depth t >= 1 -- W-CONST1
  || isSemi (head t) && iswhnf (neck t) && not (preSeq2 (neck t)) && depth t >= 2 -- W-SEQ2
  || isVar (head t) && depth t >= 0  -- W-VAR
  || isDual (head t) && iswhnf (neck t) && not (preDual (neck t)) && depth t >= 2 -- W-DUAL
