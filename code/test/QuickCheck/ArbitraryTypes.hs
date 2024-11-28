{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module QuickCheck.ArbitraryTypes
where

import Test.QuickCheck
import Control.Monad ()
import qualified Data.Map.Strict as Map
import Syntax


variable :: [Int]
variable = [1, 2, 3]

-- choices ["A", "B"]

instance Arbitrary Polarity where
  arbitrary = elements [Out, In]

instance Arbitrary View where
  arbitrary = elements [External, Internal]

instance Arbitrary Sort where
  arbitrary = elements [Record, Variant]

  -- | Kinds
instance Arbitrary BaseKind where
  arbitrary = frequency [(1, return Session), (2, return Top)]
  --arbitrary = elements $ Session : replicate 2 Top

instance Arbitrary Kind where
  arbitrary = sized $ \n -> do
    k <- arbitrary
    case n of
      0 -> return $ ProperK k
      _ -> do
        k1 <- resize (n `div` 2) arbitrary
        k2 <- resize (n `div` 2) arbitrary
        return $ ArrowK k1 k2

 -- | Type Generator
instance Arbitrary Type where
  arbitrary = sized $ \n -> do
    frequency [(1, arbitraryConstant),
                      (1, arbitraryVariable),
                      (3, arbitraryAbs n),
                      (1, arbitraryApp n)]
    where
      arbitraryConstant = frequency [
        (1, return Int),
        (1, Arrow <$> arbitrary <*> arbitrary),
        (1, Labelled <$> arbitrary <*> labelMap),
        (4, Rec <$> arbitrary),
        (1, Quantifier <$> arbitrary <*> arbitrary <*> arbitrary),
        (1, return Skip),
        (1, End <$> arbitrary),
        (1, Message <$> arbitrary <*> arbitrary),
        (4, return Semi),
        (1, Choice <$> arbitrary <*> labelMap),
        (1, return Dual)
        ]
      arbitraryVariable = do
        v <- choose (1, 4) --range v [1..4]
        return $ Var v
      arbitraryAbs n = do
        v <- choose (1, 4)
        k <- arbitrary
        t <- resize (n `div` 2) arbitrary
        return $ Abs v k t
      arbitraryApp n = do
        t1 <- resize (n `div` 2) arbitrary
        t2 <- resize (n `div` 2) arbitrary
        return $ App t1 t2

-- | Type operator Generator
-- instance Arbitrary Constant where
--   arbitrary = frequency [
--       (1, return Int),
--       (1, return Arrow),
--       (1, Labelled <$> arbitrary <*> labelMap),
--       (4, Rec <$> arbitrary),
--       (1, Forall <$> arbitrary),
--       (1, return Skip),
--       (1, End <$> arbitrary),
--       (1, Message <$> arbitrary),
--       (4, return Semi),
--       (1, Choice <$> arbitrary <*> labelMap),
--       (1, return Dual)
--     ]

generatePair :: Gen (Type, Type)
generatePair = do
    t1 <- arbitrary
    t2 <- arbitrary
    return (t1, t2)

-- | generating weak head normal form Types

-- newtype WhnfType = WhnfType Type

-- instance Show WhnfType where
--   show t = show t ++ " is a weak head normal form."

-- instance Arbitrary WhnfType where
--   arbitrary = WhnfType <$> whnfGen

-- whnfGen :: Gen Type
-- whnfGen = sized $ \n -> do
--     frequency [(1, arbitraryConstant),
--                (1, arbitraryAbs n),
--                (1, appSemi),
--                (1, whnfVariable n),
--                (6, whnfConst n),
--                (1, whnfSeq2 n)]
--     where
--       arbitraryConstant = Constant <$> arbitrary
--       appSemi = do
--         App Semi <$> arbitrary
--       arbitraryAbs n = do
--         v <- choose (1, 4)
--         k <- arbitrary
--         t <- resize (n `div` 2) arbitrary
--         return $ Abs v k t
--       whnfVariable n = do
--         v <- choose (1, 4)
--         t <- resize (n `div` 2) arbitrary
--         return $ App (Var v) t
--       whnfConst n = do
--         o <- const1
--         t <- resize (n `div` 2) arbitrary
--         return $ App o t
--       whnfSeq2 n = do
--         t1 <- seq2
--         t <- resize (n `div` 2) arbitrary
--         return $ App (App (Constant Semi) t1) t

-- const1 :: Gen Type
-- const1 = oneof [opInt, opArrow, opLabelled, opForall,
--                 opEnd,opSkip, opMessage]
-- seq2 :: Gen Type
-- seq2 = oneof [opInt, opArrow, opLabelled, opForall,
--               opEnd, opMessage, opChoice, opDual]

-- opInt :: Gen Type
-- opInt = pure Int

-- opArrow :: Gen Type
-- opArrow = pure Arrow

-- opLabelled :: Gen Type
-- opLabelled = do
--   s <- arbitrary
--   Labelled s <$> labelMap

-- opRec :: Gen Type
-- opRec = do  Rec <$> arbitrary

-- opForall :: Gen Type
-- opForall = do Quantifier <$> arbitrary <*> arbitrary

-- opSkip :: Gen Type
-- opSkip = pure Skip

-- opEnd :: Gen Type
-- opEnd = do End <$> arbitrary

-- opMessage :: Gen Type
-- opMessage = do Message <$> arbitrary

-- opSemi :: Gen Type
-- opSemi = pure Semi

-- opChoice :: Gen Type
-- opChoice = do
--   v <- arbitrary
--   Choice v <$> labelMap

-- opDual :: Gen Type
-- opDual = pure Dual

-- -- | generating types that reduce

-- newtype RedType = RedType Type

-- instance Show RedType where
--   show t = show t ++ " reduces to another type."

-- instance Arbitrary RedType where
--   arbitrary = RedType <$> reduceGen

-- reduceGen :: Gen Type
-- reduceGen = sized $ \n -> do
--     frequency [(1, rseq1),
--                (1, rmu),
--                (1, rdSkip),
--                (1, rdWait),
--                (15, rdClose),
--                (1, rdout),
--                (1, rdin),
--                (1, rdext),
--                (1, rdinter),
--                (1, rseq2 n),
--                (1, rassoc n),
--                (1, rbeta n),
--                (1, rapp n),
--                (1, rdsemi n),
--                (1, rdctx n)]
--     where
--       rseq2 n = do
--         t <- resize (n `div` 2) arbitrary
--         u <- resize (n `div` 2) arbitrary
--         return $ App (App (Constant Semi) t) u
--       rassoc n = do
--         t <- resize (n `div` 2) arbitrary
--         u <- resize (n `div` 2) arbitrary
--         v <- resize (n `div` 2) arbitrary
--         return $ App (App (Constant Semi) (App (App (Constant Semi) t) u)) v
--       rbeta n = do
--         v <- choose (1,4)
--         k <- arbitrary
--         t <- resize (n `div` 2) arbitrary
--         u <- resize (n `div` 2) arbitrary
--         return $ App (Abs v k t) u
--       rapp n = do
--         t <- resize (n `div` 2) arbitrary
--         u <- resize (n `div` 2) arbitrary
--         return $ App t u
--       rdsemi n = do
--          t <- resize (n `div` 2) arbitrary
--          u <- resize (n `div` 2) arbitrary
--          return (App (Constant Dual) (App (App (Constant Semi) t) u))
--       rdctx n = do
--         t <- resize (n `div` 2) arbitrary
--         return $ App (Constant Dual) t

-- rseq1 :: Gen Type
-- rseq1 = App (App (Constant Semi) (Constant Skip)) <$> arbitrary

-- rmu :: Gen Type
-- rmu = do
--   k <- arbitrary
--   App (Constant (Rec k)) <$> arbitrary

-- rdSkip :: Gen Type
-- rdSkip = pure (App (Constant Dual) (Constant Skip))

-- rdWait :: Gen Type
-- rdWait = pure (App (Constant Dual) (Constant (End In)))

-- rdClose :: Gen Type
-- rdClose = pure (App (Constant Dual) (Constant (End Out)))

-- rdout :: Gen Type
-- rdout = pure (App (Constant Dual) (Constant (Message Out)))

-- rdin :: Gen Type
-- rdin = pure (App (Constant Dual) (Constant (Message In)))

-- rdext :: Gen Type
-- rdext = do
--   App (Constant Dual) . Constant . Choice External <$> labelMap

-- rdinter :: Gen Type
-- rdinter = do
--   App (Constant Dual) . Constant . Choice Internal <$> labelMap

-- rddvar :: Gen Type  
-- como gerar T1..Tm

-- Generator for LabelMap
-- labels numero arbitrary 
labelMap :: Gen LabelMap
labelMap = do
  keyValues <- listOf keyValue
  return (Map.fromList keyValues)
  where
    keyValue :: Gen (Variable, Type)
    keyValue = do
      v <- choose (1, 4)
      t <- arbitrary
      return (v, t)

