{-# LANGUAGE TypeOperators, FlexibleContexts, UndecidableInstances #-}

module LambdaLift.FreeVars where

import LambdaLift.ULC

import qualified Data.IntSet as IS
import Data.Foldable (Foldable, foldMap)

import Data.Yoko





type Frees = IS.IntSet

bump :: Int -> Frees -> Frees
bump k = IS.map (subtract k) . IS.filter (>= k)





anonFVs :: ULC -> Frees
anonFVs = freeVars



class FreeVars a where freeVars :: a -> Frees

instance FreeVars ULC where
  freeVars = w where
    w tm = case partition $ disband tm of
      Left x -> ($ x) $
        (\(Lam_ ty tm) -> bump 1 $ w tm) .||
        (\(Var_ i) -> IS.singleton i) .|.
        (\(Let_ ds tm) ->
          foldr (\(Decl _ tm) -> IS.union (w tm) . bump 1) (w tm) ds)
      Right x -> freeVars x

-- through sums
instance FreeVars sum => FreeVars (DCsOf t sum) where
  freeVars = freeVars . unDCsOf
instance (FreeVars a, FreeVars b) => FreeVars (a :+: b) where
  freeVars = foldPlus freeVars freeVars
instance (Generic a, FreeVars (Rep a)) => FreeVars (N a) where
  freeVars = freeVars . rep . unN

-- through products
instance FreeVars U where freeVars = const IS.empty
instance (FreeVars a, FreeVars b) => FreeVars (a :*: b) where
  freeVars = foldTimes IS.union freeVars freeVars

-- through fields
instance FreeVars a => FreeVars (Rec a) where
  freeVars = freeVars . unRec
instance FreeVars (Dep a) where freeVars = const IS.empty
instance (Foldable f, FreeVars a) => FreeVars (Par1 f a) where
  freeVars = foldMap freeVars . unPar1
