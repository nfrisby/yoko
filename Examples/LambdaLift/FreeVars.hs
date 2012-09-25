{-# LANGUAGE TypeOperators, FlexibleContexts, UndecidableInstances, KindSignatures, DataKinds, FlexibleInstances #-}

{- |

Module      :  LambdaLift.FreeVars
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

An example lambba lifter using @hcompos@.

-}

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
class FreeVars2 a where freeVars2 :: a (p1 :: *) (p0 :: *) -> Frees

instance FreeVars ULC where
  freeVars = w where
    w tm = case partition $ unW0 disband tm of
      Left x -> ($ x) $
        (\(Lam_ _ty tm) -> bump 1 $ w tm) .||
        (\(Var_ i) -> IS.singleton i) .|.
        (\(Let_ ds tm) ->
          foldr (\(Decl _ tm) -> IS.union (w tm) . bump 1) (w tm) ds)
      Right x -> freeVars2 x

-- through sums
--instance FreeVars sum => FreeVars (DCsOf t sum) where
--  freeVars = freeVars . unDCsOf
instance (FreeVars2 a, FreeVars2 b) => FreeVars2 (a :+: b) where
  freeVars2 = foldPlus freeVars2 freeVars2
instance (Generic a, FreeVars2 (Rep a)) => FreeVars2 (N0 a) where
  freeVars2 = freeVars2 . repUnN0

repUnN0 :: Generic dc => N0 dc p1 p0 -> Rep dc p1 p0
repUnN0 = unW0 rep . unN0

-- through products
instance FreeVars2 U where freeVars2 = const IS.empty
instance (FreeVars2 a, FreeVars2 b) => FreeVars2 (a :*: b) where
  freeVars2 = foldTimes IS.union freeVars2 freeVars2
instance FreeVars2 a => FreeVars2 (C dc a) where freeVars2 = freeVars2 . unC

-- through fields
instance FreeVars a => FreeVars2 (T0 (Rec lbl) a) where
  freeVars2 = freeVars . unT0
instance FreeVars2 (T0 Dep a) where freeVars2 = const IS.empty
instance (Foldable f, FreeVars2 a) => FreeVars2 (T1 v f a) where
  freeVars2 = foldMap freeVars2 . unT1
