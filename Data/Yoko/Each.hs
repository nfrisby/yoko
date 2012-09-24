{-# LANGUAGE KindSignatures, ConstraintKinds, MultiParamTypeClasses,
  Rank2Types, FlexibleInstances, UndecidableInstances, TypeOperators #-}

{- |

Module      :  Data.Yoko.Each
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Basic support for folding through type-level sums.

-}

module Data.Yoko.Each (Each0, each0, Each1, each1, Each2, each2) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation


-- | The constraint @Each0 con sum@ corresponds to the constraing @forall dc in
-- sum. con dc@.
type Each0 = Each0_
type Each1 = Each1_
type Each2 = Each2_

-- | Fold through a type-level sum.
each0 :: Each0 cxt sum => Proxy cxt -> (forall a. cxt a => a -> b) -> sum p1 p0 -> b
each0 = each0_

each1 :: Each1 cxt sum => Proxy cxt -> (forall a. cxt a => a p0 -> b) -> sum p1 p0 -> b
each1 = each1_

each2 :: Each2 cxt sum => Proxy cxt -> (forall a. cxt a => a p1 p0 -> b) -> sum p1 p0 -> b
each2 = each2_





class Each0_ cxt sum where
  each0_ :: Proxy cxt -> (forall a. cxt a => a -> b) -> sum p1 p0 -> b
instance cxt a => Each0_ cxt (N0 a) where each0_ _ f = f . unN0
instance (Each0_ cxt a, Each0_ cxt b) => Each0_ cxt (a :+: b) where each0_ c f = foldPlus (each0 c f) (each0 c f)

class Each1_ cxt sum where
  each1_ :: Proxy cxt -> (forall a. cxt a => a p0 -> b) -> sum p1 p0 -> b
instance cxt a => Each1_ cxt (N1 a) where each1_ _ f = f . unN1
instance (Each1_ cxt a, Each1_ cxt b) => Each1_ cxt (a :+: b) where each1_ c f = foldPlus (each1 c f) (each1 c f)

class Each2_ cxt sum where
  each2_ :: Proxy cxt -> (forall a. cxt a => a p1 p0 -> b) -> sum p1 p0 -> b
instance cxt a => Each2_ cxt (N2 a) where each2_ _ f = f . unN2
instance (Each2_ cxt a, Each2_ cxt b) => Each2_ cxt (a :+: b) where each2_ c f = foldPlus (each2 c f) (each2 c f)





--_ex = putStrLn $ each (Proxy :: Proxy Show) show $
--       L (N (L_ 'n')) `asTypeOf` R (N (R_ True))

--newtype L_ (p1 :: *) (p0 :: *) = L_ Char deriving Show
--newtype R_ (p1 :: *) (p0 :: *) = R_ Bool deriving Show
