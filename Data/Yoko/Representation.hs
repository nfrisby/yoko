{-# LANGUAGE TypeFamilies, TypeOperators, TemplateHaskell,
  UndecidableInstances, EmptyDataDecls, DataKinds, PolyKinds,
  MultiParamTypeClasses, FlexibleInstances #-}

{- |

Module      :  Data.Yoko.Representation
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

The @yoko@ representation types.

-}

module Data.Yoko.Representation
  (-- * Representation
   -- ** Sums
   Void(..), N(..), (:+:)(..),
   C(..),
   -- ** Products
   U(..), (:*:)(..),
   -- ** Fields
   T0(..), T1(..), T2(..), Variety(..),
   Par1(..), Par0(..),
   -- ** Conversions to and from fields-of-products structure
   Rep, Generic(..),
   -- ** Auxilliaries
   unC, foldC, mapC,
   unN, foldN, mapN,
   foldPlus, mapPlus,
   foldTimes, mapTimes,
   unT0, mapT0,
   unT1, mapT1,
   unT2, mapT2,
   unPar0, mapPar0,
   unPar1, mapPar1,
   DistMaybePlus
   ) where

import Data.Yoko.W
import Data.Yoko.TypeBasics



data Variety = Rec Nat | Dep



-- | Wrapper around productus
newtype C dc r (p1 :: *) (p0 :: *) = C (r p1 p0)

-- | The empty product.
data U (p1 :: *) (p0 :: *) = U

infixr 6 :*:
-- | Product union.
data (:*:) a b (p1 :: *) (p0 :: *) = a p1 p0 :*: b p1 p0

-- | The empty sum. Used as an error type instead of a represention type, since
-- data types with no constructors are uninteresting from a generic programming
-- perspective -- there's just not much to be done generically.
data Void (p1 :: *) (p0 :: *)

-- | The singleton sum.
newtype N (dc :: k) (p1 :: *) (p0 :: *) = N (W dc p1 p0)

infixl 6 :+:
-- | Sum union.
data (:+:) a b (p1 :: *) (p0 :: *) = L (a p1 p0) | R (b p1 p0) deriving (Eq, Show, Ord, Read)



-- | An occurrence of the 1st parameter.
newtype Par1 (p1 :: *) (p0 :: *) = Par1 p1

-- | An occurrence of the zeroth parameter.
newtype Par0 (p1 :: *) (p0 :: *) = Par0 p0



newtype T0 (v :: Variety)  t                     (p1 :: *) (p0 :: *) = T0  t
newtype T1 (v :: Variety) (t :: * -> *)        a (p1 :: *) (p0 :: *) = T1 (t           (a p1 p0))
newtype T2 (v :: Variety) (t :: * -> * -> *) b a (p1 :: *) (p0 :: *) = T2 (t (b p1 p0) (a p1 p0))



-- | A mapping to the structural representation of a fields type: just products
-- of fields, no sums -- fields types have just one constructor.
type family Rep (t :: k) :: * -> * -> *



-- | Converts between a fields type and its product-of-fields structure.
class Generic dc where
  rep :: W   dc p1 p0 -> Rep dc p1 p0
  obj :: Rep dc p1 p0 -> W   dc p1 p0


unT0 (T0 x) = x
mapT0 f (T0 x) = T0 (f x)

unT1 (T1 x) = x
mapT1 f (T1 x) = T1 (f x)

unT2 (T2 x) = x
mapT2 f (T2 x) = T2 (f x)

unPar0 (Par0 x) = x
mapPar0 f (Par0 x) = Par0 (f x)

unPar1 (Par1 x) = x
mapPar1 f (Par1 x) = Par1 (f x)



unC (C x) = x
foldC f = f . unC
mapC f = foldC (C . f)

unN (N x) = x
foldN f = f . unN

mapN f = N . foldN f

foldPlus f g x = case x of
  L x -> f x   ;   R x -> g x

mapPlus f g = foldPlus (L . f) (R . g)

mapTimes f g (a :*: b) = f a :*: g b

foldTimes comb f g (a :*: b) = comb (f a) (g b)



-- | We avoid empty sums with a type-level @Maybe@. @DistMaybePlus@ performs
-- sum union on lifted sums, only introducing @:+:@ when both arguments are
-- @Just@s.
type family DistMaybePlus (a :: Maybe (* -> * -> *)) (b :: Maybe (* -> * -> *)) :: Maybe (* -> * -> *)
type instance DistMaybePlus Nothing b = b
type instance DistMaybePlus (Just a) Nothing = Just a
type instance DistMaybePlus (Just a) (Just b) = Just (a :+: b)


{-
data Nat = Z | S Nat
type family Add (n :: Nat) (m :: Nat) :: Nat
type instance Add Z m = m
type instance Add (S n) m = S (Add n m)

type family CountRs (rep :: * -> * -> *) :: Nat
type instance CountRs (Dep a) = Z
type instance CountRs (Rec a) = S Z
type instance CountRs U = Z
type instance CountRs (a :*: b) = Add (CountRs a) (CountRs b)
-}





concat `fmap` mapM derive_data [''Variety, ''T0, ''T1, ''T2, ''Par1, ''Par0, ''C, ''U, ''(:*:), ''N, ''(:+:)]
concat `fmap` mapM derive_pro ['Rec, 'Dep, 'Z, 'S]
