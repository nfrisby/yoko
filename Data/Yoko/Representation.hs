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
   WN(..),
   unN0, foldN0, mapN0,
   unN1, foldN1, mapN1,
   unN2, foldN2, mapN2,
   foldPlus, FoldPlusW'(..), mapPlus,
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
data family N (dc :: k) :: * -> * -> *
newtype instance N dc (p1 :: *) (p0 :: *) = N0  dc
newtype instance N dc (p1 :: *) (p0 :: *) = N1 (dc    p0)
newtype instance N dc (p1 :: *) (p0 :: *) = N2 (dc p1 p0)

infixl 6 :+:
-- | Sum union.
data (:+:) a b (p1 :: *) (p0 :: *) = L (a p1 p0) | R (b p1 p0) deriving (Eq, Show, Ord, Read)



-- | An occurrence of the 1st parameter.
newtype Par1 (p1 :: *) (p0 :: *) = Par1 p1

-- | An occurrence of the zeroth parameter.
newtype Par0 (p1 :: *) (p0 :: *) = Par0 p0



newtype T0 (v :: Variety) t                      (p1 :: *) (p0 :: *) = T0  t
newtype T1 (v :: Variety) (t :: * -> *)        a (p1 :: *) (p0 :: *) = T1 (t           (a p1 p0))
newtype T2 (v :: Variety) (t :: * -> * -> *) b a (p1 :: *) (p0 :: *) = T2 (t (b p1 p0) (a p1 p0))



-- | A mapping to the structural representation of a fields type: just products
-- of fields, no sums -- fields types have just one constructor.
type family Rep (t :: k) :: * -> * -> *



-- | Converts between a fields type and its product-of-fields structure.
class Generic dc where
  rep :: W dc (Rep dc) p1 p0; obj :: W' dc (Rep dc) p1 p0




class ComposeW dc => WN dc where
  nN  :: W  dc (N dc) p1 p0
  unN :: W' dc (N dc) p1 p0
instance WN (dc :: *)           where nN = W0 N0; unN = W'0 unN0
instance WN (dc :: * -> *)      where nN = W1 N1; unN = W'1 unN1
instance WN (dc :: * -> * -> *) where nN = W2 N2; unN = W'2 unN2

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

unN0 (N0 x) = x
foldN0 f = f . unN0

unN1 (N1 x) = x
foldN1 f = f . unN1

unN2 (N2 x) = x
foldN2 f = f . unN2

mapN0 f = N0 . foldN0 f
mapN1 f = N1 . foldN1 f
mapN2 f = N2 . foldN2 f

foldPlus f g x = case x of
  L x -> f x   ;   R x -> g x

class FoldPlusW' (s :: k) where
  foldPlusW' :: W' s l p1 p0 -> W' s r p1 p0 -> W' s (l :+: r) p1 p0
instance FoldPlusW' (s :: *) where foldPlusW' (W'0 f) (W'0 g) = W'0 $ foldPlus f g
instance FoldPlusW' (s :: * -> *) where foldPlusW' (W'1 f) (W'1 g) = W'1 $ foldPlus f g
instance FoldPlusW' (s :: * -> * -> *) where foldPlusW' (W'2 f) (W'2 g) = W'2 $ foldPlus f g

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
