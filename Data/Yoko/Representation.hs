{-# LANGUAGE TypeFamilies, TypeOperators, TemplateHaskell,
  UndecidableInstances, EmptyDataDecls, DataKinds, PolyKinds #-}

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
   -- ** Products
   C(..), U(..), (:*:)(..),
   -- ** Fields
   Rec0(..), Rec1(..), Rec2(..),
   Dep(..), Par1(..), Par0(..), (:@:)(..), (:@@:)(..),
   -- ** Conversions to and from fields-of-products structure
   Rep, Generic0(..), Generic1(..), Generic2(..),
   -- ** Auxilliaries
   unN, foldN, mapN,
   foldPlus, mapPlus,
   foldTimes, mapTimes,
   unDep,
   unRec0, mapRec0,
   unRec1, mapRec1,
   unRec2, mapRec2,
   DistMaybePlus
   ) where

import Data.Yoko.TypeBasics




-- | Wrapper around productus
newtype C (dc :: * -> * -> *) r (p1 :: *) (p0 :: *) = C (r p1 p0)

-- | The empty product.
data U (p1 :: *) (p0 :: *) = U

infixr 6 :*:
-- | Product union.
data (:*:) a b (p1 :: *) (p0 :: *) = a p1 p0 :*: b p1 p0

-- | The empty sum. Used as an error type instead of a represention type, since
-- data types with no constructors are uninteresting from a generic programming
-- perspective -- there's just not much to be done generically.
data Void t (p1 :: *) (p0 :: *)

-- | The singleton sum.
newtype N dc (p1 :: *) (p0 :: *) = N (dc p1 p0)

infixl 6 :+:
-- | Sum union.
data (:+:) a b (p1 :: *) (p0 :: *) = L (a p1 p0) | R (b p1 p0) deriving (Eq, Show, Ord, Read)



-- | An occurrence of the 1st parameter.
newtype Par1 (p1 :: *) (p0 :: *) = Par1 p1

-- | An occurrence of the zeroth parameter.
newtype Par0 (p1 :: *) (p0 :: *) = Par0 p0



-- | A recursive @*@ occurrence.
newtype Rec0 (lbl :: Nat) a (p1 :: *) (p0 :: *) = Rec0 a
-- | A non-recursive @*@ occurrence.
newtype Dep (a :: *) (p1 :: *) (p0 :: *) = Dep a

-- | A recursive occurrence.
newtype Rec1 (lbl :: Nat) (t :: * -> *) a (p1 :: *) (p0 :: *) = Rec1 (t (a p1 p0))
-- | A non-recursive @* -> *@ occurrence.
newtype (:@:) (f :: * -> *) a (p1 :: *) (p0 :: *) = App1 (f (a p1 p0))

-- | A recursive @* -> * -> *@ occurrence.
newtype Rec2 (lbl :: Nat) (t :: * -> * -> *) b a (p1 :: *) (p0 :: *) = Rec2 (t (b p1 p0) (a p1 p0))
-- | A non-recursive @* -> * -> *@ occurrence.
newtype (:@@:) (ff :: * -> * -> *) b a (p1 :: *) (p0 :: *) =
  App2 (ff (b p1 p0) (a p1 p0))



-- | A mapping to the structural representation of a fields type: just products
-- of fields, no sums -- fields types have just one constructor.
type family Rep (t :: k) :: * -> * -> *



-- | Converts between a fields type and its product-of-fields structure.
class Generic0 a where rep0 :: a       -> Rep a p1 p0; obj0 :: Rep a p1 p0 -> a
class Generic1 a where rep1 :: a    p0 -> Rep a p1 p0; obj1 :: Rep a p1 p0 -> a    p0
class Generic2 a where rep2 :: a p1 p0 -> Rep a p1 p0; obj2 :: Rep a p1 p0 -> a p1 p0



unDep (Dep x) = x

unRec0 (Rec0 x) = x
mapRec0 f (Rec0 x) = Rec0 (f x)

unRec1 (Rec1 x) = x
mapRec1 f (Rec1 x) = Rec1 (f x)

unRec2 (Rec2 x) = x
mapRec2 f (Rec2 x) = Rec2 (f x)

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







concat `fmap` mapM derive_data [''Dep, ''Rec0, ''Rec1, ''Rec2, ''Par1, ''Par0, ''C, ''U, ''(:*:), ''N, ''(:+:), ''(:@:), ''(:@@:)]
