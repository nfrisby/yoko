{-# LANGUAGE TypeFamilies, TypeOperators, TemplateHaskell,
  UndecidableInstances, EmptyDataDecls, DataKinds #-}

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
   U(..), (:*:)(..),
   -- ** Fields
   Rec(..), Dep(..), Par1(..), Par2(..),
   -- ** Conversions to and from fields-of-products structure
   Rep, Generic(..),
   -- ** Auxilliaries
   unN, foldN, mapN,
   foldPlus, mapPlus,
   foldTimes, mapTimes,
   unRec, mapRec, unDep, unPar1, unPar2,
   DistMaybePlus
   ) where

import Data.Yoko.TypeBasics



-- | The empty product.
data U = U

infixr 6 :*:
-- | Product union.
data a :*: b = a :*: b

-- | The empty sum. Used as an error type instead of a represention type, since
-- data types with no constructors are uninteresting from a generic programming
-- perspective -- there's just not much to be done generically.
data Void

-- | The singleton sum.
newtype N a = N a

infixl 6 :+:
-- | Sum union.
data a :+: b = L a | R b deriving (Eq, Show, Ord, Read)


-- | Representation of unary type application. @f@ is a genuine @*->*@ type,
-- not a representation. @a@ is a representation.
newtype Par1 f a = Par1 (f a)

-- | Representation of binary type application. @f@ is a genuine @*->*->*@
-- type, not a representation. @a@ and @b@ are representations.
newtype Par2 f a b = Par2 (f a b)


-- | A non-recursive occurrence.
newtype Dep a = Dep a

-- | A recursive occurrence.
newtype Rec a = Rec a



-- | A mapping to the structural representation of a fields type: just products
-- of fields, no sums -- fields types have just one constructor.
type family Rep a



-- | Converts between a fields type and its product-of-fields structure.
class Generic a where rep :: a -> Rep a; obj :: Rep a -> a



unDep (Dep x) = x

unRec (Rec x) = x
mapRec f (Rec x) = Rec (f x)

unPar1 (Par1 x) = x
unPar2 (Par2 x) = x

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
type family DistMaybePlus (a :: Maybe *) (b :: Maybe *) :: Maybe *
type instance DistMaybePlus Nothing b = b
type instance DistMaybePlus (Just a) Nothing = Just a
type instance DistMaybePlus (Just a) (Just b) = Just (a :+: b)



data Z; data S n
type family Add n m
type instance Add Z m = m
type instance Add (S n) m = S (Add n m)

type family CountRs rep
type instance CountRs (Dep a) = Z
type instance CountRs (Rec a) = S Z
type instance CountRs U = Z
type instance CountRs (a :*: b) = Add (CountRs a) (CountRs b)





concat `fmap` mapM derive_data [''Dep, ''Rec, ''U, ''(:*:), ''N, ''(:+:)]
