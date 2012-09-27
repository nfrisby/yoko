{-# LANGUAGE TypeFamilies, TypeOperators, TemplateHaskell,
  UndecidableInstances, EmptyDataDecls, DataKinds, PolyKinds,
  MultiParamTypeClasses, FlexibleInstances, LambdaCase,
  ScopedTypeVariables, ConstraintKinds #-}

{-# LANGUAGE GADTs #-}

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
   Par0_0(..), Par0_1(..), Par0_2(..),
   Par1_0(..), Par1_1(..), Par1_2(..),
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
   DistMaybePlus
   ) where

import Data.Yoko.W
import Data.Yoko.TypeBasics

import Data.Yoko.Invariant



data Variety k = Rec Nat k | Dep k | Par1 | Par0



-- | Wrapper around productus
newtype C dc r p1 p0 = C (r p1 p0)

-- | The empty product.
data U p1 p0 = U

infixr 6 :*:
-- | Product union.
data (:*:) a b p1 p0 = a p1 p0 :*: b p1 p0

-- | The empty sum. Used as an error type instead of a represention type, since
-- data types with no constructors are uninteresting from a generic programming
-- perspective -- there's just not much to be done generically.
data Void p1 p0

-- | The singleton sum.
data family N (dc :: k) (p1 :: k1) (p0 :: k0) :: *
newtype instance N dc p1 p0 = N0  dc
newtype instance N dc p1 p0 = N1 (dc    p0)
newtype instance N dc p1 p0 = N2 (dc p1 p0)

infixl 6 :+:
-- | Sum union.
data (:+:) a b p1 p0 = L (a p1 p0) | R (b p1 p0) deriving (Eq, Show, Ord, Read)



-- | An occurrence of one of the parameters.
newtype Par0_0 p1 p0 = Par0_0 p0
newtype Par1_0 p1 p0 = Par1_0 p1

data Par0_1 a p1 p0 where
  Par0_1 :: Invariant p0 => p0 (a p1 p0 :: *) -> Par0_1 a p1 p0
data Par1_1 a p1 p0 where
  Par1_1 :: Invariant p1 => p1 (a p1 p0 :: *) -> Par1_1 a p1 p0

data Par0_2 b a p1 p0 where
  Par0_2 :: Invariant2 p0 => p0 (b p1 p0 :: *) (a p1 p0 :: *) -> Par0_2 b a p1 p0
data Par1_2 b a p1 p0 where
  Par1_2 :: Invariant2 p1 => p1 (b p1 p0 :: *) (a p1 p0 :: *) -> Par1_2 b a p1 p0



{-newtype T0   (v :: Variety) t     (p1 :: *) (p0 :: *)     = T0    t
newtype T1'1 (v :: Variety) t a   (p1 :: *) (p0 :: *)     = T1'1 (t (a p1 p0))
newtype T1'0 (v :: Variety) t     (p1 :: *) (p0 :: *) x   = T1'0 (t x)
newtype T2'2 (v :: Variety) t b a (p1 :: *) (p0 :: *)     = T2'2 (t (b p1 p0) (a p1 p0))
newtype T2'1 (v :: Variety) t   a (p1 :: *) (p0 :: *)   x = T2'1 (t (a p1 p0) x)
newtype T2'0 (v :: Variety) t     (p1 :: *) (p0 :: *) y x = T2'0 (t y         x)-}

type family TData (v :: Variety k) (p1 :: k1) (p0 :: k0) :: k
type instance TData (Rec lbl t) p1 p0 = t
type instance TData (Dep t)     p1 p0 = t
type instance TData Par1        p1 p0 = p1
type instance TData Par0        p1 p0 = p0

newtype T0 (v :: Variety *)                 p1 p0 = T0 (TData v p1 p0)
newtype T1 (v :: Variety (* -> *))        a p1 p0 = T1 (TData v p1 p0 (a p1 p0 :: *))
newtype T2 (v :: Variety (* -> * -> *)) b a p1 p0 = T2 (TData v p1 p0 (b p1 p0 :: *) (a p1 p0 :: *))





-- | A mapping to the structural representation of a fields type: just products
-- of fields, no sums -- fields types have just one constructor.
type family Rep (t :: k) (any :: KProxy k1 k0) :: k1 -> k0 -> *



-- | Converts between a fields type and its product-of-fields structure.
class Generic (dc :: k) (any :: KProxy k1 k0) where
  rep :: (InvPrereq p1, InvPrereq p0) => Proxy any -> W  dc (Rep dc any) (p1 :: k1) (p0 :: k0)
  obj :: (InvPrereq p1, InvPrereq p0) => Proxy any -> W' dc (Rep dc any) (p1 :: k1) (p0 :: k0)




class ComposeW dc any => WN (dc :: k) (any :: KProxy k1 k0) where
  nN  :: Proxy any -> W  dc (N dc) (p1 :: k1) (p0 :: k0)
  unN :: Proxy any -> W' dc (N dc) (p1 :: k1) (p0 :: k0)
instance WN (dc :: *)               any              where nN _ = W0 N0; unN _ = W'0 unN0
instance WN (dc :: k0 -> *)        (any :: KProxy k1 k0) where nN _ = W1 N1; unN _ = W'1 unN1
instance WN (dc :: k1 -> k0 -> *)  (any :: KProxy k1 k0) where nN _ = W2 N2; unN _ = W'2 unN2

unT0 (T0 x) = x
mapT0 f (T0 x) = T0 (f x)

unT1 (T1 x) = x
mapT1 f (T1 x) = T1 (f x)

unT2 (T2 x) = x
mapT2 f (T2 x) = T2 (f x)




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

class FoldPlusW' (s :: k) (any :: KProxy k1 k0) where
  foldPlusW' :: Proxy (any :: KProxy k1 k0) -> W' s l (p1 :: k1) (p0 :: k0) -> W' s r p1 p0 -> W' s (l :+: r) p1 p0
instance FoldPlusW' (s :: *)               any              where foldPlusW' _ (W'0 f) (W'0 g) = W'0 $ foldPlus f g
instance FoldPlusW' (s :: k0 -> *)        (any :: KProxy k1 k0) where foldPlusW' _ (W'1 f) (W'1 g) = W'1 $ foldPlus f g
instance FoldPlusW' (s :: k1 -> k0 -> *)  (any :: KProxy k1 k0) where foldPlusW' _ (W'2 f) (W'2 g) = W'2 $ foldPlus f g

mapPlus f g = foldPlus (L . f) (R . g)

mapTimes f g (a :*: b) = f a :*: g b

foldTimes comb f g (a :*: b) = comb (f a) (g b)



-- | We avoid empty sums with a type-level @Maybe@. @DistMaybePlus@ performs
-- sum union on lifted sums, only introducing @:+:@ when both arguments are
-- @Just@s.
type family DistMaybePlus (a :: Maybe (k1 -> k0 -> *)) (b :: Maybe (k1 -> k0 -> *)) :: Maybe (k1 -> k0 -> *)
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





concat `fmap` mapM derive_data [''Variety, ''T0, ''T1, ''T2, ''Par0_0, ''Par0_1, ''Par0_2, ''Par1_0, ''Par1_1, ''Par1_2, ''C, ''U, ''(:*:), ''N, ''(:+:)]
concat `fmap` mapM derive_pro ['Rec, 'Dep, 'Z, 'S]

















instance Invariant2 U where
  invmap2 _ _ _ _ _ = U

instance (Invariant2 l, Invariant2 r) => Invariant2 (l :*: r) where
  invmap2 f f' g g' (l :*: r) = invmap2 f f' g g' l :*: invmap2 f f' g g' r

instance (Invariant2 r) => Invariant2 (C dc r) where
  invmap2 f f' g g' (C x) = C $ invmap2 f f' g g' x

-- can be optimized for * and * -> *, but I'm favoring terseness

instance (any ~ ('KProxy :: KProxy k1 k0),
          WN dc any, Invariant2 (Rep dc any), Generic dc any)
  => Invariant2 (N dc :: k1 -> k0 -> *) where
  invmap2 f f' g g'  = unSym p (nN p) (obj p) . invmap2 f f' g g' .
                       unSym p (rep p) (unN p) where
    p = Proxy :: Proxy ('KProxy :: KProxy k1 k0)

instance (Invariant2 l, Invariant2 r) => Invariant2 (l :+: r) where
  invmap2 f f' g g' = \case
    L x -> L $ invmap2 f f' g g' x
    R x -> R $ invmap2 f f' g g' x

instance Invariant2 Void where invmap2 = error "invmap2 @Void"



instance Invariant2 (T0 (Dep t))     where invmap2 _ _ _ _ (T0 x) = T0 x
instance Invariant2 (T0 (Rec lbl t)) where invmap2 _ _ _ _ (T0 x) = T0 x
instance Invariant2 (T0 Par0 :: k1 -> * -> *) where invmap2 _ _ (InvArg0 f) _ (T0 x) = T0 $ f x
instance Invariant2 (T0 Par1 :: * -> k0 -> *) where invmap2 (InvArg0 f) _ _ _ (T0 x) = T0 $ f x



instance (Invariant t, Invariant2 a) => Invariant2 (T1 (Dep t) a :: k1 -> k0 -> *) where
  invmap2 f f' g g' (T1 x) = T1 $ invmap
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x

instance (Invariant t, Invariant2 a) => Invariant2 (T1 (Rec lbl t) a :: k1 -> k0 -> *) where
  invmap2 f f' g g' (T1 x) = T1 $ invmap
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x

instance Invariant2 a => Invariant2 (T1 Par0 a :: k1 -> (* -> *) -> *) where
  invmap2 f f' g@(InvArg1 cnv) g' (T1 x) = T1 $ cnv $ invmap
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x

instance Invariant2 a => Invariant2 (T1 Par1 a :: (* -> *) -> k0 -> *) where
  invmap2 f@(InvArg1 cnv) f' g g' (T1 x) = T1 $ cnv $ invmap
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x



instance (Invariant2 t, Invariant2 a, Invariant2 b)
  => Invariant2 (T2 (Dep t) b a :: k1 -> k0 -> *) where
  invmap2 f f' g g' (T2 x) = T2 $ invmap2
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g)
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x

instance (Invariant2 t, Invariant2 a, Invariant2 b)
  => Invariant2 (T2 (Rec lbl t) b a :: k1 -> k0 -> *) where
  invmap2 f f' g g' (T2 x) = T2 $ invmap2
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g)
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x

instance (Invariant2 a, Invariant2 b)
  => Invariant2 (T2 Par0 b a :: k1 -> (* -> * -> *) -> *) where
  invmap2 f f' g@(InvArg2 cnv) g' (T2 x) = T2 $ cnv $ invmap2
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g)
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x

instance (Invariant2 a, Invariant2 b)
  => Invariant2 (T2 Par1 b a :: (* -> * -> *) -> k0 -> *) where
  invmap2 f@(InvArg2 cnv) f' g g' (T2 x) = T2 $ cnv $ invmap2
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g)
    (InvArg0 $ invmap2 f f' g g') (InvArg0 $ invmap2 f' f g' g) x
