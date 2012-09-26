{-# LANGUAGE TypeFamilies, UndecidableInstances, DataKinds, PolyKinds, GADTs,
  FlexibleInstances, TypeOperators, Rank2Types, ScopedTypeVariables,
  InstanceSigs, ConstraintKinds, MultiParamTypeClasses #-}

{- |

Module      :  Data.Yoko.TypeBasics
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Some type-level programming basics.

-}

module Data.Yoko.TypeBasics (
  Proxy(..), Equal, derive_data, derive_pro,
  Nat(..), SingNat(..),
  Length, Length', Append,
  App, Constant(..),
  Vec(..), vCarrying,
  VFunctor(..), TrivCon, trivCon,
  VInitialize(..),
  CVec(..), cvec2list,
  VRepeat(..), Diag_(..), VZip(..), cvZipWith,
  Idx(..), IndexInto(..), cvAt, cvUpd, VEnum(..), cvAddIndexes,
  -- ** Re-exports
  module Data.Yoko.MaybeKind, encode, SpineCompare
  ) where

import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import qualified Control.Applicative as I

import Data.Yoko.MaybeKind

import Type.Spine
import Type.Ord (IsEQ)
import Type.Serialize
import Type.Ord.SpineSerialize (SpineCompare)



-- | A polykinded proxy.
data Proxy a = Proxy



-- | Convenient synonym. @type Equal a b = 'IsEQ' ('SpineCompare' a b)@
type Equal a b = IsEQ (SpineCompare a b)



-- | Template Haskell derivation for the @type-spine@ and @type-cereal@
-- packages' 'Spine' and 'Serialize' type families, which support generic
-- instances of 'Compare'.
derive_data n = do
  d <- spineType_d n
  (d ++) `fmap` serializeTypeAsHash_data n

derive_pro n = do
  d <- spineType_pro n
  (d ++) `fmap` serializeTypeAsHash_pro n



-- naturals
data Nat = Z | S Nat

data SingNat :: Nat -> * where
  SZ ::              SingNat 'Z
  SN :: SingNat n -> SingNat ('S n)

-- lists
type family Append (x :: [k]) (y :: [k]) :: [k]
type instance Append '[] y       = y
type instance Append (t ': ts) y = t ': Append ts y


type Length list = Length' Z list

type family Length' (acc :: Nat) (list :: [k]) :: Nat
type instance Length' acc '[]         = acc
type instance Length' acc (t ': list) = Length' (S acc) list

-- indexed vectors
type family App (fn :: k -> *) (t :: k) :: *

newtype Constant a (t :: k) = Constant a
type instance App (Constant a) k = a

data Vec :: [k] -> (k -> *) -> * where
  VNil  ::                        Vec '[]       f
  VCons :: App f t -> Vec ts f -> Vec (t ': ts) f

instance Eq (Vec '[] f) where _ == _ = True
instance (Eq (App f t), Eq (Vec ts f)) => Eq (Vec (t ': ts) f) where
  VCons a as == VCons b bs = a == b && as == bs

instance Ord (Vec '[] f) where compare _ _ = EQ
instance (Ord (App f t), Ord (Vec ts f)) => Ord (Vec (t ': ts) f) where
  VCons a as `compare` VCons b bs = compare (a, as) (b, bs)

vCarrying :: Proxy f -> Vec ts f -> Vec ts f
vCarrying _ = id

class VFunctor c ts where
  vMap :: Proxy c -> (forall t. c t => Proxy t -> App f t -> App g t) -> Vec ts f -> Vec ts g

instance VFunctor c '[] where
  vMap _ _ VNil         = VNil
instance (c t, VFunctor c ts) => VFunctor c (t ': ts) where
  vMap c f (VCons x xs) = VCons (f (Proxy :: Proxy t) x) $ vMap c f xs

class TrivCon a; instance TrivCon a
trivCon :: Proxy TrivCon
trivCon = Proxy

instance Monoid (Vec '[] f) where
  mempty = VNil; mappend _ _ = VNil
instance (Monoid (App f t), Monoid (Vec ts f)) => Monoid (Vec (t ': ts) f) where
  mempty = VCons mempty mempty
  VCons x xs `mappend` VCons y ys = mappend x y `VCons` mappend xs ys



newtype CVec ts a = CVec {unCVec :: Vec ts (Constant a)}

instance Eq  (Vec ts (Constant a)) => Eq  (CVec ts a) where CVec x == CVec y = x == y
instance Ord (Vec ts (Constant a)) => Ord (CVec ts a) where CVec x `compare` CVec y = compare x y

instance Monoid (Vec ts (Constant a)) => Monoid (CVec ts a) where
  mempty = CVec mempty
  CVec x `mappend` CVec y = CVec $ mappend x y

instance Functor (CVec ts) where fmap = T.fmapDefault
instance F.Foldable (CVec ts) where foldMap = T.foldMapDefault

instance T.Traversable (CVec ts) where
  traverse :: forall a i b. I.Applicative i => (a -> i b) -> CVec ts a -> i (CVec ts b)
  traverse f (CVec v) = CVec I.<$> w v where
    w :: forall ts. Vec ts (Constant a) -> i (Vec ts (Constant b))
    w x = case x of
      VNil       -> I.pure VNil
      VCons a as -> VCons I.<$> f a I.<*> w as

cvec2list :: CVec ts a -> [a]
cvec2list = F.toList

class VRepeat ts where cvRepeat :: a -> CVec ts a

instance VRepeat '[]                     where cvRepeat _ = CVec VNil
instance VRepeat ts => VRepeat (t ': ts) where
  cvRepeat a = CVec $ VCons a $ unCVec $ cvRepeat a

data Diag_ (f :: k -> *) (g :: k -> *) (t :: k) = Diag_
type instance App (Diag_ f g) t = (App f t, App g t)

class VZip ts where vZip :: Vec ts f -> Vec ts g -> Vec ts (Diag_ f g)

instance VZip '[] where vZip _ _ = VNil
instance VZip ts => VZip (t ': ts) where
  vZip (VCons a as) (VCons b bs) = VCons (a, b) $ vZip as bs

cvZipWith :: forall a b c ts. (a -> b -> c) -> CVec ts a -> CVec ts b -> CVec ts c
cvZipWith f (CVec x) (CVec y) = CVec $ w x y where
  w :: forall ts. Vec ts (Constant a) -> Vec ts (Constant b) -> Vec ts (Constant c)
  w VNil         VNil         = VNil
  w (VCons a as) (VCons b bs) = VCons (f a b) $ w as bs

data Idx :: [k] -> * where
  ZIdx :: Idx (t ': ts)
  SIdx :: Idx ts -> Idx (t ': ts)
type instance App Idx ts = Idx ts

class IndexInto (n :: Nat) (ts :: [k]) where
  indexInto :: Proxy n -> Proxy ts -> Idx ts

instance IndexInto Z (t ': ts) where indexInto _ _ = ZIdx
instance IndexInto n ts => IndexInto (S n) (t ': ts) where
  indexInto _ _ = SIdx $ indexInto (Proxy :: Proxy n) (Proxy :: Proxy ts)

instance Show (Idx ts) where
  showsPrec _ ZIdx = showString "ZIdx"
  showsPrec p (SIdx x) = showParen (p > 10) $
    showString "SIdx" . showChar ' ' . showsPrec 11 x

instance Eq (Idx ts) where
  ZIdx == ZIdx = True
  SIdx a == SIdx b = a == b
  _ == _ = False

instance Ord (Idx ts) where
  ZIdx   `compare` ZIdx   = EQ
  ZIdx   `compare` _      = LT
  SIdx _ `compare` ZIdx   = GT
  SIdx a `compare` SIdx b = compare a b

cvAt :: forall ts a. CVec ts a -> Idx ts -> a
cvAt (CVec v) = flip w v where
  w :: forall ts. Idx ts -> Vec ts (Constant a) -> a
  w ZIdx       (VCons a _ ) = a
  w (SIdx idx) (VCons _ as) = w idx as

cvUpd :: forall ts a. CVec ts a -> Idx ts -> (a -> a) -> CVec ts a
cvUpd (CVec v) idx f = CVec $ w idx v where
  w :: forall ts. Idx ts -> Vec ts (Constant a) -> Vec ts (Constant a)
  w ZIdx       (VCons a as) = VCons (f a) as
  w (SIdx idx) (VCons a as) = VCons a $ w idx as

class VEnum ts where cvEnum :: CVec ts (Idx ts)
instance VEnum '[] where cvEnum = CVec VNil
instance VEnum ts => VEnum (t ': ts) where
  cvEnum = CVec $ VCons ZIdx $ unCVec $ fmap SIdx cvEnum

cvAddIndexes :: VEnum ts => CVec ts a -> CVec ts (Idx ts, a)
cvAddIndexes = cvZipWith (,) cvEnum



type instance App Proxy t = Proxy t

class VInitialize c ts where
  vInitialize  :: Proxy c -> Proxy f -> (forall t. c t => Proxy t -> App f t) -> Vec  ts f
  cvInitialize :: Proxy c ->            (forall t. c t => Proxy t -> a) ->       CVec ts a
instance VInitialize c '[] where
  vInitialize  _ _ _ = VNil
  cvInitialize _   _ = CVec VNil
instance (c t, VInitialize c ts) => VInitialize c (t ': ts) where
  vInitialize  pc pf x = VCons (x (Proxy :: Proxy t)) (vInitialize  pc pf x)
  cvInitialize pc    x = CVec $
                         VCons (x (Proxy :: Proxy t)) (unCVec $ cvInitialize pc    x)
