{-# LANGUAGE TypeFamilies, PolyKinds, RankNTypes, ConstraintKinds #-}

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, DataKinds #-}

module Data.Yoko.W where

import Data.Yoko.TypeBasics (Proxy)



data KProxy (k1 :: *) (k0 :: *) = KProxy



data family W (t :: k) (s :: k1 -> k0 -> *) :: k1 -> k0 -> *

newtype instance W (t :: *)           s p1 p0 = W0 (t       -> s p1 p0)
newtype instance W (t :: k0 -> *)      s p1 p0 = W1 (t    p0 -> s p1 p0)
newtype instance W (t :: k1 -> k0 -> *) s p1 p0 = W2 (t p1 p0 -> s p1 p0)

unW0 (W0 f) = f
unW1 (W1 f) = f
unW2 (W2 f) = f

data family W' (s :: k) :: (k1 -> k0 -> *) -> k1 -> k0 -> *

newtype instance W' (s :: *)           t p1 p0 = W'0 (t p1 p0 -> s      )
newtype instance W' (s :: k0 -> *)      t p1 p0 = W'1 (t p1 p0 -> s    p0)
newtype instance W' (s :: k1 -> k0 -> *) t p1 p0 = W'2 (t p1 p0 -> s p1 p0)

unW'0 (W'0 f) = f
unW'1 (W'1 f) = f
unW'2 (W'2 f) = f

data family Sym (t :: k) (s :: k) (p1 :: k1) (p0 :: k0) :: *

newtype instance Sym (t :: *)             s (p1 :: k1) (p0 :: k0) = Sym0 (t       -> s      )
newtype instance Sym (t :: k0 -> *)       s (p1 :: k1) (p0 :: k0) = Sym1 (t    p0 -> s    p0)
newtype instance Sym (t :: k1 -> k0 -> *) s (p1 :: k1) (p0 :: k0) = Sym2 (t p1 p0 -> s p1 p0)

unSym0 (Sym0 f) = f
unSym1 (Sym1 f) = f
unSym2 (Sym2 f) = f


class ComposeW (t :: k) (any :: KProxy k1 k0) where
  composeW  :: Proxy any -> (s (p1 :: k1) (p0 :: k0) -> s' p1 p0) -> W t s p1 p0 -> W t s' p1 p0
  composeW' :: Proxy any ->  W' t s' (p1 :: k1) (p0 :: k0) -> (s p1 p0 -> s' p1 p0) -> W' t s p1 p0
  sym :: Proxy any ->    W' t' s  (p1 :: k1) (p0 :: k0) -> W  t s p1 p0 -> Sym t t' p1 p0
  unSym :: Proxy any ->  W  t  s' (p1 :: k1) (p0 :: k0) -> W' t s p1 p0 -> s p1 p0 -> s' p1 p0
  composeSymW' :: Proxy any ->  Sym t t' (p1 :: k1) (p0 :: k0) -> W' t s p1 p0 -> W' t' s p1 p0
  composeWSym  :: Proxy any ->  W t' s (p1 :: k1) (p0 :: k0) -> Sym t t' p1 p0 -> W t s p1 p0
instance ComposeW (t :: *) (any :: KProxy k1 k0) where
  composeW _       f  (W0  g) = W0  (f . g)
  composeW' _ (W'0 f)      g  = W'0 (f . g)
  sym _       (W'0 f) (W0  g) = Sym0 (f . g)
  unSym _    (W0  f) (W'0 g) = f . g
  composeSymW' _ (Sym0 f) (W'0 g) = W'0 (f . g)
  composeWSym  _ (W0 f) (Sym0 g) = W0 (f . g)
instance ComposeW (t :: k0 -> *) (any :: KProxy k1 k0) where
  composeW _       f  (W1  g) = W1 (f . g)
  composeW' _ (W'1 f)      g  = W'1 (f . g)
  sym _      (W'1 f) (W1  g) = Sym1 (f . g)
  unSym _    (W1  f) (W'1 g) = f . g
  composeSymW' _ (Sym1 f) (W'1 g) = W'1 (f . g)
  composeWSym _ (W1 f) (Sym1 g) = W1 (f . g)
instance ComposeW (t :: k1 -> k0 -> *) (any1 :: KProxy k1 k0) where
  composeW _       f  (W2  g) = W2 (f . g)
  composeW' _ (W'2 f)      g = W'2 (f . g)
  sym _       (W'2 f) (W2  g) = Sym2 (f . g)
  unSym _    (W2  f) (W'2 g) = f . g
  composeSymW' _ (Sym2 f) (W'2 g) = W'2 (f . g)
  composeWSym  _ (W2 f) (Sym2 g) = W2 (f . g)
