{-# LANGUAGE TypeOperators, FlexibleContexts, UndecidableInstances, DefaultSignatures #-}

module Data.Yoko.Foldable
  (module Data.Yoko.Foldable, module Data.Foldable) where

import Data.YokoRaw

import Data.Monoid
import Data.Foldable (Foldable, foldMap)



gen_foldMap :: (DT t, Foldable2 (DCs t), Monoid m) => (a -> m) -> t a -> m
gen_foldMap f = foldMap2 (error "Data.Yoko.Foldable.gen_foldMap @Par1") f . disband . W1

gen_foldMap2 :: (DT t, Foldable2 (DCs t), Monoid m) => (b -> m) -> (a -> m) -> t b a -> m
gen_foldMap2 f g = foldMap2 f g . disband . W2



class Foldable2 t where
  foldMap2 :: Monoid m => (b -> m) -> (a -> m) -> t b a -> m
  default foldMap2 :: (DT t, Foldable2 (DCs t), Monoid m)
                   => (b -> m) -> (a -> m) -> t b a -> m
  foldMap2 = gen_foldMap2

instance Foldable2 Void where foldMap2 _ _ _ = mempty
instance (Foldable2 l, Foldable2 r) => Foldable2 (l :+: r) where
  foldMap2 f g = foldPlus (foldMap2 f g) (foldMap2 f g)
instance (Generic dc, Foldable2 (Rep dc)) => Foldable2 (N dc) where
  foldMap2 f g = foldMap2 f g . rep . unN

instance Foldable2 U where foldMap2 _ _ _ = mempty
instance (Foldable2 l, Foldable2 r) => Foldable2 (l :*: r) where
  foldMap2 f g (l :*: r) = foldMap2 f g l `mappend` foldMap2 f g r
instance Foldable2 r => Foldable2 (C dc r) where
  foldMap2 f g = foldC (foldMap2 f g)

instance Foldable2 (T0 v t) where foldMap2 _ _ = mempty
instance (Foldable t, Foldable2 a) => Foldable2 (T1 v t a) where
  foldMap2 f g = foldMap (foldMap2 f g) . unT1
instance (Foldable2 t, Foldable2 b, Foldable2 a) => Foldable2 (T2 v t b a) where
  foldMap2 f g = foldMap2 (foldMap2 f g) (foldMap2 f g) . unT2

instance Foldable2 Par1 where foldMap2 f _ = f . unPar1
instance Foldable2 Par0 where foldMap2 _ g = g . unPar0
