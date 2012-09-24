{-# LANGUAGE TypeOperators, LambdaCase, FlexibleContexts, UndecidableInstances, PolyKinds #-}

module Data.Yoko.Invariant
  (module Data.Yoko.Invariant, module Data.Functor.Invariant) where

import Data.Yoko.Each
import Data.YokoRaw

import Data.Functor.Invariant





gen_invmap :: (Invariant2 (DCs t), DT1 t, Each1 (ConDCOf1 t) (DCs t)) =>
              (a -> b) -> (b -> a) -> t a -> t b
gen_invmap f f' = band1 . invmap2 id id f f' . disband1

gen_invmap2 :: (Invariant2 (DCs t), DT2 t, Each2 (ConDCOf2 t) (DCs t)) =>
               (a -> c) -> (c -> a) -> (b -> d) -> (d -> b) -> t a b -> t c d
gen_invmap2 f f' g g' = band2 . invmap2 f f' g g' . disband2





instance Invariant2 U where
  invmap2 _ _ _ _ _ = U

instance (Invariant2 l, Invariant2 r) => Invariant2 (l :*: r) where
  invmap2 f f' g g' (l :*: r) = invmap2 f f' g g' l :*: invmap2 f f' g g' r

instance (Invariant2 r) => Invariant2 (C dc r) where
  invmap2 f f' g g' (C x) = C $ invmap2 f f' g g' x



instance Invariant2 (N0 dc) where
  invmap2 _ _ _ _ (N0 x) = N0 x

instance (Invariant2 (Rep dc), Generic1 dc) => Invariant2 (N1 dc) where
  invmap2 _ _ g g' (N1 x) = N1 $ obj1 $ invmap2 id id g g' $ rep1 x

instance (Invariant2 (Rep dc), Generic2 dc) => Invariant2 (N2 dc) where
  invmap2 f f' g g' (N2 x) = N2 $ obj2 $ invmap2 f f' g g' $ rep2 x

instance (Invariant2 l, Invariant2 r) => Invariant2 (l :+: r) where
  invmap2 f f' g g' = \case
    L x -> L $ invmap2 f f' g g' x
    R x -> R $ invmap2 f f' g g' x

instance Invariant2 Void where invmap2 = error "invmap2 @Void"



instance Invariant2 (Rec0 lbl t) where
  invmap2 _ _ _ _ (Rec0 x) = Rec0 x

instance (Invariant t, Invariant2 r) => Invariant2 (Rec1 lbl t r) where
  invmap2 f f' g g' (Rec1 x) = Rec1 $ invmap (invmap2 f f' g g') (invmap2 f' f g' g) x

instance (Invariant2 t, Invariant2 r, Invariant2 s) => Invariant2 (Rec2 lbl t r s) where
  invmap2 f f' g g' (Rec2 x) = Rec2 $ invmap2 (invmap2 f f' g g') (invmap2 f' f g' g) (invmap2 f f' g g') (invmap2 f' f g' g) x

instance Invariant2 (Dep0 t) where
  invmap2 _ _ _ _ (Dep0 x) = Dep0 x

instance (Invariant t, Invariant2 r) => Invariant2 (Dep1 t r) where
  invmap2 f f' g g' (Dep1 x) = Dep1 $ invmap (invmap2 f f' g g') (invmap2 f' f g' g) x

instance (Invariant2 t, Invariant2 r, Invariant2 s) => Invariant2 (Dep2 t r s) where
  invmap2 f f' g g' (Dep2 x) = Dep2 $ invmap2 (invmap2 f f' g g') (invmap2 f' f g' g) (invmap2 f f' g g') (invmap2 f' f g' g) x



instance Invariant2 Par1 where invmap2 f _ _ _ (Par1 x) = Par1 (f x)
instance Invariant2 Par0 where invmap2 _ _ g _ (Par0 x) = Par0 (g x)
