{-# LANGUAGE TypeOperators, LambdaCase, FlexibleContexts, UndecidableInstances, PolyKinds #-}

module Data.Yoko.Invariant
  (module Data.Yoko.Invariant, module Data.Functor.Invariant) where

import Data.Yoko.W
import Data.YokoRaw

import Data.Functor.Invariant





gen_invmap :: (Invariant2 (DCs t), DT t, AreDCsOf t (DCs t)) =>
              (a -> b) -> (b -> a) -> t a -> t b
gen_invmap f f' = unW1 . band . invmap2 id id f f' . disband . W1

gen_invmap2 :: (Invariant2 (DCs t), DT t, AreDCsOf t (DCs t)) =>
               (a -> c) -> (c -> a) -> (b -> d) -> (d -> b) -> t a b -> t c d
gen_invmap2 f f' g g' = unW2 . band . invmap2 f f' g g' . disband . W2





instance Invariant2 U where
  invmap2 _ _ _ _ _ = U

instance (Invariant2 l, Invariant2 r) => Invariant2 (l :*: r) where
  invmap2 f f' g g' (l :*: r) = invmap2 f f' g g' l :*: invmap2 f f' g g' r

instance (Invariant2 r) => Invariant2 (C dc r) where
  invmap2 f f' g g' (C x) = C $ invmap2 f f' g g' x


-- can optimize for * and * -> *, but I'm favoring terseness
instance (Invariant2 (Rep dc), Generic dc) => Invariant2 (N dc) where
  invmap2 f f' g g'  = mapN $ obj . invmap2 f f' g g' . rep

instance (Invariant2 l, Invariant2 r) => Invariant2 (l :+: r) where
  invmap2 f f' g g' = \case
    L x -> L $ invmap2 f f' g g' x
    R x -> R $ invmap2 f f' g g' x

instance Invariant2 Void where invmap2 = error "invmap2 @Void"



instance Invariant2 (T0 v t) where
  invmap2 _ _ _ _ (T0 x) = T0 x

instance (Invariant t, Invariant2 r) => Invariant2 (T1 v t r) where
  invmap2 f f' g g' (T1 x) = T1 $ invmap (invmap2 f f' g g') (invmap2 f' f g' g) x

instance (Invariant2 t, Invariant2 r, Invariant2 s) => Invariant2 (T2 v t r s) where
  invmap2 f f' g g' (T2 x) = T2 $ invmap2 (invmap2 f f' g g') (invmap2 f' f g' g) (invmap2 f f' g g') (invmap2 f' f g' g) x



instance Invariant2 Par1 where invmap2 f _ _ _ (Par1 x) = Par1 (f x)
instance Invariant2 Par0 where invmap2 _ _ g _ (Par0 x) = Par0 (g x)
