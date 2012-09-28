{-# LANGUAGE TypeOperators, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, TypeFamilies,
  PolyKinds #-}

module Data.Yoko.Traversable
 (module Data.Yoko.Traversable, module Data.Traversable) where

import Data.Yoko.W
import Data.YokoRaw

import Control.Applicative
import Data.Traversable (Traversable, traverse)



gen_traverse :: (Traversable2Sum (DCs t) t, DT t, Applicative i) =>
              (a -> i b) -> t a -> i (t b)
gen_traverse f = fmap unW1 . traverse2sum (error "gen_traverse @Par1") f . disband . W1

gen_traverse2 :: (Traversable2Sum (DCs t) t, DT t, Applicative i) =>
               (b -> i d) -> (a -> i c) -> t b a -> i (t d c)
gen_traverse2 f g = fmap unW2 . traverse2sum f g . disband . W2



gen_fmap :: (Traversable2Sum (DCs t) t, DT t) => (a -> b) -> t a -> t b
gen_fmap f = unW1 . runId . traverse2sum (error "gen_traverse @Par1") (Id . f) . disband . W1


class Traversable2 t where
  traverse2 :: Applicative i => (b -> i d) -> (a -> i c) -> t b a -> i (t d c)





class Traversable2Sum dcs (t :: k) where
  traverse2sum :: Applicative i => (b -> i d) -> (a -> i c) -> dcs b a -> i (W t d c)


instance (Traversable2Sum l t, Traversable2Sum r t) => Traversable2Sum (l :+: r) t where
  traverse2sum f g = foldPlus (traverse2sum f g) (traverse2sum f g)
instance Traversable2Sum Void t where traverse2sum = error "traverse2 @Void"
-- can optimize for * and * -> *, but I'm favoring terseness
instance (Traversable2 (Rep dc), DC dc, Codomain dc ~ t) => Traversable2Sum (N dc) t where
  traverse2sum f g = fmap (rejoin . ascribe . obj) . traverse2 f g . rep . unN
    where ascribe :: W dc p1 p0 -> W dc p1 p0
          ascribe = id




instance Traversable2 U where traverse2 _ _ _ = pure U

instance (Traversable2 l, Traversable2 r) => Traversable2 (l :*: r) where
  traverse2 f g (l :*: r) = (:*:) <$> traverse2 f g l <*> traverse2 f g r

instance (Traversable2 r) => Traversable2 (C dc r) where
  traverse2 f g (C x) = C <$> traverse2 f g x

instance Traversable2 (T0 v t) where
  traverse2 _ _ (T0 x) = pure $ T0 x

instance (Traversable t, Traversable2 r) => Traversable2 (T1 v t r) where
  traverse2 f g (T1 x) = T1 <$> traverse (traverse2 f g) x

instance (Traversable2 t, Traversable2 r, Traversable2 s) => Traversable2 (T2 v t r s) where
  traverse2 f g (T2 x) = T2 <$> traverse2 (traverse2 f g) (traverse2 f g) x



instance Traversable2 Par1 where traverse2 f _ (Par1 x) = Par1 <$> f x
instance Traversable2 Par0 where traverse2 _ g (Par0 x) = Par0 <$> g x
