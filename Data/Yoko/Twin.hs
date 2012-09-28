{-# LANGUAGE PolyKinds, TypeOperators, FlexibleContexts, UndecidableInstances, DefaultSignatures, Rank2Types, MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}

module Data.Yoko.Twin where

import Data.YokoRaw

import Data.Monoid (Monoid, mappend, mempty, All(..))
import Control.Applicative ((<$>), (<*>))




gen_eq :: (DT t, Zip2 Eq (DCs t)) => t -> t -> Bool
gen_eq l r = maybe False getAll $
  zip2 (Proxy :: Proxy Eq) (\x y -> Just (All (x == y)))
    (error "gen_eq @Par1") (error "gen_eq @Par1")
    (disband $ W0 l) (disband $ W0 r)

gen_zip1 :: (DT t, Zip2 c (DCs t), Monoid m) => Proxy c -> (forall a. c a => a -> a -> Maybe m) -> (a -> a' -> Maybe m) -> t a -> t a' -> Maybe m
gen_zip1 pc dep f l r = zip2 pc dep (error "gen_zip @Par1") f (disband $ W1 l) (disband $ W1 r)

gen_zip2 :: (DT t, Zip2 c (DCs t), Monoid m) => Proxy c -> (forall a. c a => a -> a -> Maybe m) -> (b -> b' -> Maybe m) -> (a -> a' -> Maybe m) -> t b a -> t b' a' -> Maybe m
gen_zip2 pc dep f g l r = zip2 pc dep f g (disband $ W2 l) (disband $ W2 r)




class Zip1 c t where
  zip1 :: Monoid m => Proxy c -> (forall a. c a => a -> a -> Maybe m) -> (a -> a' -> Maybe m) -> t a -> t a' -> Maybe m
  default zip1 :: (DT t, Zip2 c (DCs t), Monoid m) => Proxy c -> (forall a. c a => a -> a -> Maybe m) -> (a -> a' -> Maybe m) -> t a -> t a' -> Maybe m
  zip1 = gen_zip1

class Zip2 c t where
  zip2 :: Monoid m => Proxy c -> (forall a. c a => a -> a -> Maybe m) ->
          (b -> b' -> Maybe m) -> (a -> a' -> Maybe m) ->
          t b a -> t b' a' -> Maybe m
  default zip2 :: (DT t, Zip2 c (DCs t), Monoid m) => Proxy c -> (forall a. c a => a -> a -> Maybe m) -> (b -> b' -> Maybe m) -> (a -> a' -> Maybe m) -> t b a -> t b' a' -> Maybe m
  zip2 = gen_zip2

instance (Zip2 c l, Zip2 c r) => Zip2 c (l :+: r) where
  zip2 pc dep f g (L l) (L r) = zip2 pc dep f g l r
  zip2 pc dep f g (R l) (R r) = zip2 pc dep f g l r
  zip2 _  _   _ _ _     _     = Nothing
instance Zip2 c Void where zip2 _ _ _ _ _ _ = Just mempty
instance (Generic dc, Zip2 c (Rep dc)) => Zip2 c (N dc) where
  zip2 pc dep f g (N l) (N r) = zip2 pc dep f g (rep l) (rep r)

instance (Zip2 c l, Zip2 c r) => Zip2 c (l :*: r) where
  zip2 pc dep f g (ll :*: lr) (rl :*: rr) = mappend <$> zip2 pc dep f g ll rl <*> zip2 pc dep f g lr rr
instance Zip2 c U where zip2 _ _ _ _ _ _ = Just mempty
instance Zip2 c r => Zip2 c (C dc r) where zip2 pc dep f g (C l) (C r) = zip2 pc dep f g l r

instance c t => Zip2 c (T0 v t) where zip2 _ dep _ _ (T0 l) (T0 r) = dep l r
instance (Zip1 c t, Zip2 c a) => Zip2 c (T1 v t a) where
  zip2 pc dep f g (T1 l) (T1 r) = zip1 pc dep (zip2 pc dep f g) l r
instance (Zip2 c t, Zip2 c b, Zip2 c a) => Zip2 c (T2 v t b a) where
  zip2 pc dep f g (T2 l) (T2 r) = zip2 pc dep (zip2 pc dep f g) (zip2 pc dep f g) l r

instance Zip2 c Par1 where zip2 _ _ f _ (Par1 l) (Par1 r) = f l r
instance Zip2 c Par0 where zip2 _ _ _ g (Par0 l) (Par0 r) = g l r
