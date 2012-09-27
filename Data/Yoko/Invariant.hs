{-# LANGUAGE Rank2Types, PolyKinds #-}

{-# LANGUAGE TypeFamilies, GADTs, ConstraintKinds, DataKinds #-}

module Data.Yoko.Invariant where

import GHC.Prim (Constraint)



type family InvPrereq (t :: k) :: Constraint
type instance InvPrereq (t :: ()) = ()
type instance InvPrereq (t :: *) = ()
type instance InvPrereq (t :: k0 -> *) = Invariant t
type instance InvPrereq (t :: k1 -> k0 -> *) = Invariant2 t



data family InvArg (t :: k) :: k -> *
newtype instance InvArg (t :: *) s = InvArg0 (t -> s)
data instance InvArg (t :: k0 -> *) s where
  InvArg1 :: (Invariant t, Invariant s) => (forall p0. t p0 -> s p0) -> InvArg t s
data instance InvArg (t :: k1 -> k0 -> *) s where
  InvArg2 :: (Invariant2 t, Invariant2 s) => (forall p1 p0. t p1 p0 -> s p1 p0) -> InvArg t s


class Invariant t where
  invmap :: (InvPrereq a, InvPrereq b)
            => InvArg a b -> InvArg b a -> t a -> t b

class Invariant2 t where
  invmap2 :: (InvPrereq a, InvPrereq b, InvPrereq c, InvPrereq d)
             => InvArg b d -> InvArg d b -> InvArg a c -> InvArg c a -> t b a -> t d c

instance Invariant []               where invmap (InvArg0 f) _ = fmap f
instance Invariant Maybe            where invmap (InvArg0 f) _ = fmap f
instance Invariant IO               where invmap (InvArg0 f) _ = fmap f
instance Invariant (Either a)       where invmap (InvArg0 f) _ = fmap f
instance Invariant ((->) a)         where invmap (InvArg0 f) _ = fmap f
instance Invariant ((,,,,) a b c d) where invmap (InvArg0 f) _ (a, b, c, d, e) = (a, b, c, d, f e)
instance Invariant ((,,,)  a b c)   where invmap (InvArg0 f) _ (a, b, c, d) = (a, b, c, f d)
instance Invariant ((,,)   a b)     where invmap (InvArg0 f) _ (a, b, c) = (a, b, f c)
instance Invariant ((,)    a)       where invmap (InvArg0 f) _ = fmap f

instance Invariant2 Either         where invmap2 (InvArg0 f) _ (InvArg0 g) _ = either (Left . f) (Right . g)
instance Invariant2 (->)           where invmap2 _ (InvArg0 f') (InvArg0 g) _ h = g . h . f'
instance Invariant2 ((,,,,) a b c) where invmap2 (InvArg0 f) _ (InvArg0 g) _ (a, b, c, d, e) = (a, b, c, f d, g e)
instance Invariant2 ((,,,)  a b)   where invmap2 (InvArg0 f) _ (InvArg0 g) _ (a, b, c, d) = (a, b, f c, g d)
instance Invariant2 ((,,)   a)     where invmap2 (InvArg0 f) _ (InvArg0 g) _ (a, b, c) = (a, f b, g c)
instance Invariant2 (,)            where invmap2 (InvArg0 f) _ (InvArg0 g) _ (a, b) = (f a, g b)





{-
type Sym' a b = forall p1 p0. Sym a b p1 p0

class Invariant t where
  invmap :: Sym' a b -> Sym' b a -> t a -> t b

class Invariant2 t where
  invmap2 :: Sym' a c -> Sym' c a -> Sym' b d -> Sym' d b -> t a b -> t c d

instance Invariant []               where invmap (Sym0 f) _ = fmap f
instance Invariant Maybe            where invmap (Sym0 f) _ = fmap f
instance Invariant IO               where invmap (Sym0 f) _ = fmap f
instance Invariant (Either a)       where invmap (Sym0 f) _ = fmap f
instance Invariant ((->) a)         where invmap (Sym0 f) _ = fmap f
instance Invariant ((,,,,) a b c d) where invmap (Sym0 f) _ (a, b, c, d, e) = (a, b, c, d, f e)
instance Invariant ((,,,)  a b c)   where invmap (Sym0 f) _ (a, b, c, d) = (a, b, c, f d)
instance Invariant ((,,)   a b)     where invmap (Sym0 f) _ (a, b, c) = (a, b, f c)
instance Invariant ((,)    a)       where invmap (Sym0 f) _ = fmap f

instance Invariant2 Either         where invmap2 (Sym0 f) _ (Sym0 g) _ = either (Left . f) (Right . g)
instance Invariant2 (->)           where invmap2 _ (Sym0 f') (Sym0 g) _ h = g . h . f'
instance Invariant2 ((,,,,) a b c) where invmap2 (Sym0 f) _ (Sym0 g) _ (a, b, c, d, e) = (a, b, c, f d, g e)
instance Invariant2 ((,,,)  a b)   where invmap2 (Sym0 f) _ (Sym0 g) _ (a, b, c, d) = (a, b, f c, g d)
instance Invariant2 ((,,)   a)     where invmap2 (Sym0 f) _ (Sym0 g) _ (a, b, c) = (a, f b, g c)
instance Invariant2 (,)            where invmap2 (Sym0 f) _ (Sym0 g) _ (a, b) = (f a, g b)
-}
