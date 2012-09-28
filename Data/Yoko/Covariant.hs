{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, Rank2Types, ConstraintKinds, FlexibleInstances #-}

{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

module Data.Yoko.Mappings where

import GHC.Prim (Constraint)

import Data.Yoko.TypeBasics (Nat(..))



data Kind (k :: *) = Kind -- gets promoted to a singleton kind



class Trivial (a :: k); instance Trivial (a :: k)



type family   Prereq (con :: (k0 -> *) -> Constraint)
                               (t :: k0 -> *) (any :: Kind k0) :: k0 -> Constraint
type instance Prereq Covariant (t :: () -> *) (any :: Kind ()) = Trivial
type instance Prereq Covariant (t :: *  -> *) (any :: Kind *)  = Trivial

type family   Prereq2_0 (con :: (k1 -> k0 -> *) -> Constraint) (tgt :: Nat)
  (t :: k1 -> k0 -> *) (any :: Kind k0) :: k0 -> Constraint
type family   Prereq2_1 (con :: (k1 -> k0 -> *) -> Constraint) (tgt :: Nat)
  (t :: k1 -> k0 -> *) (any :: Kind k1) :: k1 -> Constraint
type instance Prereq2_0 Covariant2 tgt
  (t :: k1 -> () -> *) (any :: Kind ()) = Trivial
type instance Prereq2_0 Covariant2 tgt
  (t :: k1 -> *  -> *) (any :: Kind *)  = Trivial
type instance Prereq2_1 Covariant2 tgt
  (t :: () -> k0 -> *) (any :: Kind ()) = Trivial
type instance Prereq2_1 Covariant2 tgt
  (t :: *  -> k0 -> *) (any :: Kind *)  = Trivial



data    family   MapArg (t :: k)          :: k -> *
newtype instance MapArg (t :: *)             s = MapArg0 (t -> s)
newtype instance MapArg (t :: k0 -> *)       s = MapArg1 (forall p0. t p0 -> s p0)
newtype instance MapArg (t :: k1 -> k0 -> *) s = MapArg2 (forall p1 p0. t p1 p0 -> s p1 p0)



class Covariant t where
  covmap  :: Prereq Covariant t ('Kind :: Kind k0) a => MapArg (a :: k0) a' -> t a -> t a'
class Covariant2 t where
  covmap2 :: (Prereq2_1 Covariant2 (S Z) t ('Kind :: Kind k1) b, Prereq2_0 Covariant2 (S Z) t ('Kind :: Kind k0) a)
             => MapArg (b :: k1) b' -> t b (a :: k0) -> t b' a

class Covariant' t where
  covmap' :: (Prereq2_1 Covariant2 Z t ('Kind :: Kind k1) b, Prereq2_0 Covariant2 Z t ('Kind :: Kind k0) a)
              => MapArg (a :: k0) a' -> t (b :: k1) a -> t b a'

instance Covariant []               where covmap (MapArg0 f) = fmap f
instance Covariant Maybe            where covmap (MapArg0 f) = fmap f
instance Covariant IO               where covmap (MapArg0 f) = fmap f
instance Covariant (Either a)       where covmap (MapArg0 f) = fmap f
instance Covariant ((->) a)         where covmap (MapArg0 f) = fmap f
instance Covariant ((,,,,) a b c d) where covmap (MapArg0 f) (a, b, c, d, e) = (a, b, c, d, f e)
instance Covariant ((,,,)  a b c)   where covmap (MapArg0 f) (a, b, c, d) = (a, b, c, f d)
instance Covariant ((,,)   a b)     where covmap (MapArg0 f) (a, b, c) = (a, b, f c)
instance Covariant ((,)    a)       where covmap (MapArg0 f) = fmap f

instance Covariant2 Either         where covmap2 (MapArg0 f) = either (Left . f) Right
instance Covariant2 ((,,,,) a b c) where covmap2 (MapArg0 f) (a, b, c, d, e) = (a, b, c, f d, e)
instance Covariant2 ((,,,)  a b)   where covmap2 (MapArg0 f) (a, b, c, d) = (a, b, f c, d)
instance Covariant2 ((,,)   a)     where covmap2 (MapArg0 f) (a, b, c) = (a, f b, c)
instance Covariant2 (,)            where covmap2 (MapArg0 f) (a, b) = (f a, b)

-- one reason that these Covariant' instances below are well-typed is because
-- the corresponding Covariant instances are parametric in the argument
instance Covariant' Either         where covmap' = covmap
instance Covariant' ((,,,,) a b c) where covmap' = covmap
instance Covariant' ((,,,)  a b)   where covmap' = covmap
instance Covariant' ((,,)   a)     where covmap' = covmap
instance Covariant' (,)            where covmap' = covmap

-- a more general reason is because the context of each corresponding Covariant
-- instance is satisfied by the matching Prereq2_1 instance. This is more
-- explicit with the Covariant' instance for App below.

-- require @f@ to be Covariant because it is applied to an occurrence of @a@
newtype App f (a :: *) = App (f a) deriving Show

instance Covariant f => Covariant (App f) where covmap f (App x) = App (covmap f x)

type instance Prereq2_1 Covariant2 Z App (k1 :: Kind (* -> *)) = Covariant
instance Covariant' App where covmap' = covmap

-- NB @f@ only needs to be Covariant for the Covariant (App f) and Covariant'
-- App instances, not for the Covariant2 App instance
type instance Prereq2_1 Covariant2 (S Z) App (k1 :: Kind (* -> *)) = Trivial
instance Covariant2 App where covmap2 (MapArg1 f) (App x) = App (f x)

testApp0 = covmap  (MapArg0 length)           $ App (Just "nick")
testApp1 = covmap2 (MapArg1 (maybe [] (:[]))) $ App (Just "nick")
testApp2 = covmap' (MapArg0 length)           $ App (Just "nick")

-- I think we could alleviate the burden of these trivial Covariant' instances
-- if we had support for generic class implication declarations; this is what
-- we're specificying manually each time we declare the trivial Covariant'
-- instance



-- require @f@ to be Covariant because it is applied to a recursive occurrence
newtype Fix f = Fix (f (Fix f))
deriving instance Show (f (Fix f)) => Show (Fix f)

type instance Prereq Covariant Fix (k0 :: Kind (* -> *)) = Covariant
instance Covariant Fix where
  covmap (MapArg1 f) = w where
    w (Fix x) = Fix $ f $ covmap (MapArg0 w) x

testFix0 = covmap (MapArg1 $ maybe [] (:[])) $ Fix $ Just $ Fix $ Just $ Fix Nothing



-- require @f@ to be Covariant because it is applied to an occurrence of itself
newtype TwiceBool f = TwiceBool (f (f Bool))
deriving instance Show (f (f Bool)) => Show (TwiceBool f)

type instance Prereq Covariant TwiceBool (k0 :: Kind (* -> *)) = Covariant
instance Covariant TwiceBool where
  covmap (MapArg1 f) (TwiceBool x) = TwiceBool $ f $ covmap (MapArg0 f) x

testTwiceBool0 = covmap (MapArg1 $ maybe [] (:[])) $ TwiceBool $ Just $ Just True





-- observe that @f@ need not be Covariant
data Independent a f = Independent a (f Bool)
deriving instance (Show a, Show (f Bool)) => Show (Independent a f)

type instance Prereq Covariant (Independent b) (k0 :: Kind (* -> *)) = Trivial
type instance Prereq2_0 Covariant2 tgt Independent (k0 :: Kind (* -> *)) = Trivial

instance Covariant (Independent f) where
  covmap  (MapArg1 f) (Independent a x) = Independent a (f x)
instance Covariant2 Independent where
  covmap2 (MapArg0 f) (Independent a x) = Independent (f a) x
instance Covariant' Independent where covmap' = covmap

testIndependent0 =
  covmap' (MapArg1 $ foldr (const . Just) Nothing) $
  covmap2 (MapArg0 length) $
  covmap (MapArg1 $ maybe [] (:[])) $
  Independent "nick" (Just True)










type instance Prereq Contravariant (t :: () -> *) (any :: Kind ()) = Trivial
type instance Prereq Contravariant (t :: *  -> *) (any :: Kind *)  = Trivial

type instance Prereq2_0 Contravariant2 tgt
  (t :: k1 -> () -> *) (any :: Kind ()) = Trivial
type instance Prereq2_0 Contravariant2 tgt
  (t :: k1 -> *  -> *) (any :: Kind *)  = Trivial
type instance Prereq2_1 Contravariant2 tgt
  (t :: () -> k0 -> *) (any :: Kind ()) = Trivial
type instance Prereq2_1 Contravariant2 tgt
  (t :: *  -> k0 -> *) (any :: Kind *)  = Trivial



class Contravariant t where
  contramap  :: Prereq Contravariant t ('Kind :: Kind k0) a => MapArg (a' :: k0) a -> t a -> t a'
class Contravariant2 t where
  contramap2 :: (Prereq2_1 Contravariant2 (S Z) t ('Kind :: Kind k1) b, Prereq2_0 Contravariant2 (S Z) t ('Kind :: Kind k0) a)
             => MapArg (b' :: k1) b -> t b (a :: k0) -> t b' a

class Contravariant' t where
  contramap' :: (Prereq2_1 Contravariant2 Z t ('Kind :: Kind k1) b, Prereq2_0 Contravariant2 Z t ('Kind :: Kind k0) a)
              => MapArg (a' :: k0) a -> t (b :: k1) a -> t b a'

instance Contravariant2 (->) where contramap2 (MapArg0 f) = (. f)





instance Contravariant f => Contravariant (App f) where
  contramap arg (App x) = App $ contramap arg x

type instance Prereq2_1 Contravariant2 Z App (k1 :: Kind (* -> *)) = Contravariant
instance Contravariant' App where contramap' = contramap





newtype Into f (a :: *) = Into (f a -> Int)

instance Contravariant f => Covariant (Into f) where
  covmap arg (Into x) = Into $ x . contramap arg

instance Covariant f => Contravariant (Into f) where
  contramap arg (Into x) = Into $ x . covmap arg

testInto0 = (\(Into f) -> f [True, False, True]) $
  contramap (MapArg0 $ \x -> if x then 4 :: Int else 0) $
  Into sum
