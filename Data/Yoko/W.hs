{-# LANGUAGE TypeFamilies, PolyKinds, RankNTypes, ConstraintKinds #-}

{-# LANGUAGE FlexibleInstances #-}

module Data.Yoko.W where



data family W (t :: k) :: (* -> * -> *) -> * -> * -> *

newtype instance W (t :: *)           s p1 p0 = W0 (t       -> s p1 p0)
newtype instance W (t :: * -> *)      s p1 p0 = W1 (t    p0 -> s p1 p0)
newtype instance W (t :: * -> * -> *) s p1 p0 = W2 (t p1 p0 -> s p1 p0)

unW0 (W0 f) = f
unW1 (W1 f) = f
unW2 (W2 f) = f

class ComposeW t where composeW :: (s p1 p0 -> s' p1 p0) -> W t s p1 p0 -> W t s' p1 p0
instance ComposeW (t :: *) where composeW f (W0 g) = W0 (f . g)
instance ComposeW (t :: * -> *) where composeW f (W1 g) = W1 (f . g)
instance ComposeW (t :: * -> * -> *) where composeW f (W2 g) = W2 (f . g)

data family W' (s :: k) :: (* -> * -> *) -> * -> * -> *

newtype instance W' (s :: *)           t p1 p0 = W'0 (t p1 p0 -> s      )
newtype instance W' (s :: * -> *)      t p1 p0 = W'1 (t p1 p0 -> s    p0)
newtype instance W' (s :: * -> * -> *) t p1 p0 = W'2 (t p1 p0 -> s p1 p0)

unW'0 (W'0 f) = f
unW'1 (W'1 f) = f
unW'2 (W'2 f) = f

class ComposeW' s where composeW' :: W' s t' p1 p0 -> (t p1 p0 -> t' p1 p0) -> W' s t p1 p0
instance ComposeW' (s :: *) where composeW' (W'0 f) g = W'0 (f . g)
instance ComposeW' (s :: * -> *) where composeW' (W'1 f) g = W'1 (f . g)
instance ComposeW' (s :: * -> * -> *) where composeW' (W'2 f) g = W'2 (f . g)

data family Sym (t :: k) :: k ->  * -> * -> *

newtype instance Sym (t :: *)           s p1 p0 = Sym0 (t       -> s      )
newtype instance Sym (t :: * -> *)      s p1 p0 = Sym1 (t    p0 -> s    p0)
newtype instance Sym (t :: * -> * -> *) s p1 p0 = Sym2 (t p1 p0 -> s p1 p0)

unSym0 (Sym0 f) = f
unSym1 (Sym1 f) = f
unSym2 (Sym2 f) = f
