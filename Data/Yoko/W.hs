{-# LANGUAGE TypeFamilies, PolyKinds #-}

module Data.Yoko.W where



data family W (t :: k) :: * -> * -> *

newtype instance W (t :: *)           p1 p0 = W0  t
newtype instance W (t :: * -> *)      p1 p0 = W1 (t    p0)
newtype instance W (t :: * -> * -> *) p1 p0 = W2 (t p1 p0)

unW0 (W0 x) = x
unW1 (W1 x) = x
unW2 (W2 x) = x

foldW0 f (W0 x) = f x
foldW1 f (W1 x) = f x
foldW2 f (W2 x) = f x

mapW0 f = foldW0 (W0 . f)
mapW1 f = foldW1 (W1 . f)
mapW2 f = foldW2 (W2 . f)

unfoldW0 f = W0 . f
unfoldW1 f = W1 . f
unfoldW2 f = W2 . f
