{-# LANGUAGE TypeFamilies, TypeOperators, TemplateHaskell,
  UndecidableInstances, EmptyDataDecls #-}

module Data.Yoko.Representation where

import Data.Yoko.TypeBasics



data U = U
infixr 6 :*:
data a :*: b = a :*: b

data Void
newtype N a = N a
infixl 6 :+:
data a :+: b = L a | R b deriving (Eq, Show, Ord, Read)



newtype Par1 f a = Par1 (f a)
newtype Par2 f a b = Par2 (f a b)



newtype Dep a = Dep a
newtype Rec a = Rec a



type family Rep a



class Generic a where rep :: a -> Rep a; obj :: Rep a -> a


unDep (Dep x) = x

unRec (Rec x) = x
mapRec f (Rec x) = Rec (f x)

unPar1 (Par1 x) = x
unPar2 (Par2 x) = x

unN (N x) = x
foldN f = f . unN

mapN f = N . foldN f

foldPlus f g x = case x of
  L x -> f x   ;   R x -> g x

mapPlus f g = foldPlus (L . f) (R . g)

mapTimes f g (a :*: b) = f a :*: g b

foldTimes comb f g (a :*: b) = comb (f a) (g b)



type family DistMaybePlus a b
type instance DistMaybePlus Nothing b = b
type instance DistMaybePlus (Just a) Nothing = Just a
type instance DistMaybePlus (Just a) (Just b) = Just (a :+: b)



data Z; data S n
type family Add n m
type instance Add Z m = m
type instance Add (S n) m = S (Add n m)

type family CountRs rep
type instance CountRs (Dep a) = Z
type instance CountRs (Rec a) = S Z
type instance CountRs U = Z
type instance CountRs (a :*: b) = Add (CountRs a) (CountRs b)





-- carrying around the original type supplants many ascriptions
newtype DCsOf t sum = DCsOf sum   ;   unDCsOf (DCsOf x) = x
instance Functor (DCsOf t) where fmap f = DCsOf . f . unDCsOf

infixl 6 |||
(|||) :: (DCsOf t sumL -> a) -> (DCsOf t sumR -> a) ->
         DCsOf t (sumL :+: sumR) -> a
(|||) f g = foldPlus f g . mapPlus DCsOf DCsOf . unDCsOf





concat `fmap` mapM derive [''Dep, ''Rec, ''U, ''(:*:), ''N, ''(:+:)]
