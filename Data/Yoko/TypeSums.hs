{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, TypeOperators, PolyKinds, DataKinds #-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, EmptyDataDecls #-}

{-# OPTIONS_GHC -fcontext-stack=250 #-}

{- |

Module      :  Data.Yoko.TypeSums
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

This is the technical core of @yoko@'s cheap constructor subsets.

-}

module Data.Yoko.TypeSums (DistMaybePlus, (:-:),
                           Embed, embed, inject0, inject1, inject2,
                           Partition, project0, project1, project2, partition) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation

import Control.Arrow (left)






class Embed sub sup where embed_ :: sub (p1 :: *) (p0 :: *) -> sup p1 p0

embed :: Embed sub sup => sub p1 p0 -> sup p1 p0
embed = embed_

inject0 :: Embed (N0 a) sum => a -> sum p1 p0
inject0 = embed . N0

inject1 :: Embed (N1 a) sum => a p0 -> sum p1 p0
inject1 = embed . N1

inject2 :: Embed (N2 a) sum => a p1 p0 -> sum p1 p0
inject2 = embed . N2



class Partition sup subL subR where partition_ :: sup (p1 :: *) (p0 :: *) -> Either (subL p1 p0) (subR p1 p0)

partition :: Partition sup sub (sup :-: sub) =>
             sup p1 p0 -> Either (sub p1 p0) ((sup :-: sub) p1 p0)
partition = partition_

project0 :: Partition sum (N0 a) (sum :-: N0 a) => sum p1 p0 -> Either a ((sum :-: N0 a) p1 p0)
project0 = left unN0 . partition_

project1 :: Partition sum (N1 a) (sum :-: N1 a) => sum p1 p0 -> Either (a p0) ((sum :-: N1 a) p1 p0)
project1 = left unN1 . partition_

project2 :: Partition sum (N2 a) (sum :-: N2 a) => sum p1 p0 -> Either (a p1 p0) ((sum :-: N2 a) p1 p0)
project2 = left unN2 . partition_





data Path k = Here k | TurnLeft (Path k) | TurnRight (Path k)

type family Locate (a :: k) (sum :: * -> * -> *) :: Maybe (Path k)
type instance Locate a (N0 x)     = If (Equal x a) (Just (Here a)) Nothing
type instance Locate a (N1 x)     = If (Equal x a) (Just (Here a)) Nothing
type instance Locate a (N2 x)     = If (Equal x a) (Just (Here a)) Nothing
type instance Locate a (l :+: r) =
  MaybeMap TurnLeft (Locate a l) `MaybePlus1`
  MaybeMap TurnRight (Locate a r)
type instance Locate a Void  = Nothing

type Elem a sum = IsJust (Locate a sum)





class InjectAt path n sum where injectAt :: Proxy path -> n (p1 :: *) (p0 :: *) -> sum p1 p0
instance InjectAt (Here a) (N0 a) (N0 a) where injectAt _ = id
instance InjectAt (Here a) (N1 a) (N1 a) where injectAt _ = id
instance InjectAt (Here a) (N2 a) (N2 a) where injectAt _ = id
instance InjectAt path a l => InjectAt (TurnLeft path) a (l :+: r) where
  injectAt _ = L . injectAt (Proxy :: Proxy path)
instance InjectAt path a r => InjectAt (TurnRight path) a (l :+: r) where
  injectAt _ = R . injectAt (Proxy :: Proxy path)





instance (Locate x sup ~ Just path, InjectAt path (N0 x) sup) => Embed (N0 x) sup where
  embed_ = injectAt (Proxy :: Proxy path)
instance (Locate x sup ~ Just path, InjectAt path (N1 x) sup) => Embed (N1 x) sup where
  embed_ = injectAt (Proxy :: Proxy path)
instance (Locate x sup ~ Just path, InjectAt path (N2 x) sup) => Embed (N2 x) sup where
  embed_ = injectAt (Proxy :: Proxy path)
instance (Embed l sup, Embed r sup) => Embed (l :+: r) sup where
  embed_ = foldPlus embed embed





infixl 6 :-:
type family (:-:) (sum :: * -> * -> *) (sum2 :: * -> * -> *) :: * -> * -> *
type instance (:-:) (N0 x)    sum2 = If (Elem x sum2) Void (N0 x)
type instance (:-:) (N1 x)    sum2 = If (Elem x sum2) Void (N1 x)
type instance (:-:) (N2 x)    sum2 = If (Elem x sum2) Void (N2 x)
type instance (:-:) (l :+: r) sum2 = Combine (l :-: sum2) (r :-: sum2)


type family Combine (sum :: * -> * -> *) (sum2 :: * -> * -> *) :: * -> * -> *
type instance Combine Void x = x
type instance Combine (N0 x) Void = N0 x
type instance Combine (N0 x) (N0 y) = N0 x :+: N0 y
type instance Combine (N0 x) (l :+: r) = N0 x :+: (l :+: r)
type instance Combine (N1 x) Void = N1 x
type instance Combine (N1 x) (N1 y) = N1 x :+: N1 y
type instance Combine (N1 x) (l :+: r) = N1 x :+: (l :+: r)
type instance Combine (N2 x) Void = N2 x
type instance Combine (N2 x) (N2 y) = N2 x :+: N2 y
type instance Combine (N2 x) (l :+: r) = N2 x :+: (l :+: r)
type instance Combine (l :+: r) Void = l :+: r
type instance Combine (l :+: r) (N0 y) = (l :+: r) :+: N0 y
type instance Combine (l :+: r) (N1 y) = (l :+: r) :+: N1 y
type instance Combine (l :+: r) (N2 y) = (l :+: r) :+: N2 y
type instance Combine (ll :+: rl) (lr :+: rr) = (ll :+: rl) :+: (lr :+: rr)



class Partition_N (bn :: Bool) x subL subR where
  partition_N :: Proxy bn -> x (p1 :: *) (p0 :: *) -> Either (subL p1 p0) (subR p1 p0)

instance (Partition_N (Elem x subL) (N0 x) subL subR
         ) => Partition (N0 x) subL subR where
  partition_ = partition_N (Proxy :: Proxy (Elem x subL))

instance (Partition_N (Elem x subL) (N1 x) subL subR
         ) => Partition (N1 x) subL subR where
  partition_ = partition_N (Proxy :: Proxy (Elem x subL))

instance (Partition_N (Elem x subL) (N2 x) subL subR
         ) => Partition (N2 x) subL subR where
  partition_ = partition_N (Proxy :: Proxy (Elem x subL))

instance (Partition a subL subR, Partition b subL subR
         ) => Partition (a :+: b) subL subR where
  partition_ = foldPlus partition_ partition_



instance Embed x subR => Partition_N False x subL subR where
  partition_N _ = Right . embed
instance Embed x subL => Partition_N True  x subL subR where
  partition_N _ = Left  . embed
