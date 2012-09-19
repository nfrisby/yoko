{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, TypeOperators,
  NoPolyKinds, DataKinds #-}

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
                           Embed, embed, inject,
                           Partition, project, partition) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation

import Control.Arrow (left)






class Embed sub sup where embed_ :: sub p1 p0 -> sup p1 p0

embed :: Embed sub sup => sub p1 p0 -> sup p1 p0
embed = embed_

inject :: Embed (N a) sum => a p1 p0 -> sum p1 p0
inject = embed . N



class Partition sup subL subR where partition_ :: sup p1 p0 -> Either (subL p1 p0) (subR p1 p0)

partition :: Partition sup sub (sup :-: sub) =>
             sup p1 p0 -> Either (sub p1 p0) ((sup :-: sub) p1 p0)
partition = partition_

project :: Partition sum (N a) (sum :-: N a) => sum p1 p0 -> Either (a p1 p0) ((sum :-: N a) p1 p0)
project = left unN . partition_





data Here (a :: * -> * -> *)
data TurnLeft  path
data TurnRight path

type family Locate (a :: * -> * -> *) (sum :: * -> * -> *) :: Maybe *
type instance Locate a (N x)     = If (Equal x a) (Just (Here a)) Nothing
type instance Locate a (l :+: r) =
  MaybeMap TurnLeft (Locate a l) `MaybePlus1`
  MaybeMap TurnRight (Locate a r)
type instance Locate a Void      = Nothing

type Elem a sum = IsJust (Locate a sum)





class InjectAt path a sum where injectAt :: Proxy path -> a p1 p0 -> sum p1 p0
instance InjectAt (Here a) a (N a) where injectAt _ = N
instance InjectAt path a l => InjectAt (TurnLeft path) a (l :+: r) where
  injectAt _ = L . injectAt (Proxy :: Proxy path)
instance InjectAt path a r => InjectAt (TurnRight path) a (l :+: r) where
  injectAt _ = R . injectAt (Proxy :: Proxy path)





instance (Locate x sup ~ Just path, InjectAt path x sup) => Embed (N x) sup where
  embed_ = injectAt (Proxy :: Proxy path) . unN
instance (Embed l sup, Embed r sup) => Embed (l :+: r) sup where
  embed_ = foldPlus embed embed





infixl 6 :-:
type family (:-:) (sum :: * -> * -> *) (sum2 :: * -> * -> *) :: * -> * -> *
type instance (:-:) (N x) sum2 = If (Elem x sum2) Void (N x)
type instance (:-:) (l :+: r) sum2 = Combine (l :-: sum2) (r :-: sum2)


type family Combine (sum :: * -> * -> *) (sum2 :: * -> * -> *) :: * -> * -> *
type instance Combine Void x = x
type instance Combine (N x) Void = N x
type instance Combine (N x) (N y) = N x :+: N y
type instance Combine (N x) (l :+: r) = N x :+: (l :+: r)
type instance Combine (l :+: r) Void = l :+: r
type instance Combine (l :+: r) (N y) = (l :+: r) :+: N y
type instance Combine (ll :+: rl) (lr :+: rr) = (ll :+: rl) :+: (lr :+: rr)



class Partition_N (bn :: Bool) x subL subR where
  partition_N :: Proxy bn -> N x p1 p0 -> Either (subL p1 p0) (subR p1 p0)

instance (Partition_N (Elem x subL) x subL subR
         ) => Partition (N x) subL subR where
  partition_ = partition_N (Proxy :: Proxy (Elem x subL))

instance (Partition a subL subR, Partition b subL subR
         ) => Partition (a :+: b) subL subR where
  partition_ = foldPlus partition_ partition_



instance Embed (N x) subR => Partition_N False x subL subR where
  partition_N _ = Right . embed
instance Embed (N x) subL => Partition_N True  x subL subR where
  partition_N _ = Left  . embed
