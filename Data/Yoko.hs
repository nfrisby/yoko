{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, ConstraintKinds,
  ScopedTypeVariables, UndecidableInstances #-}

module Data.Yoko
  (Equal,
   module Data.Yoko.Representation,
   module Data.Yoko.TypeSums,
   module Data.Yoko.View,
   module Data.Yoko) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation
import Data.Yoko.View
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import qualified Data.Yoko.TypeSums as TypeSums
import Data.Yoko.Each

import Control.Arrow (right, (+++))




one :: (dc -> a) -> DCsOf (Range dc) (N dc) -> a
one = (. unDCsOf) . foldN

infixl 9 .|.   ;   f .|. g = one f ||| one g
infixr 8 .||   ;   f .|| g = one f ||| g
infixl 8 ||.   ;   f ||. g = f ||| one g






disbanded :: Embed (N dc) (DCs (Range dc)) => dc -> Disbanded (Range dc)
disbanded = DCsOf . TypeSums.inject

band :: forall t. Each (ConDCOf t) (DCs t) => Disbanded t -> t
band = each (Proxy :: Proxy (ConDCOf t)) rejoin

class (Range dc ~ t, DC dc) => ConDCOf t dc
instance (Range dc ~ t, DC dc) => ConDCOf t dc



inject :: Embed (N dc) sum => dc -> sum
inject = TypeSums.inject

partition :: Partition sum sub (sum :-: sub) =>
             DCsOf t sum -> Either (DCsOf t sub) (DCsOf t (sum :-: sub))
partition = (DCsOf +++ DCsOf) . TypeSums.partition . unDCsOf

project :: Partition sum (N dc) (sum :-: N dc) =>
           DCsOf (Range dc) sum -> Either dc (DCsOf (Range dc) (sum :-: N dc))
project = right DCsOf . TypeSums.project . unDCsOf



-- TODO need a MapSum just like MapRs, use a RPV for rep
reps :: EachGeneric sum => DCsOf t sum -> EachRep sum
reps = repEach . unDCsOf

type family EachRep sum
type instance EachRep (N a) = Rep a
type instance EachRep (a :+: b) = EachRep a :+: EachRep b
class EachGeneric sum where
  repEach :: sum -> EachRep sum   ;   objEach :: EachRep sum -> sum
instance Generic a => EachGeneric (N a) where
  repEach (N x) = rep x   ;   objEach = N . obj
instance (EachGeneric a, EachGeneric b) => EachGeneric (a :+: b) where
  repEach = mapPlus repEach repEach
  objEach = mapPlus objEach objEach





exact_case :: (DT t, Partition (DCs t) dcs (DCs t :-: dcs)) =>
  (DCsOf t (DCs t :-: dcs) -> a) -> t -> (DCsOf t dcs -> a) -> a
exact_case g x f =
  either f g $ partition $ disband x

ig_from x = reps $ disband x
