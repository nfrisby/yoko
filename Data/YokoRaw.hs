{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables,
  UndecidableInstances, PolyKinds, DataKinds, ConstraintKinds #-}

{- |

Module      :  Data.YokoRaw
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

This is the entire library, excluding the fancy builder of precise cases from
"Data.Yoko.SmartPreciseCase".

-}

module Data.YokoRaw
  (module Data.Yoko.Representation,
   module Data.Yoko.View,
   module Data.Yoko.TypeBasics,
   module Data.Yoko.W,
   -- * Building fields type consumers
   one, (|||), (||.), (.||), (.|.),
   -- * Operations on disbanded data types
   disbanded, AreDCsOf, band, precise_case0,
   -- * Operations on sums of fields types
   (:-:), Embed, Partition,
   embed, inject, partition, project,
   -- * Forgetting @yoko@'s extra structure
   reps, EachGeneric, EachRep, ig_from) where

import Data.Yoko.W
import Data.Yoko.TypeBasics
import Data.Yoko.Representation
import Data.Yoko.View
import Data.Yoko.Invariant
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import qualified Data.Yoko.TypeSums as TypeSums
--import Data.Yoko.Each



-- | @one@ extends a function that consumes a fields type to a function that
-- consumes a disbanded data type containing just that fields type.
one :: (dc -> a) -> N dc p1 p0 -> a
one = foldN0

infixl 6 |||
-- | Combines two functions that consume disbanded data types into a function
-- that consumes their union. All fields types must be from the same data type.
(|||) :: (Codomain0 sumL ~ Codomain0 sumR) => (sumL p1 p0 -> a) -> (sumR p1 p0 -> a) -> (sumL :+: sumR) p1 p0 -> a
(|||) = foldPlus

infixl 9 .|.
infixr 8 .||, ||.
-- | @f .|. g = one f '|||' one g@
f .|. g = one f ||| one g
-- | @f .|| g = one f '|||' g@
f .|| g = one f ||| g
-- | @f ||. g = f '|||' one g@
f ||. g = f ||| one g





-- | @disbanded@ injects a fields type into its disbanded range
disbanded :: Embed (N dc) (DCs (Codomain dc) ('KProxy :: KProxy k1 k0)) => dc -> DCs (Codomain dc) ('KProxy :: KProxy k1 k0) p1 p0
disbanded x = TypeSums.inject0 x

-- | @band@s a disbanded data type back into its normal data type.
--
-- Since 'DCs' is a type family, it's the range of @band@ that determines the
-- @t@ type variable.
class AreDCsOf (t :: k) (dcs :: k1 -> k0 -> *) where band_ :: W' t dcs p1 p0
instance (WN dc ('KProxy :: KProxy k1 k0),
          Codomain dc ~ t,
          DC dc ('KProxy :: KProxy k1 k0))
  => AreDCsOf (t :: k) (N (dc :: k) :: k1 -> k0 -> *) where
  band_ = composeSymW' p (rejoin p) (unN p) where
    p = Proxy :: Proxy ('KProxy :: KProxy k1 k0)
instance (FoldPlusW' t ('KProxy :: KProxy k1 k0), AreDCsOf t l, AreDCsOf t r) => AreDCsOf t ((l :+: r) :: k1 -> k0 -> *) where band_ = foldPlusW' (Proxy :: Proxy ('KProxy :: KProxy k1 k0)) band_ band_

band :: AreDCsOf t (DCs t any) => Proxy (any :: KProxy k1 k0) -> W' t (DCs t any) (p1 :: k1) (p0 :: k0)
band _ = band_

embed :: (Codomain0 sub ~ Codomain0 sup, Embed sub sup) => sub p1 p0 -> sup p1 p0
embed = TypeSums.embed


-- | @inject@s a fields type into a sum of fields types.
inject :: Embed (N dc) sum => dc -> sum p1 p0
inject = TypeSums.inject0

-- | @partition@s a sum of fields type into a specified sum of fields types and
-- the remaining sum.
partition :: (Codomain0 sum ~ Codomain0 sub, Partition sum sub (sum :-: sub)) =>
             sum p1 p0 -> Either (sub p1 p0) ((sum :-: sub) p1 p0)
partition = TypeSums.partition

-- | @project@s a single fields type out of a disbanded data type.
project :: (Codomain0 sum ~ Codomain dc, Partition sum (N dc) (sum :-: N dc)) =>
           sum p1 p0 -> Either dc ((sum :-: N dc) p1 p0)
project = TypeSums.project0



-- TODO need a MapSum just like MapRs, use a RPV for rep

-- | @reps@ maps a disbanded data type to its sum-of-products representation.
reps :: (EachGeneric sum, InvPrereq p1, InvPrereq p0) => sum p1 p0 -> EachRep sum p1 p0
reps = repEach

type family EachRep (sum :: k1 -> k0 -> *) :: k1 -> k0 -> *
type instance EachRep (N a :: k1 -> k0 -> *) = Rep a ('KProxy :: KProxy k1 k0)
type instance EachRep (a :+: b) = EachRep a :+: EachRep b
class EachGeneric sum where repEach :: (InvPrereq p1, InvPrereq p0) => sum p1 p0 -> EachRep sum p1 p0
instance (any ~ ('KProxy :: KProxy k1 k0), WN dc any, Generic dc any) => EachGeneric (N dc :: k1 -> k0 -> *) where
  repEach = unSym p (rep p) (unN p) where p = Proxy :: Proxy ('KProxy :: KProxy k1 k0)
instance (EachGeneric a, EachGeneric b) => EachGeneric (a :+: b) where repEach = mapPlus repEach repEach




-- | @precise_case@ is an exactly-typed case: the second argument is the
-- discriminant, the first argument is the default case, and the third argument
-- approximates a list of alternatives.
--
-- @
-- precise_case default x $
--   (\(C0_ ...) -> ...) '.||'
--   (\(C1_ ...) -> ...) '.|.'
--   (\(C2_ ...) -> ...)
-- @
--
-- In this example, @C0_@, @C1_@, and @C2_@ are fields types. The other fields
-- types for the same data type are handled with the @default@ function.
precise_case0 :: (Codomain0 dcs ~ t, Codomain0 (DCs t ('KProxy :: KProxy k1 k0)) ~ t, DT t ('KProxy :: KProxy k1 k0),
                 Partition (DCs t ('KProxy :: KProxy k1 k0)) dcs ((DCs t ('KProxy :: KProxy k1 k0)) :-: dcs)) =>
  (((DCs t ('KProxy :: KProxy k1 k0)) :-: dcs) p1 p0 -> a) -> t -> (dcs p1 p0 -> a) -> a
precise_case0 g x f = either f g $ partition $ unW0 (disband p) x
  where p = Proxy :: Proxy ('KProxy :: KProxy k1 k0)
-- | @ig_from x =@ 'reps $ disband' @x@ is a convenience. It approximates the
-- @instant-generics@ view, less the @CEq@ annotations.
ig_from :: (InvPrereq p1, InvPrereq p0,
            ComposeW t ('KProxy :: KProxy k1 k0),
            DT t ('KProxy :: KProxy k1 k0),
            EachGeneric (DCs t ('KProxy :: KProxy k1 k0))) => W t (EachRep (DCs t ('KProxy :: KProxy k1 k0))) p1 p0
ig_from = composeW (Proxy :: Proxy ('KProxy :: KProxy k1 k0)) reps (disband p)
  where p = Proxy :: Proxy ('KProxy :: KProxy k1 k0)
