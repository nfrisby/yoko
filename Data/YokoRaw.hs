{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables,
  UndecidableInstances, PolyKinds #-}

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
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import qualified Data.Yoko.TypeSums as TypeSums
--import Data.Yoko.Each



-- | @one@ extends a function that consumes a fields type to a function that
-- consumes a disbanded data type containing just that fields type.
one :: (dc -> a) -> N0 dc p1 p0 -> a
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
disbanded :: Embed (N0 dc) (DCs (Codomain dc)) => dc -> DCs (Codomain dc) p1 p0
disbanded = TypeSums.inject0

-- | @band@s a disbanded data type back into its normal data type.
--
-- Since 'DCs' is a type family, it's the range of @band@ that determines the
-- @t@ type variable.
class AreDCsOf (t :: k) (dcs :: * -> * -> *) where band_ :: W' t dcs p1 p0
instance (Codomain dc ~ t, DC dc) => AreDCsOf t (N0 dc) where
  band_ = W'0 $ (\(Sym0 f) -> f) rejoin . unN0
instance (Codomain dc ~ t, DC dc) => AreDCsOf t (N1 dc) where
  band_ = W'1 $ (\(Sym1 f) -> f) rejoin . unN1
instance (Codomain dc ~ t, DC dc) => AreDCsOf t (N2 dc) where
  band_ = W'2 $ (\(Sym2 f) -> f) rejoin . unN2
instance (FoldPlusW' t, AreDCsOf t l, AreDCsOf t r) => AreDCsOf t (l :+: r) where band_ = foldPlusW' band_ band_

band :: (AreDCsOf (t :: k) (DCs t)) => W' t (DCs t) p1 p0
band = band_

embed :: (Codomain0 sub ~ Codomain0 sup, Embed sub sup) => sub p1 p0 -> sup p1 p0
embed = TypeSums.embed


-- | @inject@s a fields type into a sum of fields types.
inject :: Embed (N0 dc) sum => dc -> sum p1 p0
inject = TypeSums.inject0

-- | @partition@s a sum of fields type into a specified sum of fields types and
-- the remaining sum.
partition :: (Codomain0 sum ~ Codomain0 sub, Partition sum sub (sum :-: sub)) =>
             sum p1 p0 -> Either (sub p1 p0) ((sum :-: sub) p1 p0)
partition = TypeSums.partition

-- | @project@s a single fields type out of a disbanded data type.
project :: (Codomain0 sum ~ Codomain dc, Partition sum (N0 dc) (sum :-: N0 dc)) =>
           sum p1 p0 -> Either dc ((sum :-: N0 dc) p1 p0)
project = TypeSums.project0



-- TODO need a MapSum just like MapRs, use a RPV for rep

-- | @reps@ maps a disbanded data type to its sum-of-products representation.
reps :: EachGeneric sum => sum p1 p0 -> EachRep sum p1 p0
reps = repEach

type family EachRep (sum :: * -> * -> *) :: * -> * -> *
type instance EachRep (N0 a) = Rep a
type instance EachRep (N1 a) = Rep a
type instance EachRep (N2 a) = Rep a
type instance EachRep (a :+: b) = EachRep a :+: EachRep b
class EachGeneric sum where
  repEach :: sum p1 p0 -> EachRep sum p1 p0
instance Generic a => EachGeneric (N0 a) where
  repEach = (\(W0 x) -> x) rep . unN0
instance Generic a => EachGeneric (N1 a) where
  repEach = (\(W1 x) -> x) rep . unN1
instance Generic a => EachGeneric (N2 a) where
  repEach = (\(W2 x) -> x) rep . unN2
instance (EachGeneric a, EachGeneric b) => EachGeneric (a :+: b) where
  repEach = mapPlus repEach repEach




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
precise_case0 :: (Codomain0 dcs ~ t, Codomain0 (DCs t) ~ t, DT t,
                 Partition (DCs t) dcs (DCs t :-: dcs)) =>
  ((DCs t :-: dcs) p1 p0 -> a) -> t -> (dcs p1 p0 -> a) -> a
precise_case0 g x f = either f g $ partition $ unW0 disband x

-- | @ig_from x =@ 'reps $ disband' @x@ is a convenience. It approximates the
-- @instant-generics@ view, less the @CEq@ annotations.
ig_from :: (ComposeW t, DT t, EachGeneric (DCs t)) => W t (EachRep (DCs t)) p1 p0
ig_from = reps `composeW` disband
