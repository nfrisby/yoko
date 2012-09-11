{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables,
  UndecidableInstances #-}

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
   -- * Building fields type consumers
   one, (|||), (||.), (.||), (.|.),
   -- * Operations on disbanded data types
   disbanded, band, ConDCOf, precise_case,
   -- * Operations on sums of fields types
   (:-:), Embed, Partition,
   embed, inject, partition, project,
   -- * Forgetting @yoko@'s extra structure
   reps, EachGeneric, EachRep, ig_from,
   Equal,
   -- * Bundled Template Haskell
   module Data.Yoko.TH) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation
import Data.Yoko.View
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import qualified Data.Yoko.TypeSums as TypeSums
import Data.Yoko.Each

import Data.Yoko.TH



-- | @one@ extends a function that consumes a fields type to a function that
-- consumes a disbanded data type containing just that fields type.
one :: (dc -> a) -> N dc -> a
one = foldN

infixl 6 |||
-- | Combines two functions that consume disbanded data types into a function
-- that consumes their union. All fields types must be from the same data type.
(|||) :: (Codomain sumL ~ Codomain sumR) => (sumL -> a) -> (sumR -> a) -> sumL :+: sumR -> a
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
disbanded :: Embed (N dc) (DCs (Codomain dc)) => dc -> DCs (Codomain dc)
disbanded = TypeSums.inject

-- | @band@s a disbanded data type back into its normal data type.
--
-- Since 'Disbanded' is a type family, the range of @band@ determines the @t@
-- type variable.
band :: forall t. Each (ConDCOf t) (DCs t) => DCs t -> t
band = each (Proxy :: Proxy (ConDCOf t)) rejoin

class (Codomain dc ~ t, DC dc) => ConDCOf t dc
instance (Codomain dc ~ t, DC dc) => ConDCOf t dc

embed :: (Codomain sub ~ Codomain sup, Embed sub sup) => sub -> sup
embed = TypeSums.embed


-- | @inject@s a fields type into a sum of fields types.
inject :: Embed (N dc) sum => dc -> sum
inject = TypeSums.inject

-- | @partition@s a sum of fields type into a specified sum of fields types and
-- the remaining sum.
partition :: (Codomain sum ~ Codomain sub, Partition sum sub (sum :-: sub)) =>
             sum -> Either sub (sum :-: sub)
partition = TypeSums.partition

-- | @project@s a single fields type out of a disbanded data type.
project :: (Codomain sum ~ Codomain dc, Partition sum (N dc) (sum :-: N dc)) =>
           sum -> Either dc (sum :-: N dc)
project = TypeSums.project



-- TODO need a MapSum just like MapRs, use a RPV for rep

-- | @reps@ maps a disbanded data type to its sum-of-products representation.
reps :: EachGeneric sum => sum -> EachRep sum
reps = repEach

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
precise_case :: (Codomain dcs ~ t, Codomain (DCs t) ~ t, DT t,
               Partition (DCs t) dcs (DCs t :-: dcs)) =>
  (DCs t :-: dcs -> a) -> t -> (dcs -> a) -> a
precise_case g x f = either f g $ partition $ disband x

-- | @ig_from x =@ 'reps $ disband' @x@ is a convenience. It approximates the
-- @instant-generics@ view, less the @CEq@ annotations.
ig_from :: (DT t, EachGeneric (DCs t)) => t -> EachRep (DCs t)
ig_from x = reps $ disband x
