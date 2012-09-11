{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}

{- |

Module      :  Data.Yoko.View
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

The @yoko@ generic view.

-}

module Data.Yoko.View
  (-- * Reflection
   -- ** Fields types
   Tag, Codomain, DC(..),
   -- ** Disbanded data types
   DCs, DT(..)
  ) where

import Data.Yoko.Representation
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import Data.Yoko.Each




-- | @Tag@ returns a simulated type-level string that is the name of the
-- constructor that the @dc@ fields type represents.
type family Tag dc

-- | @Codomain@ is the data type that contains the constructor that the fields
-- type @dc@ represents.  It can also be applied to sums of fields types, in
-- which case it just uses the left-most.
type family Codomain dc
type instance Codomain (N dc) = Codomain dc
type instance Codomain (l :+: r) = Codomain l

-- | Any fields type can be further represented as a product-of-fields and can
-- be injected back into the original data type.
class (Generic dc, DT (Codomain dc)) => DC dc where rejoin :: dc -> Codomain dc

-- | The @DCs@ of a data type is sum of all of its fields types.
type family DCs t
-- | @DT@ disbands a data type if all of its fields types have @DC@ instances.
class Each IsDCOf (DCs t) => DT t where disband :: t -> DCs t

class (Partition (DCs (Codomain dc)) (N dc) (DCs (Codomain dc) :-: N dc),
       Embed (N dc) (DCs (Codomain dc))) => IsDCOf dc
instance (Partition (DCs (Codomain dc)) (N dc) (DCs (Codomain dc) :-: N dc),
          Embed (N dc) (DCs (Codomain dc))) => IsDCOf dc
