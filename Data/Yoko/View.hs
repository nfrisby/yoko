{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, ConstraintKinds,
  UndecidableInstances #-}

{- |

Module      :  Data.Yoko.View
Copyright   :  (c) The University of Kansas 2011
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

The @yoko@ generic view.

-}

module Data.Yoko.View
  (-- * Reflection
   -- ** Fields types
   Tag, Range, DC(..),
   -- ** Disbanded data types
   DCs, Disbanded, DT(..)
  ) where

import Data.Yoko.Representation
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import Data.Yoko.Each




-- | @Tag@ returns a simulated type-level string that is the name of the
-- constructor that the @dc@ fields type represents.
type family Tag dc

-- | @Range@ is the data type that contains the constructor that the fields
-- type @dc@ represents.
type family Range dc

-- | Any fields type can be further represented as a product-of-fields and can
-- be injected back into the original data type.
class (Generic dc, DT (Range dc)) => DC dc where rejoin :: dc -> Range dc

-- | The @DCs@ of a data type is sum of all of its fields types.
type family DCs t
-- | A disbanded data type is the data type's @DCs@ annotated with it.
type Disbanded t = DCsOf t (DCs t)
-- | @DT@ disbands a data type if all of its fields types have @DC@ instances.
class Each IsDCOf (DCs t) => DT t where disband :: t -> Disbanded t

class (Partition (DCs (Range dc)) (N dc) (DCs (Range dc) :-: N dc),
       Embed (N dc) (DCs (Range dc))) => IsDCOf dc
instance (Partition (DCs (Range dc)) (N dc) (DCs (Range dc) :-: N dc),
          Embed (N dc) (DCs (Range dc))) => IsDCOf dc
