{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, DataKinds,
  PolyKinds, GADTs, EmptyDataDecls #-}

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
{-  (-- * Reflection
   -- ** Fields types
   Tag, Codomain0, Codi, DC(..),
   -- ** Substitution
   Subst, Subst0, Subst1,
   -- ** Disbanded data types
   DCs, DT(..)
  ) -} where

import Data.Yoko.W
import Data.Yoko.TypeBasics
import Data.Yoko.Representation
--import Data.Yoko.TypeSums (Embed, Partition, (:-:))
--import Data.Yoko.Each

import Type.Digits (Digit)





-- | @Tag@ returns a simulated type-level string that is the name of the
-- constructor that the @dc@ fields type represents.
type family Tag (dc :: k) :: Digit

-- | @Codomain@ is the data type that contains the constructor that the fields
-- type @dc@ represents.  It can also be applied to sums of fields types, in
-- which case it just uses the left-most.
type family Codomain (dc :: k) :: k

type family Codomains (dcs :: * -> * -> *) :: k
type instance Codomains (N (dc :: *)          ) = Codomain dc
type instance Codomains (N (dc :: * -> *)     ) = Codomain dc
type instance Codomains (N (dc :: * -> * -> *)) = Codomain dc
type instance Codomains (l :+: r) = Codomains l



data DTPos k = NonRecDT | RecDT [k] [k]

-- | Maps a type to its mutually recursive siblings.
type family DTs (t :: k) :: DTPos k


type NumDTs t = NumDTs' (DTs t)
type family NumDTs' (t :: DTPos k) :: Nat
type instance NumDTs' NonRecDT    = Z
type instance NumDTs' (RecDT l r) = S (Length' (Length r) l)

type SiblingDTs t = SiblingDTs' t (DTs t)
type family SiblingDTs' (t :: k) (dpos :: DTPos k) :: [k]
type instance SiblingDTs' t NonRecDT    = '[]
type instance SiblingDTs' t (RecDT l r) = Append l (t ': r)



-- | Any fields type can be further represented as a product-of-fields and can
-- be injected back into the original data type.
class (Generic dc, DT (Codomain dc)) => DC dc where
  rejoin :: W dc p1 p0 -> W (Codomain dc) p1 p0

-- | The @DCs@ of a data type is sum of all of its fields types.
type family DCs (t :: k) :: * -> * -> *
-- | @DT@ disbands a data type.@
class DT t where disband :: W t p1 p0 -> DCs t p1 p0





-- | Maps a field representation to the represented type.
type family EvalT (r :: * -> * -> *) (p1 :: *) (p0 :: *) :: *
type instance EvalT (T0 v t)     p1 p0 = t
type instance EvalT (T1 v t a)   p1 p0 = t (EvalT a p1 p0)
type instance EvalT (T2 v t b a) p1 p0 = t (EvalT b p1 p0) (EvalT a p1 p0)
