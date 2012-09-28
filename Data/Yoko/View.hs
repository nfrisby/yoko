{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, DataKinds,
  PolyKinds, GADTs #-}

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

type family Codomain0 (dcs :: * -> * -> *) :: *
type family Codomain1 (dcs :: * -> * -> *) :: * -> *
type family Codomain2 (dcs :: * -> * -> *) :: * -> * -> *
type instance Codomain0 (N dc)    = Codomain dc
type instance Codomain1 (N dc)    = Codomain dc
type instance Codomain2 (N dc)    = Codomain dc
type instance Codomain0 (l :+: r) = Codomain0 l
type instance Codomain1 (l :+: r) = Codomain1 l
type instance Codomain2 (l :+: r) = Codomain2 l



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



-- take a representation, C or above and excluding Recs/Pars, to an actual *
-- type
type family Eval (r :: * -> * -> *) :: *
type instance Eval (T0 Dep t)       = t
--type instance Eval Void           = ???
type instance Eval (l :+: r)        = Eval l -- equivalently, Eval r
type instance Eval (C  (dc :: *) r) = Codomain dc
type instance Eval (N dc)           = Codomain dc



data SubstSpec star = Sub0 star | Sub1 star | Sub10 star star



type family Subst (spec :: SubstSpec *) (r :: * -> * -> *) :: * -> * -> *
--type instance Subst spec Void  = ???
type instance Subst spec (N dc)   = N dc
type instance Subst spec (l :+: r) = Subst spec l :+: Subst spec r

type instance Subst spec (C dc r) = C dc (Subst spec r)
type instance Subst spec U         = U
type instance Subst spec (l :*: r) = Subst spec l :*: Subst spec r

type instance Subst (Sub0  par0     ) Par0 = T0 Dep par0
type instance Subst (Sub1  par1     ) Par0 = Par0
type instance Subst (Sub10 par1 par0) Par0 = T0 Dep par0
type instance Subst (Sub1  par1     ) Par1 = T0 Dep par1
type instance Subst (Sub10 par1 par0) Par1 = T0 Dep par1

type instance Subst (Sub0 par0) (T1 (Rec lbl) t a) = T0 (Rec lbl) (t (Eval (Subst (Sub0 par0) a)))
--type instance Subst (Sub1 par1) (Rec0 lbl t) = undefined
--type instance Subst (Sub10 par1 par0) (Rec1 lbl t a) = undefined

--type instance Subst (Sub0 par0 (Rec2 lbl t b a) = undefined
type instance Subst (Sub1 par1) (T2 (Rec lbl) t b a) =
  T1 (Rec lbl)    (t (Eval (Subst (Sub1 par1) b)))    (Subst (Sub1 par1) a)
type instance Subst (Sub10 par1 par0) (T2 (Rec lbl) t b a) =
  T0 (Rec lbl)    (t (Eval (Subst (Sub10 par1 par0) b))    (Eval (Subst (Sub10 par1 par0) a)))

type instance Subst spec (T0 Dep t)  = T0 Dep t

type instance Subst spec (T1 Dep f x  ) = T1 Dep f (Subst spec x)
type instance Subst spec (T2 Dep f x y) = T2 Dep f (Subst spec x) (Subst spec y)



type Subst0  t    p0 = Subst (Sub0 p0)     (Rep t)
type Subst1  t p1    = Subst (Sub1 p1)     (Rep t)
type Subst10 t p1 p0 = Subst (Sub10 p1 p0) (Rep t)
