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

import Data.Yoko.TypeBasics
import Data.Yoko.Representation
--import Data.Yoko.TypeSums (Embed, Partition, (:-:))
--import Data.Yoko.Each

import Type.Digits (Digit)





-- | @Tag@ returns a simulated type-level string that is the name of the
-- constructor that the @dc@ fields type represents.
type family Tag dc :: Digit

-- | @Codomain@ is the data type that contains the constructor that the fields
-- type @dc@ represents.  It can also be applied to sums of fields types, in
-- which case it just uses the left-most.
type family Codomain0 (dc :: k) :: *
type family Codomain1 (dc :: k) :: * -> *
type family Codomain2 (dc :: k) :: * -> * -> *
type instance Codomain0 (N dc   ) = Codomain0 dc
type instance Codomain0 (l :+: r) = Codomain0 l
type instance Codomain1 (N dc   ) = Codomain1 dc
type instance Codomain1 (l :+: r) = Codomain1 l
type instance Codomain2 (N dc   ) = Codomain2 dc
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
class (Generic0 dc, DT0 (Codomain0 dc)) => DC0 dc where rejoin0 :: dc       -> Codomain0 dc
class (Generic1 dc, DT1 (Codomain1 dc)) => DC1 dc where rejoin1 :: dc    p0 -> Codomain1 dc    p0
class (Generic2 dc, DT2 (Codomain2 dc)) => DC2 dc where rejoin2 :: dc p1 p0 -> Codomain2 dc p1 p0

-- | The @DCs@ of a data type is sum of all of its fields types.
type family DCs (t :: k) :: * -> * -> *
-- | @DT@ disbands a data type if all of its fields types have @DC@ instances.
class {- Each IsDCOf (DCs t) => -} DT0 t where disband0 :: t       -> DCs t p1 p0
class {- Each IsDCOf (DCs t) => -} DT1 t where disband1 :: t    p0 -> DCs t p1 p0
class {- Each IsDCOf (DCs t) => -} DT2 t where disband2 :: t p1 p0 -> DCs t p1 p0

--class (Partition (DCs (Codomain dc)) (N dc) (DCs (Codomain dc) :-: N dc),
--       Embed (N dc) (DCs (Codomain dc))) => IsDCOf dc
--instance (Partition (DCs (Codomain dc)) (N dc) (DCs (Codomain dc) :-: N dc),
--          Embed (N dc) (DCs (Codomain dc))) => IsDCOf dc





-- take a representation, C or above and excluding Recs/Pars, to an actual *
-- type
type family Eval (r :: * -> * -> *) :: *
type instance Eval (Dep t)   = t
type instance Eval (Void t)  = t
type instance Eval (l :+: r) = Eval l -- equivalently, Eval r
type instance Eval (C dc r)  = Codomain0 dc
type instance Eval (N dc)    = Codomain0 dc



data SubstSpec star = Sub0 star | Sub1 star | Sub10 star star



type family Subst (spec :: SubstSpec *) (r :: * -> * -> *) :: * -> * -> *
type instance Subst spec (Void t)  = Void t
type instance Subst spec (N dc)    = N dc
type instance Subst spec (l :+: r) = Subst spec l :+: Subst spec r

type instance Subst spec (C dc r)  = C dc (Subst spec r)
type instance Subst spec U         = U
type instance Subst spec (l :*: r) = Subst spec l :*: Subst spec r

type instance Subst (Sub0  par0     ) Par0 = Dep par0
type instance Subst (Sub1  par1     ) Par0 = Par0
type instance Subst (Sub10 par1 par0) Par0 = Dep par0
type instance Subst (Sub1  par1     ) Par1 = Dep par1
type instance Subst (Sub10 par1 par0) Par1 = Dep par1

type instance Subst (Sub0 par0) (Rec1 lbl t a) = Rec0 lbl (t (Eval (Subst (Sub0 par0) a)))
--type instance Subst (Sub1 par1) (Rec0 lbl t) = undefined
--type instance Subst (Sub10 par1 par0) (Rec1 lbl t a) = undefined

--type instance Subst (Sub0 par0 (Rec2 lbl t b a) = undefined
type instance Subst (Sub1 par1) (Rec2 lbl t b a) =
  Rec1 lbl    (t (Eval (Subst (Sub1 par1) b)))    (Subst (Sub1 par1) a)
type instance Subst (Sub10 par1 par0) (Rec2 lbl t b a) =
  Rec0 lbl    (t (Eval (Subst (Sub10 par1 par0) b))    (Eval (Subst (Sub10 par1 par0) a)))

type instance Subst spec (Dep t)  = Dep t

type instance Subst spec ( f :@:  x   ) =  f :@:  Subst spec x
type instance Subst spec ((f :@@: x) y) = (f :@@: Subst spec x) (Subst spec y)



type Subst0  t    p0 = Subst (Sub0 p0)     (Rep t)
type Subst1  t p1    = Subst (Sub1 p1)     (Rep t)
type Subst10 t p1 p0 = Subst (Sub10 p1 p0) (Rep t)
