{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, DataKinds,
  PolyKinds, GADTs, LambdaCase #-}

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
type family Tag (dc :: k) :: Digit

-- | @Codomain@ is the data type that contains the constructor that the fields
-- type @dc@ represents.  It can also be applied to sums of fields types, in
-- which case it just uses the left-most.
type family Codomain (dc :: k) :: k

type family Codomain0 (dc :: k) :: *
type family Codomain1 (dc :: k) :: * -> *
type family Codomain2 (dc :: k) :: * -> * -> *
type instance Codomain0 (N0 dc   ) = Codomain dc
type instance Codomain1 (N1 dc   ) = Codomain dc
type instance Codomain2 (N2 dc   ) = Codomain dc
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
class (Generic0 dc, DT0 (Codomain dc)) => DC0 dc where rejoin0 :: dc       -> Codomain dc
class (Generic1 dc, DT1 (Codomain dc)) => DC1 dc where rejoin1 :: dc    p0 -> Codomain dc    p0
class (Generic2 dc, DT2 (Codomain dc)) => DC2 dc where rejoin2 :: dc p1 p0 -> Codomain dc p1 p0

-- | The @DCs@ of a data type is sum of all of its fields types.
type family DCs (t :: k) :: * -> * -> *
-- | @DT@ disbands a data type if all of its fields types have @DC@ instances.
class Reband0 t (DCs t) => DT0 t where disband0 :: t       -> DCs t p1 p0
class Reband1 t (DCs t) => DT1 t where disband1 :: t    p0 -> DCs t p1 p0
class Reband2 t (DCs t) => DT2 t where disband2 :: t p1 p0 -> DCs t p1 p0

--class (Partition (DCs (Codomain dc)) (N dc) (DCs (Codomain dc) :-: N dc),
--       Embed (N dc) (DCs (Codomain dc))) => IsDCOf dc
--instance (Partition (DCs (Codomain dc)) (N dc) (DCs (Codomain dc) :-: N dc),
--          Embed (N dc) (DCs (Codomain dc))) => IsDCOf dc





class Reband0 t r where reband0 :: r p1 p0 -> t
instance (DC0 dc, Codomain dc ~ t) => Reband0 t (N0 dc) where reband0 (N0 x) = rejoin0 x
instance (Reband0 t l, Reband0 t r) => Reband0 t (l :+: r) where
  reband0 = \case (L x) -> reband0 x; (R x) -> reband0 x

class Reband1 t r where reband1 :: r p1 p0 -> t p0
instance (DC1 dc, Codomain dc ~ t) => Reband1 t (N1 dc) where reband1 (N1 x) = rejoin1 x
instance (Reband1 t l, Reband1 t r) => Reband1 t (l :+: r) where
  reband1 = \case (L x) -> reband1 x; (R x) -> reband1 x

class Reband2 t r where reband2 :: r p1 p0 -> t p1 p0
instance (DC2 dc, Codomain dc ~ t) => Reband2 t (N2 dc) where reband2 (N2 x) = rejoin2 x
instance (Reband2 t l, Reband2 t r) => Reband2 t (l :+: r) where
  reband2 = \case (L x) -> reband2 x; (R x) -> reband2 x











-- take a representation, C or above and excluding Recs/Pars, to an actual *
-- type
type family Eval (r :: * -> * -> *) :: *
type instance Eval (Dep0 t)          = t
--type instance Eval Void           = ???
type instance Eval (l :+: r)        = Eval l -- equivalently, Eval r
type instance Eval (C  (dc :: *) r) = Codomain dc
type instance Eval (N0 dc)          = Codomain dc



data SubstSpec star = Sub0 star | Sub1 star | Sub10 star star



type family Subst (spec :: SubstSpec *) (r :: * -> * -> *) :: * -> * -> *
--type instance Subst spec Void  = ???
type instance Subst spec (N0 dc)   = N0 dc
type instance Subst spec (N1 dc)   = N1 dc
type instance Subst spec (N2 dc)   = N2 dc
type instance Subst spec (l :+: r) = Subst spec l :+: Subst spec r

type instance Subst spec (C dc r) = C dc (Subst spec r)
type instance Subst spec U         = U
type instance Subst spec (l :*: r) = Subst spec l :*: Subst spec r

type instance Subst (Sub0  par0     ) Par0 = Dep0 par0
type instance Subst (Sub1  par1     ) Par0 = Par0
type instance Subst (Sub10 par1 par0) Par0 = Dep0 par0
type instance Subst (Sub1  par1     ) Par1 = Dep0 par1
type instance Subst (Sub10 par1 par0) Par1 = Dep0 par1

type instance Subst (Sub0 par0) (Rec1 lbl t a) = Rec0 lbl (t (Eval (Subst (Sub0 par0) a)))
--type instance Subst (Sub1 par1) (Rec0 lbl t) = undefined
--type instance Subst (Sub10 par1 par0) (Rec1 lbl t a) = undefined

--type instance Subst (Sub0 par0 (Rec2 lbl t b a) = undefined
type instance Subst (Sub1 par1) (Rec2 lbl t b a) =
  Rec1 lbl    (t (Eval (Subst (Sub1 par1) b)))    (Subst (Sub1 par1) a)
type instance Subst (Sub10 par1 par0) (Rec2 lbl t b a) =
  Rec0 lbl    (t (Eval (Subst (Sub10 par1 par0) b))    (Eval (Subst (Sub10 par1 par0) a)))

type instance Subst spec (Dep0 t)  = Dep0 t

type instance Subst spec (Dep1 f x  ) = Dep1 f (Subst spec x)
type instance Subst spec (Dep2 f x y) = Dep2 f (Subst spec x) (Subst spec y)



type Subst0  t    p0 = Subst (Sub0 p0)     (Rep t)
type Subst1  t p1    = Subst (Sub1 p1)     (Rep t)
type Subst10 t p1 p0 = Subst (Sub10 p1 p0) (Rep t)
