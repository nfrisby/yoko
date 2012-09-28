{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators,
  UndecidableInstances, DataKinds, LambdaCase #-}

module Data.Yoko.Prelude where

import qualified GHC.Real

import Data.Yoko.TH
import Data.Yoko.W
import Data.YokoRaw

import Type.Spine (spineType_d)
import Type.Serialize (serializeTypeAsHash_data)


yokoTH ''Bool


yokoTH ''()

type instance DTs (,,) = NonRecDT

yokoTH_with (yokoDefaults {invInsts = \_ -> False}) ''GHC.Real.Ratio
yokoTH_with (yokoDefaults {invInsts = \_ -> False}) ''(,)
yokoTH_with (yokoDefaults {invInsts = \_ -> False}) ''(,,)
yokoTH_with (yokoDefaults {invInsts = \_ -> False}) ''Maybe
yokoTH_with (yokoDefaults {invInsts = \_ -> False}) ''Either

data Nil_  (p0 :: *) = Nil_
data Cons_ (p0 :: *) = Cons_ p0 [p0]

spineType_d ''Nil_
spineType_d ''Cons_

serializeTypeAsHash_data ''Nil_
serializeTypeAsHash_data ''Cons_

type instance Codomain Nil_  = []
type instance Codomain Cons_ = []

type instance Codomain (Nil_ a)  = [a]
type instance Codomain (Cons_ a) = [a]

type instance Rep (Nil_ a)  = Subst0 Nil_ a
instance Generic (Nil_ a) where
  rep = foldW0   $ \_ -> C U
  obj = unfoldW0 $ \_ -> Nil_

instance (EQ ~ SpineCompare a a) => DC (Nil_ a) where
  rejoin = mapW0 $ \_ -> []

type instance Rep Nil_  = C Nil_ U
instance Generic Nil_ where
  rep = foldW1   $ \_ -> C U
  obj = unfoldW1 $ \_ -> Nil_

instance DC Nil_ where rejoin = mapW1 $ \_ -> []

type instance Rep (Cons_ a) = Subst0 Cons_ a
instance Generic (Cons_ a) where
  rep = foldW0   $ \(Cons_ a as)         -> C (T0 a :*: T0 as)
  obj = unfoldW0 $ \(C (T0 a :*: T0 as)) -> Cons_ a as

instance (EQ ~ SpineCompare a a) => DC (Cons_ a) where
  rejoin = mapW0 $ \(Cons_ a as) -> a : as

type instance Rep Cons_ = C Cons_ (Par0 :*: T1 (Rec 'Z) [] Par0)
instance Generic Cons_ where
  rep = foldW1   $ \(Cons_ a as)           -> C (Par0 a :*: T1 (map Par0 as))
  obj = unfoldW1 $ \(C (Par0 a :*: T1 as)) -> Cons_ a (map unPar0 as)

instance DC Cons_ where rejoin = mapW1 $ \(Cons_ a as) -> a : as

type instance DTs []  = RecDT '[] '[]
type instance DCs []  = N Nil_     :+: N Cons_
type instance DTs [a] = RecDT '[] '[]
type instance DCs [a] = N (Nil_ a) :+: N (Cons_ a)

instance (EQ ~ SpineCompare a a) => DT [a] where
  disband = foldW0 $ \case
    []     -> L $ N $ W0 $ Nil_
    a : as -> R $ N $ W0 $ Cons_ a as

instance DT [] where
  disband = foldW1 $ \case
    []     -> L $ N $ W1 $ Nil_
    a : as -> R $ N $ W1 $ Cons_ a as
