{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators, UndecidableInstances, DataKinds #-}

module Data.Yoko.Prelude where

import qualified GHC.Real

import Data.Yoko.TH
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
instance Generic0 (Nil_ a) where
  rep0 _ = C U; obj0 _ = Nil_

type instance Rep Nil_  = C Nil_ U
instance Generic1 Nil_ where
  rep1 _ = C U; obj1 _ = Nil_

type instance Rep (Cons_ a) = Subst0 Cons_ a
instance Generic0 (Cons_ a) where
  rep0 (Cons_ a as)         = C (Dep0 a :*: Rec0 as)
  obj0 (C (Dep0 a :*: Rec0 as)) = Cons_ a as

type instance Rep Cons_ = C Cons_ (Par0 :*: Rec1 'Z [] Par0)
instance Generic1 Cons_ where
  rep1 (Cons_ a as)             = C (Par0 a :*: Rec1 (map Par0 as))
  obj1 (C (Par0 a :*: Rec1 as)) = Cons_ a (map unPar0 as)

type instance DTs []  = RecDT '[] '[]
type instance DCs []  = N1 Nil_     :+: N1 Cons_
type instance DTs [a] = RecDT '[] '[]
type instance DCs [a] = N0 (Nil_ a) :+: N0 (Cons_ a)

instance (EQ ~ SpineCompare a a) => DT0 [a] where
  disband0 []       = L $ N0 $ Nil_
  disband0 (a : as) = R $ N0 $ Cons_ a as

instance DT1 [] where
  disband1 []       = L $ N1 $ Nil_
  disband1 (a : as) = R $ N1 $ Cons_ a as
