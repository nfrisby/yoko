{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators,
  UndecidableInstances, DataKinds, LambdaCase, FlexibleInstances,
  MultiParamTypeClasses, PolyKinds #-}

-- {-# OPTIONS_GHC -ddump-splices #-}

module Data.Yoko.Prelude where

import qualified GHC.Real

import Data.Yoko.TH
import Data.Yoko.W
import Data.YokoRaw

import Type.Spine (spineType_d)
import Type.Serialize (serializeTypeAsHash_data)


yokoTH ''Bool

yokoTH ''Proxy

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

type instance Rep (Nil_ a) any = C (Nil_ a) U -- Subst0 Nil_ a
instance Generic (Nil_ a) any where
  rep _ = W0  $ \_ -> C U
  obj _ = W'0 $ \_ -> Nil_

type instance Rep Nil_ (any :: KProxy k1 *) = C Nil_ U
instance Generic Nil_ (any :: KProxy k1 *) where
  rep _ = W1  $ \_ -> C U
  obj _ = W'1 $ \_ -> Nil_

type instance Rep (Cons_ a) any = C (Cons_ a) (T0 (Dep a) :*: T0 (Rec 'Z [a])) -- Subst0 Cons_ a
instance Generic (Cons_ a) any where
  rep _ = W0  $ \(Cons_ a as)         -> C (T0 a :*: T0 as)
  obj _ = W'0 $ \(C (T0 a :*: T0 as)) -> Cons_ a as

type instance Rep Cons_ (any :: KProxy k1 *) = C Cons_ (T0 Par0 :*: T1 (Rec 'Z []) (T0 Par0))
instance Generic Cons_ (any :: KProxy k1 *) where
  rep _ = W1  $ \(Cons_ a as)           -> C (T0 a :*: T1 (map T0 as))
  obj _ = W'1 $ \(C (T0 a :*: T1 as)) -> Cons_ a (map (\(T0 x) -> x) as)

type instance DTs []  = RecDT '[] '[]
type instance DCs [] (any :: KProxy k1 *) = N Nil_     :+: N Cons_
type instance DTs [a] = RecDT '[] '[]
type instance DCs [a] any = N (Nil_ a) :+: N (Cons_ a)

instance (EQ ~ SpineCompare a a) => DT [a] any where
  disband _ = W0 $ \case
    []     -> L $ N0 $ Nil_
    a : as -> R $ N0 $ Cons_ a as

instance DT [] (any :: KProxy k1 *) where
  disband _ = W1 $ \case
    []     -> L $ N1 $ Nil_
    a : as -> R $ N1 $ Cons_ a as
