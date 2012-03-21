{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, Rank2Types, TypeOperators,
  FlexibleInstances, ConstraintKinds, UndecidableInstances,
  ScopedTypeVariables #-}

module Map (Mapped, Map, mapRPV) where

import TypeBasics
import Representation
import RPV





type Mapped rpv prod = Mapped_ rpv prod
type Map = Map_
mapRPV ::
  (Map rpv prod, RPV rpv) => (forall a. rpv a) -> prod -> Mapped rpv prod
mapRPV = mapRPV_



type family Mapped_ (rpv :: * -> *) prod

class RPV rpv => Map_ rpv prod where
  mapRPV_ :: (forall a. rpv a) -> prod -> Mapped rpv prod

-- map over products
type instance Mapped_ rpv (F a) = F (Codomain (Inst rpv a))
instance (RPV rpv, Con rpv a, Inst rpv a ~ (a -> ex)) => Map_ rpv (F a)
  where mapRPV_ rpv (F x) = F (instantiate (rpv :: rpv a) x)

type instance Mapped_ rpv U = U
instance RPV rpv => Map_ rpv U where mapRPV_ _ = id

type instance Mapped_ rpv (a :*: b) = Mapped rpv a :*: Mapped rpv b
instance (Map rpv a, Map rpv b) => Map_ rpv (a :*: b) where
  mapRPV_ rpv = mapTimes (mapRPV rpv) (mapRPV rpv)

-- map over sums
type instance Mapped_  rpv (N a) = N (Codomain (Inst rpv a))
instance Map_ rpv (F a) => Map_ rpv (N a) where
  mapRPV_ rpv (N a) = let (F b) = mapRPV_ rpv (F a) in N b

type instance Mapped_ rpv (a :+ b) = Mapped rpv a :+ Mapped rpv b
instance (Map rpv a, Map rpv b) => Map_ rpv (a :+ b) where
  mapRPV_ rpv = mapPlus (mapRPV rpv) (mapRPV rpv)
