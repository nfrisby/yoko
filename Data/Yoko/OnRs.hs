{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, Rank2Types, TypeOperators,
  FlexibleInstances, UndecidableInstances, ScopedTypeVariables #-}

module OnRs (onRsRPV, OnRsRPV(..), OnRs, OnRs_Con(..)) where

import TypeBasics
import Representation
import RPV



data OnRsRPV (rpv :: * -> *) a = OnRsRPV (forall a. rpv a)
type instance Con (OnRsRPV rpv) a = OnRs_Con rpv a
type instance Inst (OnRsRPV rpv) a = a -> OnRs rpv a
instance RPV rpv => RPV (OnRsRPV rpv) where
  instantiate (OnRsRPV rpv) = onRs_method rpv
onRsRPV :: (forall a. rpv a) -> OnRsRPV rpv a
onRsRPV = OnRsRPV


type OnRs rpv field = OnRs_ rpv field



type family OnRs_ (rpv :: * -> *) field

class OnRs_Con rpv field where
  onRs_method :: RPV rpv => (forall a. rpv a) -> field -> OnRs rpv field



type instance OnRs_ rpv (R a) = R (Codomain (Inst rpv a))
instance (Con rpv a, Inst rpv a ~ (a -> ex)) => OnRs_Con rpv (R a)
  where onRs_method rpv (R x) = R (instantiate (rpv :: rpv a) x)

type instance OnRs_  rpv (D a) = D a
instance      OnRs_Con rpv (D a) where onRs_method _ = id
