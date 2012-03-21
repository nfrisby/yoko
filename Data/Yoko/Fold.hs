{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances #-}

module Fold where

import TypeBasics
import Representation



type family Fold s u sum

type instance Fold s u (N a) = Apply s a
type instance Fold s u (a :+ b) =
  Apply (Apply u (Fold s u a)) (Fold s u b)

type instance Fold s u (F a) = Apply s a
type instance Fold s u (a :* b) =
  Apply (Apply u (Fold s u a)) (Fold s u b)
