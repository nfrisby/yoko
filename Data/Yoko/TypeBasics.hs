{-# LANGUAGE TypeFamilies, UndecidableInstances, DataKinds, PolyKinds #-}

module Data.Yoko.TypeBasics (
  module Data.Yoko.MaybeKind,
  module Type.Booleans,
  Proxy(..),
  Equal,
  IsPrefixOf,
  derive, encode
  ) where

import Type.Booleans
import Data.Yoko.MaybeKind

--import Data.Proxy.TH (Proxy(..))
import Type.Spine
import Type.Ord (IsEQ)
import Type.Serialize
import Type.Ord.SpineSerialize (Compare)



data Proxy a = Proxy



type Equal a b = IsEQ (Compare a b)



type family IsPrefixOf (pre :: *) (s :: *) :: * -- emulated primitive



derive n = do
  d <- spineType n
  (d ++) `fmap` serializeTypeAsHash n
