{-# LANGUAGE TypeFamilies, UndecidableInstances, DataKinds, PolyKinds #-}

{- |

Module      :  Data.Yoko.TypeBasics
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Some type-level programming basics.

-}

module Data.Yoko.TypeBasics (
  Proxy(..), Equal, derive_data, derive_pro,
  -- ** Re-exports
  module Data.Yoko.MaybeKind, encode
  ) where

import Data.Yoko.MaybeKind

import Type.Spine
import Type.Ord (IsEQ)
import Type.Serialize
import Type.Ord.SpineSerialize (SpineCompare)



-- | A polykinded proxy.
data Proxy a = Proxy



-- | Convenient synonym. @type Equal a b = 'IsEQ' ('SpineCompare' a b)@
type Equal a b = IsEQ (SpineCompare a b)



-- | Template Haskell derivation for the @type-spine@ and @type-cereal@
-- packages' 'Spine' and 'Serialize' type families, which support generic
-- instances of 'Compare'.
derive_data n = do
  d <- spineType_d n
  (d ++) `fmap` serializeTypeAsHash_data n

derive_pro n = do
  d <- spineType_pro n
  (d ++) `fmap` serializeTypeAsHash_pro n
