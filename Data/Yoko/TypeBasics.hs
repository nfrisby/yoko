{-# LANGUAGE TypeFamilies, UndecidableInstances, DataKinds, PolyKinds #-}

{- |

Module      :  Data.Yoko.TypeBasics
Copyright   :  (c) The University of Kansas 2011
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Some type-level programming basics.

-}

module Data.Yoko.TypeBasics (
  Proxy(..), Equal, derive,
  -- ** Re-exports
  module Data.Yoko.MaybeKind, module Type.Booleans, encode
  ) where

import Type.Booleans
import Data.Yoko.MaybeKind

import Type.Spine
import Type.Ord (IsEQ)
import Type.Serialize
import Type.Ord.SpineSerialize (Compare)



-- | A polykinded proxy.
data Proxy a = Proxy



-- | Convenient synonym. @type Equal a b = 'IsEQ' ('Compare' a b)@
type Equal a b = IsEQ (Compare a b)



-- | Template Haskell derivation for the @type-spine@ and @type-cereal@
-- packages' 'Spine' and 'Serialize' type families, which support generic
-- instances of 'Compare'.
derive n = do
  d <- spineType n
  (d ++) `fmap` serializeTypeAsHash n
