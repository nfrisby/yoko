{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds #-}

{- |

Module      :  Data.Yoko.MaybeKind
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Some interface functions for type-level @Maybe@ (and @Bool@s). These functions
are probably ripe for the @promotion@ library of Eisenberg, Weirich, et alia?

-}

module Data.Yoko.MaybeKind
  (-- ** Type-level @Maybe@
   IsJust, MaybePlus1, MaybeMap, If
   ) where

type family If (c :: Bool) (a :: k) (b :: k) :: k
type instance If True  a b = a
type instance If False a b = b

-- | Returns a type-level boolean from @type-booleans@.
type family IsJust (x :: Maybe k) :: Bool
type instance IsJust Nothing = False
type instance IsJust (Just x) = True

-- | Type-level @mplus@ for @Maybe@.
type family MaybePlus1 (x :: Maybe k) (y :: Maybe k) :: Maybe k
type instance MaybePlus1 Nothing y = y
type instance MaybePlus1 (Just x) Nothing = Just x

-- | Type-level @fmap@ for @Maybe@.
type family MaybeMap (f :: k -> l) (x :: Maybe k) :: Maybe l
type instance MaybeMap f (Just x) = Just (f x)
type instance MaybeMap f Nothing = Nothing
