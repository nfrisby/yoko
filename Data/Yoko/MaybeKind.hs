{-# LANGUAGE TypeFamilies, EmptyDataDecls #-}

module Data.Yoko.MaybeKind
  (-- ** Type-level @Maybe@
   Nothing, Just,
   IsJust, MaybePlus1, MaybeMap
   ) where

import Type.Booleans

data Nothing
data Just (x :: *)

-- | Returns a type-level boolean from @type-booleans@.
type family IsJust (x :: *) :: * -- returns Bool, ideally
type instance IsJust Nothing = False
type instance IsJust (Just x) = True

-- | Type-level @mplus@ for @Maybe@.
type family MaybePlus1 (x :: *) (y :: *) :: *
type instance MaybePlus1 Nothing y = y
type instance MaybePlus1 (Just x) Nothing = Just x

-- | Type-level @fmap@ for @Maybe@.
type family MaybeMap (f :: * -> *) (x :: *) :: *
type instance MaybeMap f (Just x) = Just (f x)
type instance MaybeMap f Nothing = Nothing
