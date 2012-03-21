{-# LANGUAGE TypeFamilies, EmptyDataDecls #-}

module Data.Yoko.MaybeKind where

import Type.Booleans

data Nothing
data Just (x :: *)

type family IsJust (x :: *) :: * -- returns Bool, ideally
type instance IsJust Nothing = False
type instance IsJust (Just x) = True

type family MaybePlus1 (x :: *) (y :: *) :: *
type instance MaybePlus1 Nothing y = y
type instance MaybePlus1 (Just x) Nothing = Just x

type family MaybeMap (f :: * -> *) (x :: *) :: *
type instance MaybeMap f (Just x) = Just (f x)
type instance MaybeMap f Nothing = Nothing
