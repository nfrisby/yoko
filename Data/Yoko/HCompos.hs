{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses,
  FlexibleContexts, FlexibleInstances, UndecidableInstances,
  ScopedTypeVariables, DataKinds  #-}

{-# OPTIONS_GHC -fcontext-stack=250 #-}

{- |

Module      :  Data.Yoko.HCompos
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

The generic homomorphism or \"heterogenous compos\".

See the paper \"A Pattern for Almost Homomorphic Functions\" at <http://www.ittc.ku.edu/~nfrisby/papers/yoko.pdf>, submitted to ICFP 2012.

-}

module Data.Yoko.HCompos where

import Data.Yoko.TypeBasics
import Data.Yoko

import Control.Applicative
import Data.Traversable (Traversable, traverse)
import Data.Bitraversable (Bitraversable, bitraverse)

import Type.Digits (Digit)





-- | The applicative functor required by the conversion.
type family Idiom cnv :: * -> *

-- | Use the conversion @cnv@ to convert from @a@ to @b@.
class Applicative (Idiom cnv) => Convert cnv a b where
  convert :: cnv -> a -> Idiom cnv b

-- | The generic version of @convert@; operates on /disbanded data types/.
class Applicative (Idiom cnv) => HCompos cnv a t where
  hcompos :: cnv -> a -> Idiom cnv t




-- these two instances make functions work directly for singly-recursive data
-- types
type instance Idiom (a -> i b) = i
instance (Applicative i, a ~ x, b ~ y) => Convert (a -> i b) x y where convert = ($)





-- | @FindDCs dcA dcBs@ returns a type-level @Maybe@. @Just dcB@ is a fields
-- type @dcB@ where @'Tag' dcA ~ dcB@.
type family FindDCs (s :: Digit) sum :: Maybe *
type instance FindDCs s (N dc) =
  If   (Equal s (Tag dc))   (Just dc)   Nothing
type instance FindDCs s (a :+: b) = DistMaybePlus (FindDCs s a) (FindDCs s b)





instance (HCompos cnv a t, HCompos cnv b t
         ) => HCompos cnv (a :+: b) t where
  hcompos cnv = foldPlus (hcompos cnv) (hcompos cnv)

-- NB only works if there's exactly one matching constructor
instance (Generic dc, Just dc' ~ FindDCs (Tag dc) (DCs t),
          MapRs cnv dc dc' (Rep dc) (Rep dc'),
          DC dc', Codomain dc' ~ t, DT t
         ) => HCompos cnv (N dc) t where
  hcompos cnv =
    foldN $ liftA (rejoin . (id :: dc' -> dc') . obj) . mapRs cnv p1 p2 . rep
    where p1 :: Proxy dc; p1 = Proxy; p2 :: Proxy dc'; p2 = Proxy




-- applies cnv to every Rec in a product; identity on other factors; the dc and
-- dc' parameters are just for error messages: all instances treat them
-- parametrically

-- | Same as @compos@ semantics, but with a generalized type and just for
-- converting between product representations.
class Applicative (Idiom cnv) => MapRs cnv dc dc' prod prod' where
  mapRs :: cnv -> Proxy dc -> Proxy dc' -> prod -> Idiom cnv prod'

instance Convert cnv a b => MapRs cnv dc dc' (Rec a) (Rec b) where
  mapRs cnv _ _ (Rec x) = Rec <$> convert cnv x

instance Applicative (Idiom cnv) => MapRs cnv dc dc' (Dep a) (Dep a) where
  mapRs _ _ _ = pure
instance Applicative (Idiom cnv) => MapRs cnv dc dc' U       U       where
  mapRs _ _ _ = pure

instance (MapRs cnv dc dc' a a', MapRs cnv dc dc' b b'
         ) => MapRs cnv dc dc' (a :*: b) (a' :*: b') where
  mapRs cnv p1 p2 (a :*: b) = (:*:) <$> mapRs cnv p1 p2 a <*> mapRs cnv p1 p2 b

instance (Traversable f, MapRs cnv dc dc' a a'
         ) => MapRs cnv dc dc' (Par1 f a) (Par1 f a') where
  mapRs cnv p1 p2 (Par1 x) = Par1 <$> traverse (mapRs cnv p1 p2) x

instance (Bitraversable f, MapRs cnv dc dc' a a', MapRs cnv dc dc' b b'
         ) => MapRs cnv dc dc' (Par2 f a b) (Par2 f a' b') where
  mapRs cnv p1 p2 (Par2 x) = Par2 <$> bitraverse (mapRs cnv p1 p2) (mapRs cnv p1 p2) x
