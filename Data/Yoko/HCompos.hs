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





data FoundDC star = NoCorrespondingConstructorFor_In_ star star | Match star

type family WithMessage (dcA :: *) (b :: *) (dcB :: Maybe *) :: FoundDC *
type instance WithMessage dcA b (Just x) = Match x
type instance WithMessage dcA b Nothing  = NoCorrespondingConstructorFor_In_ dcA b


-- | @FindDCs dcA dcBs@ returns a type-level @Maybe@. @Just dcB@ is a fields
-- type @dcB@ where @'Tag' dcA ~ dcB@.
type family FindDCs (s :: Digit) (dcBs :: *) :: Maybe *
type instance FindDCs s (N dc) =
  If   (Equal s (Tag dc))   (Just dc)   Nothing
type instance FindDCs s (a :+: b) = DistMaybePlus (FindDCs s a) (FindDCs s b)





instance (HCompos cnv a t, HCompos cnv b t
         ) => HCompos cnv (a :+: b) t where
  hcompos cnv = foldPlus (hcompos cnv) (hcompos cnv)

-- NB only works if there's exactly one matching constructor
instance (Generic dcA, Match dcB ~ WithMessage dcA b (FindDCs (Tag dcA) (DCs b)),
          MapRs cnv (ResultsInIncompatibleFields dcA dcB) dcA dcB (Rep dcA) (Rep dcB),
          DC dcB, Codomain dcB ~ b, DT b
         ) => HCompos cnv (N dcA) b where
  hcompos cnv =
    foldN $ liftA (rejoin . (id :: dcB -> dcB) . obj) . mapRs cnv msgp p1 p2 . rep
    where p1 :: Proxy dcA; p1 = Proxy; p2 :: Proxy dcB; p2 = Proxy
          msgp = ResultsInIncompatibleFields :: ResultsInIncompatibleFields dcA dcB

data ResultsInIncompatibleFields (dcA :: *) (dcB :: *) = ResultsInIncompatibleFields



-- applies cnv to every Rec in a product; identity on other factors; the dc and
-- dc' parameters are just for error messages: all instances treat them
-- parametrically

-- | Same as @compos@ semantics, but with a generalized type and just for
-- converting between product representations.
class Applicative (Idiom cnv) => MapRs cnv msg dc dc' prod prod' where
  mapRs :: cnv -> msg -> Proxy dc -> Proxy dc' -> prod -> Idiom cnv prod'

instance Convert cnv a b => MapRs cnv msg dc dc' (Rec a) (Rec b) where
  mapRs cnv _ _ _ (Rec x) = Rec <$> convert cnv x

instance Applicative (Idiom cnv) => MapRs cnv msg dc dc' (Dep a) (Dep a) where
  mapRs _ _ _ _ = pure
instance Applicative (Idiom cnv) => MapRs cnv msg dc dc' U       U       where
  mapRs _ _ _ _ = pure

instance (MapRs cnv msg dc dc' a a', MapRs cnv msg dc dc' b b'
         ) => MapRs cnv msg dc dc' (a :*: b) (a' :*: b') where
  mapRs cnv msgp p1 p2 (a :*: b) = (:*:) <$> mapRs cnv msgp p1 p2 a <*> mapRs cnv msgp p1 p2 b

instance (Traversable f, MapRs cnv msg dc dc' a a'
         ) => MapRs cnv msg dc dc' (Par1 f a) (Par1 f a') where
  mapRs cnv msgp p1 p2 (Par1 x) = Par1 <$> traverse (mapRs cnv msgp p1 p2) x

instance (Bitraversable f, MapRs cnv msg dc dc' a a', MapRs cnv msg dc dc' b b'
         ) => MapRs cnv msg dc dc' (Par2 f a b) (Par2 f a' b') where
  mapRs cnv msgp p1 p2 (Par2 x) = Par2 <$> bitraverse (mapRs cnv msgp p1 p2) (mapRs cnv msgp p1 p2) x
