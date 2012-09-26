{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses,
  FlexibleContexts, FlexibleInstances, UndecidableInstances,
  ScopedTypeVariables, DataKinds, PolyKinds  #-}

{-# OPTIONS_GHC -fcontext-stack=250 #-}

{- |

Module      :  Data.Yoko.HCompos
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

The generic homomorphism or \"heterogenous compos\".

See the paper \"A Pattern for Almost Homomorphic Functions\" at <http://www.ittc.ku.edu/~nfrisby/frisby-2012-wgp.pdf>, presented at the Workshop on Generic Programming 2012.

-}

module Data.Yoko.HCompos where

import Data.Yoko.TypeBasics
import Data.Yoko.W
import Data.Yoko

import Control.Applicative
import Data.Traversable (Traversable, traverse)
import Data.Bitraversable (Bitraversable, bitraverse)

import Type.Digits (Digit)





-- | The applicative functor required by the conversion.
type family Idiom (cnv :: *) :: * -> *

-- | Use the conversion @cnv@ to convert from @a@ to @b@.
class Applicative (Idiom cnv) => Convert0 cnv a b where
  convert0 :: cnv -> a -> Idiom cnv b

-- | The generic version of @convert@; operates on /disbanded data types/.
class Applicative (Idiom cnv) => HCompos0 cnv a t where
  hcompos0 :: cnv -> a p1 p0 -> Idiom cnv t




-- these two instances make functions work directly for singly-recursive data
-- types
type instance Idiom (a -> i b) = i
instance (Applicative i, a ~ x, b ~ y) => Convert0 (a -> i b) x y where convert0 = ($)





data FoundDC (k :: *) (l :: *) = NoCorrespondingConstructorFor_In_ k k | Match l

type family WithMessage (dcA :: k) (b :: k) (dcB :: Maybe l) :: FoundDC k l
type instance WithMessage dcA b (Just x) = Match x
type instance WithMessage dcA b Nothing  = NoCorrespondingConstructorFor_In_ dcA b


-- | @FindDCs dcA dcBs@ returns a type-level @Maybe@. @Just dcB@ is a fields
-- type @dcB@ where @'Tag' dcA ~ dcB@.
type family FindDCs (s :: Digit) (dcBs :: * -> * -> *) :: Maybe (* -> * -> *)
type instance FindDCs s (N dc) =
  If   (Equal s (Tag dc))   (Just (N dc))   Nothing
type instance FindDCs s (a :+: b) = DistMaybePlus (FindDCs s a) (FindDCs s b)





instance (HCompos0 cnv a t, HCompos0 cnv b t
         ) => HCompos0 cnv (a :+: b) t where
  hcompos0 cnv = foldPlus (hcompos0 cnv) (hcompos0 cnv)

-- NB only works if there's exactly one matching constructor
instance (Generic dcA, Match (N dcB) ~ WithMessage dcA b (FindDCs (Tag dcA) (DCs b)),
          MapRs0 cnv (ResultsInIncompatibleFields dcA dcB) dcA dcB (Rep dcA) (Rep dcB),
          DC dcB, Codomain dcB ~ b, DT b
         ) => HCompos0 cnv (N dcA) b where
  hcompos0 cnv =
    foldN0 $ liftA (unSym0 rejoin . (id :: dcB -> dcB) . unW'0 obj) . mapRs0 cnv msgp p1 p2 . unW0 rep
    where p1 :: Proxy dcA; p1 = Proxy; p2 :: Proxy dcB; p2 = Proxy
          msgp = ResultsInIncompatibleFields :: ResultsInIncompatibleFields dcA dcB

data ResultsInIncompatibleFields (dcA :: k) (dcB :: k) = ResultsInIncompatibleFields



-- applies cnv to every Rec in a product; identity on other factors; the dc and
-- dc' parameters are just for error messages: all instances treat them
-- parametrically

-- | Same as @compos@ semantics, but with a generalized type and just for
-- converting between product representations.
class Applicative (Idiom cnv) => MapRs0 cnv msg dc dc' prod prod' where
  mapRs0 :: cnv -> msg -> Proxy dc -> Proxy dc' -> prod p1 p0 -> Idiom cnv (prod' p1 p0)

instance Applicative (Idiom cnv) => MapRs0 cnv msg dc dc' U       U       where
  mapRs0 _ _ _ _ = pure

instance (MapRs0 cnv msg dc dc' a a', MapRs0 cnv msg dc dc' b b'
         ) => MapRs0 cnv msg dc dc' (a :*: b) (a' :*: b') where
  mapRs0 cnv msgp p1 p2 (a :*: b) = (:*:) <$> mapRs0 cnv msgp p1 p2 a <*> mapRs0 cnv msgp p1 p2 b

instance MapRs0 cnv msg dc dc' a a' => MapRs0 cnv msg dc dc' (C dcA a) (C dcB a') where
  mapRs0 cnv msgp p1 p2 (C x) = C <$> mapRs0 cnv msgp p1 p2 x

instance Convert0 cnv a b => MapRs0 cnv msg dc dc' (T0 (Rec lbl) a) (T0 (Rec lbl') b) where
  mapRs0 cnv _ _ _ (T0 x) = T0 <$> convert0 cnv x

instance Applicative (Idiom cnv) => MapRs0 cnv msg dc dc' (T0 Dep a) (T0 Dep a) where
  mapRs0 _ _ _ _ = pure

instance (Traversable f, MapRs0 cnv msg dc dc' a a'
         ) => MapRs0 cnv msg dc dc' (T1 Dep f a) (T1 Dep f a') where
  mapRs0 cnv msgp p1 p2 (T1 x) = T1 <$> traverse (mapRs0 cnv msgp p1 p2) x

instance (Bitraversable f, MapRs0 cnv msg dc dc' a a', MapRs0 cnv msg dc dc' b b'
         ) => MapRs0 cnv msg dc dc' (T2 Dep f a b) (T2 Dep f a' b') where
  mapRs0 cnv msgp p1 p2 (T2 x) = T2 <$> bitraverse (mapRs0 cnv msgp p1 p2) (mapRs0 cnv msgp p1 p2) x
