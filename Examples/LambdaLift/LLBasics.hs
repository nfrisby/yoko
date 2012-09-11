{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies,
  UndecidableInstances #-}

{- |

Module      :  LambdaLift.LLBasics
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

An example lambba lifter using @hcompos@.

-}

module LambdaLift.LLBasics where

import LambdaLift.Common

import LambdaLift.TLF

import qualified Data.IntMap as IM; import Data.IntMap (IntMap)

import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(pure, (<*>)))





-- # of formal variables and the mapping for captives
type Rename = (Int, IntMap Int)

lookupRN :: Rename -> Int -> Occ
lookupRN rn@(locals, m) i
  | i < locals = Par i
  | otherwise = maybe err Env $ IM.lookup (i - locals) m
  where err = error $ "LLBasics.lookupRN: unresolved variable: " ++ show (i, rn)



newtype M a =
  M {runM :: ([Type], Rename, Int) -> (a, [FunDec])}

instance Functor M where fmap = liftM
instance Applicative M where pure = return; (<*>) = ap
instance Monad M where
  return a = M $ \_ -> (a, [])
  m >>= k = M $ \(tys, rn, sh) ->
    -- NB backwards state: a and w' are circular
    let (a, w)  = runM m     (tys, rn, sh + length w')
        (b, w') = runM (k a) (tys, rn, sh)
    in (b, w ++ w')



ask :: M ([Type], Rename)
ask = M $ \ ~(x, y, _) -> ((x, y), [])

local :: (([Type], Rename) -> ([Type], Rename)) -> M a -> M a
local f (M g) = M $ \ ~(x, y, z) -> case f (x, y) of
  ~(x', y') -> g (x', y', z)



intermediates :: M Int
intermediates = M $ \ ~(_, _, s) -> (s, [])

emit :: FunDec -> M ()
emit w = M $ \_ -> ((), [w])

ignoreEmissions :: M a -> M a
ignoreEmissions (M f) = M $ \(tys, rn, _) -> f (tys, rn, 0)
