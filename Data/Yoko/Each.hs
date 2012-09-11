{-# LANGUAGE KindSignatures, ConstraintKinds, MultiParamTypeClasses,
  Rank2Types, FlexibleInstances, UndecidableInstances, TypeOperators #-}

{- |

Module      :  Data.Yoko.Each
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Basic support for folding through type-level sums.

-}

module Data.Yoko.Each (Each, each) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation


-- | The constraint @Each con sum@ corresponds to the constraing @forall dc in
-- sum. con dc@.
type Each = Each_

-- | Fold through a type-level sum.
each :: Each cxt sum => Proxy cxt -> (forall a. cxt a => a -> b) -> sum -> b
each = each_






class Each_ cxt sum where
  each_ :: Proxy cxt -> (forall a. cxt a => a -> b) -> sum -> b



instance cxt a => Each_ cxt (N a) where each_ _ f (N x) = f x

instance (Each_ cxt a, Each_ cxt b) => Each_ cxt (a :+: b) where
  each_ c f = foldPlus (each c f) (each c f)

--instance Each_ cxt sum => Each_ cxt (DCsOf t sum) where
--  each_ c f = each c f . unDCsOf





_ex = putStrLn $ each (Proxy :: Proxy Show) show $
       L (N 'n') `asTypeOf` R (N True)
