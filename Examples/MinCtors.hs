{-# LANGUAGE TemplateHaskell, TypeFamilies, DataKinds #-}

module Examples.MinCtors where

import Data.Yoko
import Data.Yoko.MinCtors
import Data.Yoko.MinCtors.Prims0 ()

data I = I Int

data H = H I

data D = D0 H
       | D1 D
       | D2 D D

concat `fmap` mapM yokoTH [''I, ''H, ''D]

instance MinCtors I
instance MinCtors H
instance MinCtors D

{-

  *MinCtorsExample> minCtors (Proxy :: Proxy D)
  Just 3

This means that the minimal value uses three constructors.

@* -> *@ and @* -> * -> *@ kinded types have different result types. Consider
the minimal @(forall p1 p0. (p1, p0))@ value: it uses both of its parameters
once, and has its own single constructor.

  *MinCtorsExample> minCtors (Proxy :: Proxy (,))
  MMap {unMMap = fromList [((1,1),Min {getMin = 1})]}

Accordingly, the minimal @[]@ value uses its single parameter zero times.

  *MinCtorsExample> minCtors (Proxy :: Proxy [])
  MMap {unMMap = fromList [(0,Min {getMin = 1})]}

And there are two minimal @Either@ values, each which uses one of the
parameters. We track both because which one is ultimately minimal depends on
the instantiation of @Either@'s parameters, and their minimal counts.

  *MinCtorsExample> minCtors (Proxy :: Proxy Either)
  MMap {unMMap = fromList [((0,1),Min {getMin = 1}),((1,0),Min {getMin = 1})]}

These might not be necessary for your uses, but they are used by my generic
definitions in order to handle types like @T@ below that have internal
applications.

-}

data T = T (Either D ((Int, Int), (Bool, Bool)))

yokoTH ''T

instance MinCtors T
