{-# LANGUAGE MultiParamTypeClasses, KindSignatures #-}

module Data.Yoko.TypeSumsAux where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation



-- this * is Bool, ideally
class Partition_N (bn :: *) x subL subR where
  partition_N :: Proxy bn -> N x -> Either subL subR
