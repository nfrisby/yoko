{-# LANGUAGE MultiParamTypeClasses, KindSignatures, DataKinds #-}

module Data.Yoko.TypeSumsAux where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation



class Partition_N (bn :: Bool) x subL subR where
  partition_N :: Proxy bn -> N x -> Either subL subR
