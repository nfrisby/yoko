module Data.Yoko.MinCtors.Prims1 where

import qualified GHC.Word
import qualified GHC.ForeignPtr

import Data.Yoko.MinCtors



instance MinCtors Int     where minCtors = nCtors 1
instance MinCtors Integer where minCtors = nCtors 1
instance MinCtors Char    where minCtors = nCtors 1
instance MinCtors Float   where minCtors = nCtors 1
instance MinCtors Double  where minCtors = nCtors 1
instance MinCtors GHC.Word.Word8 where minCtors = nCtors 1
instance MinCtors GHC.ForeignPtr.ForeignPtr where minCtors = nCtors 1
