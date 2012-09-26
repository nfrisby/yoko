module Data.Yoko.MinCtors.Prims0 where

import qualified GHC.Word
import qualified GHC.ForeignPtr

import Data.Yoko.MinCtors



instance MinCtors Int     where minCtors = nCtors 0
instance MinCtors Integer where minCtors = nCtors 0
instance MinCtors Char    where minCtors = nCtors 0
instance MinCtors Float   where minCtors = nCtors 0
instance MinCtors Double  where minCtors = nCtors 0
instance MinCtors GHC.Word.Word8 where minCtors = nCtors 0
instance MinCtors GHC.ForeignPtr.ForeignPtr where minCtors = nCtors 0
