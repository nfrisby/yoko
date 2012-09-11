{- |

Module      :  Data.Yoko
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

This omnibus module is the only necessary import for using the @yoko@ generic
programming library.

(Some sophisticated functions' types might require the import of the
"Data.Yoko.TypeBasics" or "Data.Yoko.Each" modules.)

The "Data.Yoko.HCompos" module defines the generic homomorphism; see the paper
\"A Pattern for Almost Homomorphic Functions\" at
<http://www.ittc.ku.edu/~nfrisby/papers/frisby-wgp-2012.pdf>, published at the
Workshop on Generic Programming 2012. Much more details in my dissertation:
<http://www.ittc.ku.edu/~nfrisby/papers/frisby-dissertation.pdf>.

@dc@ type variables abstract over /fields types/.

@dcs@ and @sum@ type variables abstract over sums of /fields types/.

Types of the form @'DC' t@ are /disbanded data types/; for each fields type
@dc@ in the resulting sum, @'Codomain' dc ~ t@. That means they all correspond
to constructors from @t@.

A complete Template Haskell deriver is provided in the "Data.Yoko.TH" module.

It works for the data types that `instant-generics` works on, excluding indexed
data types. Yell loudly if you need that... then send me an email :) HTH!

-}

module Data.Yoko
  (module Data.YokoRaw, module Data.Yoko.SmartPreciseCase)
  where

import Data.YokoRaw hiding (precise_case)
import Data.Yoko.SmartPreciseCase
