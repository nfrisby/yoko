{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeFamilies, UndecidableInstances, Rank2Types #-}

{- |

Module      :  Data.Yoko.SmartPreciseCase
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Using some McBride \"Faking It\" style trickery to make @precise_case@
polyvariadic in the ad-hoc cases.

E.g.

> precise_case x (\(C_ a b) -> special_case a b) (Default $ \x -> generic_function x)

and

> precise_case x (\(C_ a b) -> special_case a b) (\(D_ x) -> special_case2 x) (Default $ \x -> generic_function x)

both work.

-}

module Data.Yoko.SmartPreciseCase (precise_case0, Default(..)) where

import Data.YokoRaw hiding (precise_case0)
import qualified Data.YokoRaw as Raw


class Error_precise_case_requires_at_least_1_special_case a

data AdHoc dcs dt r = AdHoc dt (forall p1 p0. dcs p1 p0 -> r)
newtype Default a r = Default (forall p1 p0. a p1 p0 -> r)





class Builder adhoc bldr where
  precise_case_ :: adhoc -> bldr

instance Error_precise_case_requires_at_least_1_special_case () => Builder (Start dt) (Default a final -> b) where
  precise_case_ = error "precise_case_ requires at least 1 special case"

newtype Start dt = Start dt

instance (dt ~ Codomain dc,
          Builder (AdHoc (N dc) (Codomain dc) r) bldr) =>
  Builder (Start dt) ((dc -> r) -> bldr) where
  precise_case_ (Start dt) f = precise_case_ $ AdHoc dt $ one f

instance (dt ~ Codomain dc, dt ~ Codomain0 dcs, r ~ r', -- False ~ Elem dc dcs,
          Builder (AdHoc (dcs :+: N dc) dt r) bldr) =>
  Builder (AdHoc dcs dt r) ((dc -> r') -> bldr) where
  precise_case_ (AdHoc dt adhoc) f = precise_case_ $ AdHoc dt $ adhoc ||. f

instance (DT dt, dt ~ Codomain0 dcs, dt ~ Codomain0 (DCs dt),
          Partition (DCs dt) dcs (DCs dt :-: dcs),
          x ~ (DCs dt :-: dcs),
          final ~ r, final' ~ r) =>
  Builder (AdHoc dcs dt r) (Default x final -> final') where
  precise_case_ (AdHoc dt adhoc) (Default dflt) = Raw.precise_case0 dflt dt adhoc

precise_case0 :: Builder (Start dt) bldr => dt -> bldr
precise_case0 = precise_case_ . Start




{-

data T = A | B Int | C Bool

yokoTH ''T




*PreciseCase> precise_case A (\(B_ i) -> i) (Default $ const 0)
0
*PreciseCase> precise_case (B 3) (\(B_ i) -> i) (Default $ const 0)
3
*PreciseCase> precise_case (B 3) (\(B_ i) -> i) (\A_ -> 1) (Default $ const 0)
3
*PreciseCase> precise_case A (\(B_ i) -> i) (\A_ -> 1) (Default $ const 0)
1

-}
