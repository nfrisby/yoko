{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeFamilies, UndecidableInstances #-}

{- |

Module      :  Data.Yoko.SmartPreciseCase
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

Using some McBride \"Faking It\" style trickery to make @precise_case@
polyvariadic in the ad-hoc cases.

-}

module Data.Yoko.SmartPreciseCase where

import Data.YokoRaw hiding (precise_case)
import qualified Data.YokoRaw as Raw


class Error_precise_case_requires_at_least_1_special_case a

data AdHoc dcs dt r = AdHoc dt (dcs -> r)
newtype Default a = Default a





class Builder adhoc bldr where
  precise_case_ :: adhoc -> bldr

instance Error_precise_case_requires_at_least_1_special_case () => Builder (Start dt) (Default a -> b) where
  precise_case_ = error "precise_case_ requires at least 1 special case"

newtype Start dt = Start dt

instance (dt ~ Codomain dc,
          Builder (AdHoc (N dc) (Codomain dc) r) bldr) =>
  Builder (Start dt) ((dc -> r) -> bldr) where
  precise_case_ (Start dt) f = precise_case_ $ AdHoc dt $ one f

instance (dt ~ Codomain dc, dt ~ Codomain dcs, r ~ r', -- False ~ Elem dc dcs,
          Builder (AdHoc (dcs :+: N dc) dt r) bldr) =>
  Builder (AdHoc dcs dt r) ((dc -> r') -> bldr) where
  precise_case_ (AdHoc dt adhoc) f = precise_case_ $ AdHoc dt $ adhoc ||. f

instance (DT dt, dt ~ Codomain dcs, dt ~ Codomain (DCs dt),
          Partition (DCs dt) dcs (DCs dt :-: dcs),
          x ~ (DCs dt :-: dcs -> r),
          final ~ r) =>
  Builder (AdHoc dcs dt r) (Default x -> final) where
  precise_case_ (AdHoc dt adhoc) (Default dflt) = Raw.precise_case dflt dt adhoc

precise_case :: Builder (Start dt) bldr => dt -> bldr
precise_case = precise_case_ . Start




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
