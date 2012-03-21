{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts,
  MultiParamTypeClasses, FlexibleInstances, ConstraintKinds,
  UndecidableInstances #-}

module Data.Yoko.View where

import Data.Yoko.Representation
import Data.Yoko.TypeSums (Embed, Partition, (:-:))
import Data.Yoko.Each





type family Tag dc

type family Range dc
class (Generic dc, DT (Range dc)) => DC dc where rejoin :: dc -> Range dc

type family DCs t
type Disbanded t = DCsOf t (DCs t)
class Each IsDCOf (DCs t) => DT t where disband :: t -> Disbanded t

class (Partition (DCs (Range dc)) (N dc) (DCs (Range dc) :-: N dc),
       Embed (N dc) (DCs (Range dc))) => IsDCOf dc
instance (Partition (DCs (Range dc)) (N dc) (DCs (Range dc) :-: N dc),
          Embed (N dc) (DCs (Range dc))) => IsDCOf dc
