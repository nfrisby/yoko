{-# LANGUAGE TypeOperators, LambdaCase, FlexibleContexts, UndecidableInstances,
  DataKinds, DefaultSignatures, FlexibleInstances, ScopedTypeVariables,
  TypeFamilies #-}

{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, Rank2Types #-}

module Data.Yoko.Compos where

import Data.YokoRaw
import Control.Applicative
import Data.Yoko.Traversable



class Compos c t where
  compos :: Applicative i => Proxy c -> (forall t. c t => t -> i t) -> t -> i t
  default compos :: (DT t, Compos2Sum c (DCs t) t, Applicative i) => Proxy c -> (forall t. c t => t -> i t) -> t -> i t
  compos = gen_compos

pure_compos :: Compos c t => Proxy c -> (forall t. c t => t -> t) -> t -> t
pure_compos pc rec = runId . compos pc (Id . rec)


gen_compos :: (DT t, Compos2Sum c (DCs t) t, Applicative i) => Proxy c -> (forall t. c t => t -> i t) -> t -> i t
gen_compos pc rec = compos2sum pc rec . disband . W0



class Compos2Sum c dcs t where
  compos2sum :: Applicative i => Proxy c -> (forall t. c t => t -> i t) -> dcs p1 p0 -> i t

instance (Compos2Sum c l t, Compos2Sum c r t) => Compos2Sum c (l :+: r) t where
  compos2sum pc rec = foldPlus (compos2sum pc rec) (compos2sum pc rec)

instance Compos2Sum c Void t where compos2sum = error "compos @Void"
instance (DC dc, Codomain dc ~ t, Compos2Prod c (Rep dc)) => Compos2Sum c (N dc) t where
  compos2sum pc rec = fmap (unW0 . rejoin . ascription . obj) . compos2prod pc rec . rep . unN
    where ascription :: W dc p1 p0 -> W dc p1 p0
          ascription = id

class Compos2Prod c prod where
  compos2prod :: Applicative i => Proxy c -> (forall t. c t => t -> i t) -> prod p1 p0 -> i (prod p1 p0)

instance (Compos2Prod c l, Compos2Prod c r) => Compos2Prod c (l :*: r) where
  compos2prod pc rec (l :*: r) = (:*:) <$> compos2prod pc rec l <*> compos2prod pc rec r
instance Compos2Prod c U where compos2prod _ _ U = pure U
instance Compos2Prod c r => Compos2Prod c (C dc r) where
  compos2prod pc rec (C x) = C <$> compos2prod pc rec x

instance c rec => Compos2Prod c (T0 (Rec lbl) rec) where compos2prod _ rec (T0 x) = T0 <$> rec x
instance Compos2Prod c (T0 Dep dep) where compos2prod _ _ (T0 x) = pure (T0 x)
instance (Traversable t, Compos2Prod c a) => Compos2Prod c (T1 Dep t a) where
  compos2prod pc rec (T1 x) = T1 <$> traverse (compos2prod pc rec) x
instance (Traversable2 t, Compos2Prod c b, Compos2Prod c a) => Compos2Prod c (T2 Dep t b a) where
  compos2prod pc rec (T2 x) = T2 <$> traverse2 (compos2prod pc rec) (compos2prod pc rec) x

instance Compos2Prod c Par1 where compos2prod _ _ (Par1 x) = pure $ Par1 x
instance Compos2Prod c Par0 where compos2prod _ _ (Par0 x) = pure $ Par0 x
