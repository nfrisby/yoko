{-# LANGUAGE TypeOperators, FlexibleInstances, FlexibleContexts,
  UndecidableInstances, DefaultSignatures, PolyKinds, DataKinds, TypeFamilies #-}

{- |

Module      :  LambdaLift.DeepSeq
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

An example lambba lifter using @hcompos@.

-}

module LambdaLift.DeepSeq where

import Data.Yoko
import Data.Bifunctor


pK :: Proxy ('KProxy :: KProxy * *)
pK = Proxy


class DeepSeq0 a where
  rnf0 :: a       -> ()
  default rnf0 :: (DeepSeq2 (DCs a ('KProxy :: KProxy * *)), DT a ('KProxy :: KProxy * *)) => a -> ()
  rnf0 = rnf2 . unW0 (disband pK)
class DeepSeq1 a where
  rnf1 :: a    () -> ()
  default rnf1 :: (DeepSeq2 (DCs a ('KProxy :: KProxy * *)), DT a ('KProxy :: KProxy * *)) => a () -> ()
  rnf1 = rnf2 . unW1 (disband pK)
class DeepSeq2 a where
  rnf2 :: a () () -> ()
  default rnf2 :: (DeepSeq2 (DCs a ('KProxy :: KProxy * *)), DT a ('KProxy :: KProxy * *)) => a () () -> ()
  rnf2 = rnf2 . unW2 (disband pK)

instance (any ~ ('KProxy :: KProxy * *), WN a any,
          DeepSeq2 (Rep a any), Generic a any) => DeepSeq2 (N a) where
  rnf2 = rnf2 . unSym pK (rep pK) (unN pK)
instance (DeepSeq2 a, DeepSeq2 b) => DeepSeq2 (a :+: b) where
  rnf2 = foldPlus rnf2 rnf2

instance DeepSeq2 U where rnf2 U = ()
instance (DeepSeq2 a, DeepSeq2 b) => DeepSeq2 (a :*: b) where
  rnf2 = foldTimes seq rnf2 rnf2
instance DeepSeq2 a => DeepSeq2 (C dc a) where rnf2 = rnf2 . unC

instance DeepSeq0 t => DeepSeq2 (T0 (Dep t)) where rnf2 = rnf0 . unT0
instance DeepSeq0 t => DeepSeq2 (T0 (Rec lbl t)) where rnf2 = rnf0 . unT0
instance DeepSeq2 (T0 Par0) where rnf2 = (`seq` ()) . unT0
instance DeepSeq2 (T0 Par1) where rnf2 = (`seq` ()) . unT0
instance (Functor f, DeepSeq1 f, DeepSeq2 a) => DeepSeq2 (T1 (Dep f) a) where
  rnf2 = rnf1 . fmap rnf2 . unT1
instance (Functor f, DeepSeq1 f, DeepSeq2 a) => DeepSeq2 (T1 (Rec lbl f) a) where
  rnf2 = rnf1 . fmap rnf2 . unT1
instance (Bifunctor f, DeepSeq2 f, DeepSeq2 a, DeepSeq2 b) => DeepSeq2 (T2 (Dep f) a b) where
  rnf2 = rnf2 . bimap rnf2 rnf2 . unT2
instance (Bifunctor f, DeepSeq2 f, DeepSeq2 a, DeepSeq2 b) => DeepSeq2 (T2 (Rec lbl f) a b) where
  rnf2 = rnf2 . bimap rnf2 rnf2 . unT2

--instance DeepSeq2 Par0 where rnf2 (Par0 ()) = ()
--instance DeepSeq2 Par1 where rnf2 (Par1 ()) = ()



instance (EQ ~ SpineCompare a a, DeepSeq0 a) => DeepSeq0 [a]
instance DeepSeq1 []

instance DeepSeq0 Int where rnf0 = (`seq` ())
instance (DeepSeq0 a, DeepSeq0 b) => DeepSeq0 (Either a b) where
  rnf0 = either rnf0 rnf0

instance (DeepSeq0 a, DeepSeq0 b, DeepSeq0 c) =>
  DeepSeq0 (a, b, c) where
  rnf0 (a, b, c) = rnf0 a `seq` rnf0 b `seq` rnf0 c
instance (DeepSeq0 a, DeepSeq0 b, DeepSeq0 c, DeepSeq0 d) =>
  DeepSeq0 (a, b, c, d) where
  rnf0 (a, b, c, d) = rnf0 a `seq` rnf0 b `seq` rnf0 c `seq` rnf0 d
