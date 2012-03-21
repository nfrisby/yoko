{-# LANGUAGE TypeOperators, FlexibleInstances, FlexibleContexts,
  UndecidableInstances #-}

module LambdaLift.DeepSeq where

import Data.Yoko



class DeepSeq a where rnf :: a -> ()
instance DeepSeq a => DeepSeq [a] where
  rnf [] = ()
  rnf (x : xs) = rnf x `seq` rnf xs
instance DeepSeq a => DeepSeq (N a) where rnf = rnf . unN
instance (DeepSeq a, DeepSeq b) => DeepSeq (a :+: b) where
  rnf = foldPlus rnf rnf
instance DeepSeq sum => DeepSeq (DCsOf a sum) where rnf = rnf . unDCsOf
instance (DeepSeq a, DeepSeq b) => DeepSeq (a :*: b) where
  rnf = foldTimes seq rnf rnf
instance DeepSeq a => DeepSeq (Rec a) where rnf = rnf . unRec
instance DeepSeq a => DeepSeq (Dep a) where rnf = rnf . unDep
instance DeepSeq (f a) => DeepSeq (Par1 f a) where rnf = rnf . unPar1
instance DeepSeq U where rnf U = ()

instance DeepSeq Int where rnf = (`seq` ())
instance (DeepSeq a, DeepSeq b) => DeepSeq (Either a b) where
  rnf = either rnf rnf

instance (DeepSeq a, DeepSeq b, DeepSeq c) =>
  DeepSeq (a, b, c) where
  rnf (a, b, c) = rnf a `seq` rnf b `seq` rnf c
instance (DeepSeq a, DeepSeq b, DeepSeq c, DeepSeq d) =>
  DeepSeq (a, b, c, d) where
  rnf (a, b, c, d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
