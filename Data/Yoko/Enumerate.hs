{-# LANGUAGE LambdaCase, TypeOperators, FlexibleContexts, UndecidableInstances,
  DefaultSignatures, PolyKinds #-}

module Data.Yoko.Enumerate where

import Data.YokoRaw



interleave x y = diag [x, y]

diag :: [[a]] -> [a]
diag = \case
  [] -> []
  (l:ls) -> case l of
    []   ->     diag ls
    a:as -> a : diag (ls ++ [as])



class Enumerate t where
  enum :: [t]
  default enum :: (DT t, Enumerate2 (DCs t), AreDCsOf t (DCs t)) => [t]
  enum = gen_enum

gen_enum :: (DT t, Enumerate2 (DCs t), AreDCsOf t (DCs t)) => [t]
gen_enum = map (unW0 . band) $ enum2 ([] :: [()]) ([] :: [()])

class Enumerate1 t where
  enum1 :: [a] -> [t a]
  default enum1 :: (DT t, Enumerate2 (DCs t), AreDCsOf t (DCs t)) => [a] -> [t a]
  enum1 = gen_enum1

gen_enum1 :: (DT t, Enumerate2 (DCs t), AreDCsOf t (DCs t)) => [a] -> [t a]
gen_enum1 as = map (unW1 . band) $ enum2 ([] :: [()]) as

class Enumerate2 t where
  enum2 :: [b] -> [a] -> [t b a]
  default enum2 :: (DT t, Enumerate2 (DCs t), AreDCsOf t (DCs t)) => [b] -> [a] -> [t b a]
  enum2 = gen_enum2

gen_enum2 :: (DT t, Enumerate2 (DCs t), AreDCsOf t (DCs t)) => [b] -> [a] -> [t b a]
gen_enum2 bs as = map (unW2 . band) $ enum2 bs as



instance (Enumerate2 l, Enumerate2 r) => Enumerate2 (l :+: r) where
  enum2 bs as = map L (enum2 bs as) `interleave` map R (enum2 bs as)
instance Enumerate2 Void where enum2 _ _ = []
instance (DC dc, Enumerate2 (Rep dc)) => Enumerate2 (N dc) where
  enum2 bs as = map (N . obj) $ enum2 bs as

instance (Enumerate2 l, Enumerate2 r) => Enumerate2 (l :*: r) where
  enum2 bs as = diag $
                flip map (enum2 bs as) $ \l ->
                flip map (enum2 bs as) $ \r ->
                  l :*: r
instance Enumerate2 U where enum2 _ _ = [U]
instance Enumerate2 r => Enumerate2 (C dr r) where
  enum2 bs as = map C $ enum2 bs as

instance Enumerate t => Enumerate2 (T0 v t) where enum2 _ _ = map T0 enum
instance (Enumerate1 t, Enumerate2 a) => Enumerate2 (T1 v t a) where
  enum2 bs as = map T1 $ enum1 $ enum2 bs as
instance (Enumerate2 t, Enumerate2 b, Enumerate2 a) => Enumerate2 (T2 v t b a) where
  enum2 bs as = map T2 $ enum2 (enum2 bs as) (enum2 bs as)

instance Enumerate2 Par1 where enum2 bs _ = map Par1 bs
instance Enumerate2 Par0 where enum2 _ as = map Par0 as
