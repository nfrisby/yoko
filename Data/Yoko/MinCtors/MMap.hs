{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

-- | Like 'Map' but with a 'Monoid' instance that respects the value type's
-- 'Semigroup' instance.

module Data.Yoko.MinCtors.MMap where

import Data.Monoid

import Data.Semigroup (Semigroup)
import qualified Data.Semigroup as Semigroup

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Foldable as F



newtype MMap k f v = MMap {unMMap :: Map k (f v)}

deriving instance Eq (Map k (f v)) => Eq (MMap k f v)
deriving instance Show (Map k (f v)) => Show (MMap k f v)

map f (MMap m) = MMap $ Map.map f m

singleton k v = MMap $ Map.singleton k v

null (MMap m) = Map.null m

empty :: MMap k f v
empty = MMap Map.empty

instance (Ord k, Semigroup (f v)) => Monoid (MMap k f v) where
  mempty = MMap Map.empty
  MMap x `mappend` MMap y = MMap $ Map.unionWith (Semigroup.<>) x y

foldMap :: Monoid m => (k -> f v -> m) -> MMap k f v -> m
foldMap f (MMap m) = F.foldMap (uncurry f) $ Map.toList m

mapWithMonoKeys :: (k -> k1) -> (f v -> g v1) -> MMap k f v -> MMap k1 g v1
mapWithMonoKeys fk fv (MMap m) =
  MMap $ Map.mapKeysMonotonic fk $ Map.map fv m

lookup :: Ord k => k -> MMap k f v -> Maybe (f v)
lookup k (MMap m) = Map.lookup k m

fromList :: (Ord k, Semigroup (f v)) => [(k, f v)] -> MMap k f v
fromList = F.foldMap (uncurry singleton)

toList :: MMap k f v -> [(k, f v)]
toList (MMap m) = Map.toList m
