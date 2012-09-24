{-# LANGUAGE ScopedTypeVariables, PolyKinds, DataKinds, MultiParamTypeClasses,
  TypeFamilies, UndecidableInstances, FlexibleInstances, FlexibleContexts #-}

module Data.Yoko.MinCtors.Minima
  (NCtor, NRec, NP1, NP0, Minima2, Minima1, Minimum,
   DTsCVec, SumInfo, SC_SumInfo,
   SiblingInT, SiblingInC, addMinima2, addSiblingInTs,
   solve_sibling_set, solve_sibling_set',
   plug10, plug0, plug10', plug0') where

import Data.Yoko.TypeBasics

import Data.Yoko.View

import Data.Yoko.MinCtors.MMap (MMap)
import qualified Data.Yoko.MinCtors.MMap as MMap

import qualified Data.Foldable as F

import Data.Semigroup (Min(..))

import Data.Traversable (traverse)
import Data.Maybe (catMaybes)



instance Functor Min where fmap f (Min a) = Min (f a)



--------------------
-- an appropriate abstraction for the MinCtors question
type NCtor = Int
type NRec  = Int
type NP1   = Int
type NP0   = Int

type Minima2 = MMap (NP1, NP0) Min NCtor
type Minima1 = MMap NP0        Min NCtor
type Minimum = MMap ()         Min NCtor

-- scale each coordinate
scale :: Int -> Minima2 -> Minima2
scale i = MMap.mapWithMonoKeys (\(np1, np0) -> (i * np1, i * np0)) (fmap (i *))

-- take Cartesian product, add coordinates point-wise, and re\"normalize\"
addMinima2 :: Minima2 -> Minima2 -> Minima2
addMinima2 m m' = flip MMap.foldMap m $ \(np1, np0) (Min k) ->
  flip MMap.foldMap m' $ \(np1', np0') (Min k') ->
    MMap.singleton (np1 + np1', np0 + np0') (Min $ k + k')

-- product and sum info
type DTsCVec t = CVec (SiblingDTs t)

type SumInfo t = MMap (DTsCVec t NRec, NP1, NP0) Min NCtor

scaleSiblingInTs :: Int -> SiblingInT ts -> SiblingInT ts
scaleSiblingInTs i = MMap.mapWithMonoKeys (\(r, np1, np0) -> (fmap (i *) r, i * np1, i * np0)) (fmap (i *))

addSiblingInTs :: Ord (CVec ts NRec) => SiblingInT ts -> SiblingInT ts -> SiblingInT ts
addSiblingInTs m m' = flip MMap.foldMap m $ \(rs, np1, np0) (Min k) ->
  flip MMap.foldMap m' $ \(rs', np1', np0') (Min k') ->
    MMap.singleton (cvZipWith (+) rs rs', np1 + np1', np0 + np0') (Min $ k + k')





--------------------
-- solve a sibling set

-- let cnv x = ($ x) $ MMap . Map.fromList . map (\(recs, np1, np0, k) -> ((recs, np1, np0), k))

-- TODO Put an interface around 'solve' so it can also be applied to
-- non-recursive data types -- this might involve a token type representing the
-- entire "sibling set", even for non-recursive types

-- TODO how to memoize the sibling set analysis as a CAF with all siblings'
-- MinCtors dictionaries sharing the CAF's elements?

-- | @type instance 'App' SC_SumInfo t = 'SumInfo' t@
data SC_SumInfo t = SC_SumInfo
type instance App SC_SumInfo t = SumInfo t

solve_sibling_set ::
  (Eq (CVec ts Minima2), VRepeat ts,
   VFunctor (SiblingInC ts) ts, VEnum ts) => Vec ts SC_SumInfo -> Work ts
solve_sibling_set = solve_sibling_set' . homogenize

solve_sibling_set' ::
  (Eq (CVec ts Minima2), VRepeat ts, VEnum ts) => CVec ts (SiblingInT ts) -> Work ts
solve_sibling_set' table = chaotic (step table) $ initialize table

-- 1) start with the smallest non-recursive ctors

-- 2) build up only from those, so we're maintaining a correct answer the
-- entire time

-- 3) codata siblings end up as MMap.empty.

-- the work set holds the sofar determined answers -- only the ones that are
-- gauranteed to be minimal. Codata siblings never get changed from MMap.empty.
type Work ts = CVec ts Minima2

-- like SC_SumInfo except parameterized over the sibling set instead of just a
-- single sibling
type SiblingInT ts = MMap (CVec ts NRec, NP1, NP0) Min NCtor

-- switch to a 'CVec', since all of the 'DTs' instances are compatible...
homogenize :: forall ts. VFunctor (SiblingInC ts) ts =>
              Vec ts SC_SumInfo -> CVec ts (SiblingInT ts)
homogenize = (CVec .) $ vMap (Proxy :: Proxy (SiblingInC ts)) $ \_ -> id

-- ...in this way
class    (ts ~ SiblingDTs t) => SiblingInC (ts :: [k]) (t :: k)
instance (ts ~ SiblingDTs t) => SiblingInC  ts          t

-- the initial work set is the siblings' smallest non-recursive constructors
initialize :: CVec ts (SiblingInT ts) -> Work ts
initialize = fmap $ \ctors -> flip MMap.foldMap ctors $ \(recs, np1, np0) k ->
  if F.all (0 ==) recs -- non-recursive ctor iff no recursive occurrences
  then MMap.singleton (np1, np0) k
  else MMap.empty

-- extend the working set with the unsolved siblings that are now soluble
step :: VEnum ts => CVec ts (SiblingInT ts) -> Work ts -> Work ts
step table sofar = cvZipWith leftbias sofar $ flip fmap table $
  MMap.foldMap $ \(recs, np1, np0) k -> -- fold over products in this sibling
    -- if all of its non-zero NRecs are solved...
    let all_answered = flip traverse (cvAddIndexes recs) $ \(idx, times) ->
          if times <= 0 then Just Nothing -- omit without failing
          else let answer = sofar `cvAt` idx
               in if MMap.null answer then Nothing -- fail
                  else Just $ Just $ scale times answer -- emit
    in ($ all_answered) $ maybe MMap.empty $
         foldl addMinima2 (MMap.singleton (np1, np0) k) . catMaybes . cvec2list

leftbias m1 m2 = if MMap.null m1 then m2 else m1

-- rinse and repeat until clean
chaotic :: Eq a => (a -> a) -> a -> a
chaotic f = w where w x = let x' = f x in if x == x' then x else w x'





--------------------
-- combining minima

plug0 :: Ord (CVec ts NRec) => Minima2 -> SiblingInT ts -> SiblingInT ts
plug0 f s0 = flip MMap.foldMap f $ \(_, np0) (Min k) ->
  MMap.map (fmap (+k)) $ scaleSiblingInTs np0 s0

plug10 :: Ord (CVec ts NRec) => Minima2 -> SiblingInT ts -> SiblingInT ts -> SiblingInT ts
plug10 f s1 s0 = flip MMap.foldMap f $ \(np1, np0) (Min k) ->
  MMap.map (fmap (+k)) $ scaleSiblingInTs np1 s1 `addSiblingInTs` scaleSiblingInTs np0 s0

plug0' :: Minima2 -> Minima2 -> Minima2
plug0' f s0 = flip MMap.foldMap f $ \(_, np0) (Min k) ->
  MMap.map (fmap (+k)) $ scale np0 s0

plug10' :: Minima2 -> Minima2 -> Minima2 -> Minima2
plug10' f s1 s0 = flip MMap.foldMap f $ \(np1, np0) (Min k) ->
  MMap.map (fmap (+k)) $ scale np1 s1 `addMinima2` scale np0 s0
