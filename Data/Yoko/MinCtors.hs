{-# LANGUAGE DataKinds, TypeOperators, TypeFamilies, UndecidableInstances,
  DefaultSignatures, ViewPatterns, FlexibleContexts, FlexibleInstances,
  PolyKinds, MultiParamTypeClasses, Rank2Types #-}

module Data.Yoko.MinCtors (MinCtors(..), gen_minCtors) where

import Data.Yoko.TypeBasics
import Data.Yoko.Representation
import Data.Yoko.View

import Data.Semigroup (Min(..))
import qualified Data.Yoko.MinCtors.MMap as MMap
import Data.Yoko.MinCtors.Minima

import Data.Monoid (mappend)



--------------------
-- miscellaneous

pFrom :: Proxy t -> Proxy (Rep t)
pFrom _ = Proxy

type Prod t = (DTsCVec t NRec, NP1, NP0, NCtor)



--------------------
-- example reflections using the 'Minima' abstraction
nil_p, cons_p :: Prod []
nil_p  = (CVec $ VCons 0 VNil, 0, 0, 1)
cons_p = (CVec $ VCons 1 VNil, 0, 1, 1)

list_s :: [Prod []]; list_s = [nil_p, cons_p]

data Stream a = SCons a (Stream a)
type instance DTs Stream = RecDT '[] '[]

scons_p :: Prod Stream
scons_p = (CVec $ VCons 1 VNil, 0, 1, 1)

stream_s :: [Prod Stream]; stream_s = [scons_p]

data Even a = ENil | ECons a (Odd  a)
data Odd  a =        OCons a (Even a)
type instance DTs Even = RecDT '[]     '[Odd]
type instance DTs Odd  = RecDT '[Even] '[]

data ENil_  (p1 :: *) (p0 :: *) = ENil_
data ECons_ (p1 :: *) (p0 :: *) = ECons_
data OCons_ (p1 :: *) (p0 :: *) = OCons_

type instance Rep Even = C ENil_ U   :+: C ECons_ (Par0 :*: Rec1 ('S 'Z) Odd Par0)
type instance Rep Odd  = C OCons_ (Par0 :*: Rec1 'Z Even Par0)

enil_p, econs_p :: Prod Even
ocons_p         :: Prod Odd

enil_p  = (CVec $ VCons (0 :: Int) $ VCons 0 VNil, 0, 0, 1)
econs_p = (CVec $ VCons (0 :: Int) $ VCons 1 VNil, 0, 1, 1)
ocons_p = (CVec $ VCons (1 :: Int) $ VCons 0 VNil, 0, 1, 1)

even_s :: [Prod Even]; even_s = [enil_p, econs_p]
odd_s  :: [Prod Odd] ; odd_s  = [ocons_p]

unit_p :: Prod ()
unit_p = (CVec VNil, 0, 0, 1)

unit_s :: [Prod ()]
unit_s = [unit_p]



m1c_p, m1d_p :: Prod M1
m1c_p = (CVec $ VCons 0 $ VCons 0 VNil, 0, 0, 5)
m1d_p = (CVec $ VCons 0 $ VCons 1 VNil, 0, 0, 1)

m2c_p :: Prod M2
m2c_p = (CVec $ VCons 1 $ VCons 0 VNil, 0, 0, 1)

m1_s :: [Prod M1]; m1_s = [m1c_p, m1d_p]
m2_s :: [Prod M2]; m2_s = [m2c_p]



left_p, right_p :: Prod Either
left_p  = (CVec VNil, 1, 0, 1)
right_p = (CVec VNil, 0, 1, 1)



--------------------
-- TH will generate this eventually...
data False_ (p1 :: *) (p0 :: *) = False_
data True_  (p1 :: *) (p0 :: *) = True_

type instance DTs Bool = NonRecDT
type instance Rep Bool = C False_ U   :+:   C True_ U

newtype Tuple0_ (p1 :: *) (p0 :: *) = Tuple0_ ()

type instance DTs () = NonRecDT
type instance Rep () = C Tuple0_ U

type instance DTs (,)     = NonRecDT
type instance Rep (,)     = C (,) (Par1 :*: Par0)
type instance DTs ((,) a) = NonRecDT -- TODO ? map ($ a) (DTs (,))
type instance Rep ((,) a) = Subst1  (,) a
type instance DTs (a, b)  = NonRecDT
type instance Rep (a, b)  = Subst10 (,) a b

type instance DTs (,,)       = NonRecDT
-- type instance Rep (,,) = undefined
type instance DTs ((,,) a)   = NonRecDT
type instance Rep ((,,) a)   = C ((,,) a) (Dep a :*: Par1 :*: Par0)
type instance DTs ((,,) a b) = NonRecDT
type instance Rep ((,,) a b) = Subst1  ((,,) a) b
type instance DTs (a, b, c)  = NonRecDT
type instance Rep (a, b, c)  = Subst10 ((,,) a) b c

data Nothing_ (p1 :: *) (p0 :: *) = Nothing_
data Just_    (p1 :: *) (p0 :: *) = Just_ p0

type instance DTs Maybe     = NonRecDT
type instance Rep Maybe     = C Nothing_ U   :+:   C Just_ Par0
type instance DTs (Maybe a) = NonRecDT
type instance Rep (Maybe a) = Subst0 Maybe a

data Left_  (p1 :: *) (p0 :: *) = Left_  p1
data Right_ (p1 :: *) (p0 :: *) = Right_ p0

type instance DTs Either = NonRecDT
type instance Rep Either = C Left_ Par1   :+: C Right_ Par0
type instance DTs (Either a) = NonRecDT
type instance Rep (Either a) = Subst1 Either a
type instance DTs (Either a b) = NonRecDT
type instance Rep (Either a b) = Subst10 Either a b

data Nil_  (p1 :: *) (p0 :: *) = Nil_
data Cons_ (p1 :: *) (p0 :: *) = Cons_ p0 [p0]

type instance DTs []  = RecDT '[] '[]
type instance Rep []  = C Nil_ U   :+:   C Cons_ (Rec1 Z [] Par0)
type instance DTs [a] = RecDT '[] '[]
type instance Rep [a] = Subst0 [] a





--------------------
-- the internal classes

class MinInfoRec (t :: k) (ts :: [k1]) where
  minInfoRec :: Proxy t -> Proxy ts -> SiblingInT ts

class MinInfoNonRec (t :: k) where minInfoNonRec :: Proxy t -> Minima1

minima1ToSiblingInT :: VRepeat ts => Minima1 -> SiblingInT ts
minima1ToSiblingInT =
  MMap.mapWithMonoKeys (\(np1, np0) -> (cvRepeat 0, np1, np0)) id

void :: Minima1
void = MMap.singleton (0, 0) $ Min 0

oneCtor :: Minima1
oneCtor = MMap.singleton (0, 0) $ Min 1




instance MinCtors Int  where minCtors _ = oneCtor
instance MinCtors Char where minCtors _ = oneCtor



deApp :: Proxy (f :@: r) -> (Proxy f, Proxy r)
deApp _ = (Proxy, Proxy)

instance (Ord (CVec ts NRec), MinCtors f, MinInfoRec r ts) => MinInfoRec (f :@: r) ts where
  minInfoRec (deApp -> (pf, pr)) pts = minCtors pf `plug0` minInfoRec pr pts

instance (MinCtors f, MinInfoNonRec r) => MinInfoNonRec (f :@: r) where
  minInfoNonRec (deApp -> (pf, pr)) = minCtors pf `plug0'` minInfoNonRec pr

deApp2 :: Proxy ((ff :@@: r1) r0) -> (Proxy ff, Proxy r1, Proxy r0)
deApp2 _ = (Proxy, Proxy, Proxy)

instance (Ord (CVec ts NRec), MinCtors ff, MinInfoRec rB ts, MinInfoRec rA ts) => MinInfoRec ((ff :@@: rB) rA) ts where
  minInfoRec (deApp2 -> (ff, rB, rA)) pts =
    plug10 (minCtors ff) (minInfoRec rB pts) (minInfoRec rA pts)

instance (MinCtors ff, MinInfoNonRec rB, MinInfoNonRec rA) => MinInfoNonRec ((ff :@@: rB) rA) where
  minInfoNonRec (deApp2 -> (ff, rB, rA)) = plug10' (minCtors ff) (minInfoNonRec rB) (minInfoNonRec rA)



instance (VRepeat ts) => MinInfoRec (Void t) ts where minInfoRec _ _ = minima1ToSiblingInT void
instance MinInfoNonRec (Void t) where minInfoNonRec _ = void
{-
deN :: Proxy (N dc) -> Proxy dc
deN _ = Proxy

instance MinInfo1 dc => MinInfo1 (N dc) where
  minInfo1 = map (on1_3 succ) . minInfo1 . deN
-}

deC :: Proxy (C t r) -> Proxy r
deC _ = Proxy

instance MinInfoRec r ts => MinInfoRec (C dc r) ts where
  minInfoRec = (MMap.map (fmap succ) .) . minInfoRec . deC
instance MinInfoNonRec r => MinInfoNonRec (C dc r) where
  minInfoNonRec = MMap.map (fmap succ) . minInfoNonRec . deC



dePlus :: Proxy (l :+: r) -> (Proxy l, Proxy r)
dePlus _ = (Proxy, Proxy)

instance (Ord (CVec ts NRec), MinInfoRec l ts, MinInfoRec r ts) => MinInfoRec (l :+: r) ts where
  minInfoRec (dePlus -> (l, r)) pts = minInfoRec l pts `mappend` minInfoRec r pts
instance (MinInfoNonRec l, MinInfoNonRec r) => MinInfoNonRec (l :+: r) where
  minInfoNonRec (dePlus -> (l, r)) = minInfoNonRec l `mappend` minInfoNonRec r



instance MinInfoNonRec U where minInfoNonRec _ = void
instance (VRepeat ts) => MinInfoRec U ts where minInfoRec _ _ = minima1ToSiblingInT void

deTimes :: Proxy (l :*: r) -> (Proxy l, Proxy r)
deTimes _ = (Proxy, Proxy)

instance (Ord (CVec ts NRec), VRepeat ts, MinInfoRec l ts, MinInfoRec r ts) => MinInfoRec (l :*: r) ts where
  minInfoRec (deTimes -> (l, r)) pts =
    addSiblingInTs (minInfoRec l pts) (minInfoRec r pts)
instance (MinInfoNonRec l, MinInfoNonRec r) => MinInfoNonRec (l :*: r) where
  minInfoNonRec (deTimes -> (l, r)) = addMinima1 (minInfoNonRec l) (minInfoNonRec r)



instance MinInfoNonRec Par1 where minInfoNonRec _ = MMap.singleton (1, 0) $ Min 0
instance MinInfoNonRec Par0 where minInfoNonRec _ = MMap.singleton (0, 1) $ Min 0
instance (VRepeat ts, MinInfoNonRec Par1) => MinInfoRec Par1 ts where
  minInfoRec p _ = minima1ToSiblingInT $ minInfoNonRec p
instance (VRepeat ts, MinInfoNonRec Par0) => MinInfoRec Par0 ts where
  minInfoRec p _ = minima1ToSiblingInT $ minInfoNonRec p



deRec0 :: Proxy (Rec0 lbl t) -> Proxy lbl
deRec0 _ = Proxy

instance (IndexInto lbl ts, VRepeat ts) => MinInfoRec (Rec0 lbl t) ts where
  minInfoRec (deRec0 -> plbl) pts =
    MMap.singleton (cvUpd (cvRepeat 0) (indexInto plbl pts) $ \_ -> 1, 0, 0) $ Min 0

deRec1 :: Proxy (Rec1 lbl t r) -> Proxy lbl
deRec1 _ = Proxy

-- TODO: how to support non-regular data types?

-- NB only supports regular data types for now
instance (IndexInto lbl ts, VRepeat ts) => MinInfoRec (Rec1 lbl t Par0) ts where
  minInfoRec (deRec1 -> plbl) pts =
    MMap.singleton (cvUpd (cvRepeat 0) (indexInto plbl pts) $ \_ -> 1, 0, 0) $ Min 0

deRec2 :: Proxy (Rec2 lbl t r s) -> Proxy lbl
deRec2 _ = Proxy

class Regularish r s where
  regularish :: ((r ~ Par1, s ~ Par0) => a) -> ((r ~ Par0, s ~ Par1) => a) -> a
instance Regularish Par1 Par0 where regularish x _ = x
instance Regularish Par0 Par1 where regularish _ y = y
-- NB no other instances!

-- NB only supports regularish data types for now
instance (Regularish r s, IndexInto lbl ts, VRepeat ts) => MinInfoRec (Rec2 lbl t r s) ts where
  minInfoRec (deRec2 -> plbl) pts =
    MMap.singleton (cvUpd (cvRepeat 0) (indexInto plbl pts) $ \_ -> 1, 0, 0) $ Min 0



deDep :: Proxy (Dep t) -> Proxy t
deDep _ = Proxy

instance (VRepeat ts, MinInfoNonRec (Dep t)) => MinInfoRec (Dep t) ts where
  minInfoRec p _ = minima1ToSiblingInT $ minInfoNonRec p

instance MinCtors t => MinInfoNonRec (Dep t) where minInfoNonRec = minCtors . deDep




--------------------
-- usages
instance MinCtors Bool
instance MinCtors ()


instance MinCtors (,)
instance MinCtors a => MinCtors ((,) a)
instance (MinCtors a, MinCtors b) => MinCtors ((,) a b)

instance MinCtors a => MinCtors ((,,) a) -- TODO why does this one work?

instance MinCtors Maybe
instance MinCtors a => MinCtors (Maybe a)

instance MinCtors []
instance MinCtors a => MinCtors [a]

instance MinCtors Either
instance MinCtors a => MinCtors (Either a)
instance (MinCtors a, MinCtors b) => MinCtors (Either a b)



-- T tests support for interesting structures as well as avoiding the recursive
-- branch
data T a = One a | Branch (T a, [T a]) Int

data One_    (p1 :: *) (p0 :: *) = One_ p0
data Branch_ (p1 :: *) (p0 :: *) = Branch_ (T p0, [T p0]) Int

type instance Rep T     = C One_ Par0   :+:   C Branch_ ((((,) :@@: Rec1 'Z T Par0) ([] :@: Rec1 'Z T Par0)) :*: Dep Int)
type instance Rep (T a) = Subst0 T a
type instance DTs T     = RecDT '[] '[]
type instance DTs (T a) = RecDT '[] '[]

instance MinCtors T



-- S tests one interesting way that the final answer depends on the parameter
data S a = OneS a | BranchS Int Int

data OneS_    (p1 :: *) (p0 :: *) = OneS_ p0
data BranchS_ (p1 :: *) (p0 :: *) = BranchS_ Int Int

type instance Rep S     = C OneS_ Par0   :+:   C BranchS_ (Dep Int :*: Dep Int)
type instance Rep (S a) = Subst0 S a
type instance DTs S     = NonRecDT
type instance DTs (S a) = NonRecDT

instance MinCtors S
instance MinCtors a => MinCtors (S a)



-- M1 and M2 exercise the erroneous definition for Recs
data M1 = M1C Int Int Int Int | M1D M2
data M2 = M2C M1

data M1C_ (p1 :: *) (p0 :: *) = M1C_
data M1D_ (p1 :: *) (p0 :: *) = M1D_
data M2C_ (p1 :: *) (p0 :: *) = M2C_

type instance Rep M1 = C M1C_ (Dep Int :*: Dep Int :*: Dep Int :*: Dep Int)
                   :+: C M1D_ (Rec0 ('S 'Z) M2)
type instance Rep M2 = C M2C_ (Rec0 'Z      M1)
type instance DTs M1 = RecDT '[] '[M2]
type instance DTs M2 = RecDT '[M1] '[]

instance MinCtors M1
instance MinCtors M2



data Z_ (p1 :: *) (p0 :: *) = Z_
data S_ (p1 :: *) (p0 :: *) = S_

type instance Rep Nat = C Z_ U   :+:   C S_ (Rec0 Z Nat)
type instance DTs Nat = RecDT '[] '[]

instance MinCtors Nat




data Inf = Inf Inf
data Inf_ (p1 :: *) (p0 :: *) = Inf_ Inf

type instance DTs Inf = RecDT '[] '[]
type instance Rep Inf = C Inf_ (Rec0 Z Inf)

instance MinCtors Inf





instance MinCtors Even
instance MinCtors Odd





pDTs :: Proxy t -> Proxy (DTs t)
pDTs _ = Proxy

gen_minCtors :: MinCtorsWorker t (DTs t) => Proxy t -> Minima1
gen_minCtors p = method p (pDTs p)

class MinCtors t where
  minCtors :: Proxy t -> Minima1
  default minCtors :: MinCtorsWorker t (DTs t) => Proxy t -> Minima1
  minCtors = gen_minCtors

class MinCtorsWorker t dpos where method :: Proxy t -> Proxy dpos -> Minima1

pSiblingDTs :: Proxy t -> Proxy (SiblingDTs t)
pSiblingDTs _ = Proxy

instance MinInfoNonRec (Rep t) => MinCtorsWorker t NonRecDT where method pt _ = minInfoNonRec (pFrom pt)

pIndex :: Proxy (RecDT l r) -> Proxy (Length l)
pIndex _ = Proxy

instance (IndexInto (Length l) (SiblingDTs t),
          VInitialize MinInfo__ (SiblingDTs t),
          VFunctor (SiblingInC (SiblingDTs t)) (SiblingDTs t),
          VRepeat (SiblingDTs t),
          VEnum (SiblingDTs t),
          Eq (CVec (SiblingDTs t) Minima1),
          MinInfoRec (Rep t) (SiblingDTs t)) => MinCtorsWorker t (RecDT l r) where
  method pt pdpos = (`cvAt` indexInto (pIndex pdpos) psibs) $ solve_sibling_set $
                    vInitialize (Proxy :: Proxy MinInfo__) (Proxy :: Proxy SC_SumInfo) minInfo__
    where psibs = pSiblingDTs pt

class    MinInfoRec (Rep t) (SiblingDTs t) => MinInfo__ t
instance MinInfoRec (Rep t) (SiblingDTs t) => MinInfo__ t

minInfo__ :: MinInfo__ t => Proxy t -> SumInfo t
minInfo__ p = minInfoRec (pFrom p) (pSiblingDTs p)





data X a = X a a a a

type instance DTs X     = NonRecDT
type instance DTs (X a) = NonRecDT
type instance Rep X     = Par0 :*: Par0 :*: Par0 :*: Par0
type instance Rep (X a) = Subst0 X a

instance MinCtors X
instance MinCtors a => MinCtors (X a)

data Y a = Y (X (X a))

type instance DTs Y     = NonRecDT
type instance DTs (Y a) = NonRecDT
type instance Rep Y     = X :@: (X :@: Par0)
type instance Rep (Y a) = Subst0 Y a

instance MinCtors Y
instance MinCtors a => MinCtors (Y a)
