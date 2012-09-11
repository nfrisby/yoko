{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}

module LambdaLift.LambdaLift where

import LambdaLift.Common
import LambdaLift.ULC as A
import LambdaLift.TLF

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Data.Yoko
import Data.Yoko.HCompos

import LambdaLift.LLBasics
import LambdaLift.FreeVars (freeVars)
import LambdaLift.DeepSeq (DeepSeq(..))





lambdaLift :: [Type] -> ULC -> Prog
lambdaLift e x = Prog ds tm where
  (tm, ds) = runM (ll x) (e, (length e, IM.empty), 0)



data Cnv = Cnv
type instance Idiom Cnv = M
instance HCompos Cnv ULC TLF where hcompos Cnv = ll



ll :: ULC -> M TLF
ll tm = precise_case (hcompos Cnv) tm $ llLam .|| llVar .|. llLet

llLam lams@(Lam_ tyTop tmTop) = do
  -- get the body; count formals; determine captives
  let ((tys, ty), ulc) = peel ([], tyTop) tmTop where
        peel (acc, ty') (Lam ty tm) = peel (ty' : acc, ty) tm
        peel acc tm = (acc, tm)
  let nLocals = 1 + length tys -- NB "1 +" is for ty
  let captives = freeVars $ rejoin lams
      captives' = IS.toAscList captives
      captives'' = reverse captives'

  (rho, rn) <- ask

  -- generate a top-level function from the body
  do let m = IM.fromDistinctAscList $ zip captives' [0..]
     tlf <- ignoreEmissions $
            local (const (ty : tys ++ rho, (nLocals, m))) $ ll ulc
     emit (map (rho !!) captives'', reverse tys, ty, tlf)

  -- replace lambdas with an invocation of tlf
  sh <- intermediates

  return $ Top (sh - 1) $ map (lookupRN rn) $ captives''
llVar (Var_ i) = ask >>= \(_, rn) -> return $ Occ $ lookupRN rn i
llLet (Let_ ds tm) = ll $ foldr (\(Decl ty tm) x -> A.App (Lam ty tm) x) tm ds





infixl 1 @@
(@@) = A.App

s_comb a b c = Lam (TyFun a (TyFun b c)) . Lam (TyFun a b) . Lam a $
               Var 2 @@ Var 0 @@ (Var 1 @@ Var 0)

ex0 = Lam TyInt (Var 0)
ex0' = lambdaLift [] ex0

ex1 = s_comb TyInt TyInt TyInt @@ (Lam TyInt $ Lam TyInt (Var 0))
                               @@ Lam TyUnit (Var 2 @@ Var 1)
ex1' = lambdaLift [TyInt, TyFun TyInt TyInt] ex1

ex2 = Lam (TyFun (TyFun TyInt TyInt) TyUnit) $
      Lam (TyFun TyInt TyInt)
            (Var 1 @@ Lam TyInt (Var 1 @@ Var 0))
ex2' = lambdaLift [] ex2

ex3 = Lam TyUnit . Lam TyUnit . Lam TyUnit .
      (Var 1 @@) . Lam TyUnit .
       (Var 3 @@) . Lam TyInt $
        Var 1
ex3' = lambdaLift [] ex3

ex4 = Lam (TyFun TyInt TyInt) (Var 0) @@ Lam TyInt (Var 0)
ex4' = lambdaLift [] ex4

ex5 = Lam (TyFun (TyFun TyInt TyInt) (TyFun TyInt TyInt)) (Var 0) @@
      Lam (TyFun TyInt TyInt)
          (Lam TyUnit (Var 1) @@ Var 1)
ex5' = lambdaLift [TyUnit] ex5

-- TODO can I make the Tops use scoped instead of global indices?

{-
ex0' ==
Prog [([],[],TyInt,Var 0)
     ] (Top 0 [])

ex1' ==
Prog [([],[TyFun TyInt (TyFun TyInt TyInt),TyFun TyInt TyInt],TyInt,
         App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))),
      ([],[TyInt],TyInt,Var 0),
      ([TyFun TyInt TyInt,TyInt],[],TyUnit,App (Var ^1) (Var ^0))
     ] (App (App (Top 0 []) (Top 1 [])) (Top 2 [1,0]))

ex2' ==
Prog [([TyFun TyInt TyInt],[],TyInt,App (Var ^0) (Var 0)),
      ([],[TyFun (TyFun TyInt TyInt) TyUnit],TyFun TyInt TyInt,
         App (Var 1) (Top 0 [0]))
     ] (Top 1 [])

ex3' ==
Prog [([TyUnit],[],TyInt,Var ^0),
      ([TyUnit],[],TyUnit,App (Var ^0) (Top 0 [0])),
      ([],[TyUnit,TyUnit],TyUnit,App (Var 1) (Top 1 [2]))
     ] (Top 2 [])

ex4' ==
Prog [([],[],TyFun TyInt TyInt,Var 0),
      ([],[],TyInt,Var 0)
     ] (App (Top 0 []) (Top 1 []))

ex5' ==
Prog [([],[],TyFun (TyFun TyInt TyInt) (TyFun TyInt TyInt),Var 0),
      ([TyFun TyInt TyInt],[],TyUnit,Var ^0),
      ([TyUnit],[],TyFun TyInt TyInt,App (Top 1 [0]) (Var ^0))
     ] (App (Top 0 []) (Top 2 [0]))

-}

instance DeepSeq Type where rnf = (`seq` ())
instance DeepSeq Occ  where
  rnf (Par x) = rnf x
  rnf (Env x) = rnf x
instance DeepSeq Prog where rnf (Prog decs tm) = rnf decs `seq` rnf tm
instance DeepSeq TLF  where rnf = rnf . reps . disband

all_exs = rnf [ex0', ex1', ex2', ex3', ex4', ex5']
