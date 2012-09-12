{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}

{- |

Module      :  LambdaLift.LambdaLift
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

An example lambba lifter using @hcompos@.

-}

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
instance Convert Cnv ULC TLF where convert Cnv = ll



ll :: ULC -> M TLF
ll tm = precise_case tm llLam llVar llLet (Default $ hcompos Cnv)

llLam lams@(Lam_ tyTop tmTop) = do
  -- get the body; count formals; determine captives
  let ((tys, ty), ulc) = peel ([], tyTop) tmTop where
        peel (acc, ty') (Lam ty tm) = peel (ty' : acc, ty) tm
        peel acc tm = (acc, tm)
  let nLocals = 1 + length tys -- NB "1 +" is for ty
  let captives = IS.toAscList $ freeVars $ rejoin lams
      captives' = reverse captives

  (rho, rn) <- ask

  -- generate a top-level function from the body
  do let m = IM.fromDistinctAscList $ zip captives [0..]
     tlf <- ignoreEmissions $
            local (const (ty : tys ++ rho, (nLocals, m))) $ ll ulc
     emit (map (rho !!) $ captives', reverse tys, ty, tlf)

  -- replace lambdas with an invocation of tlf
  sh <- intermediates

  return $ Top sh $ map (lookupRN rn) $ captives'

-- just look up a variables new location (ie now from new closure's environment or parameters)
llVar (Var_ i) = ask >>= \(_, rn) -> return $ Occ $ lookupRN rn i

-- also simultaneously elaborate lets
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

-- note, ill-typed, but the types don't really matter as long as the LL
-- preserves them
ex5 = Lam (TyFun (TyFun TyInt TyInt) (TyFun TyInt TyInt)) (Var 0) @@
      Lam (TyFun TyInt TyInt)
          (Lam TyUnit (Var 1) @@ Var 1)
ex5' = lambdaLift [TyUnit] ex5



instance DeepSeq Type where rnf = (`seq` ())
instance DeepSeq Occ  where
  rnf (Par x) = rnf x
  rnf (Env x) = rnf x
instance DeepSeq Prog where rnf (Prog decs tm) = rnf decs `seq` rnf tm
instance DeepSeq TLF  where rnf = rnf . reps . disband




-- this should evaluate without an exception if things are working; NB doesn't
-- actually test correctness -- currently asking you to do that by
-- investigating the value of each lambda-lifted term
all_exs = rnf [ex0', ex1', ex2', ex3', ex4', ex5']
