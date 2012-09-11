{-# LANGUAGE TypeFamilies, TemplateHaskell, TypeOperators #-}

{- |

Module      :  LambdaLift.TLF
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

An example lambba lifter using @hcompos@.

-}

module LambdaLift.TLF where

import Data.Yoko.TypeBasics (encode, derive)
import Data.Yoko

import LambdaLift.Common


data Occ = Par Int | Env Int
instance Show Occ where
  show (Par i) = show i
  show (Env i) = '^' : show i

data TLF = Top Int [Occ] | Occ Occ
         | App TLF TLF deriving Show

type FunDec = ([Type], [Type], Type, TLF)
data Prog = Prog [FunDec] TLF deriving Show





data Top_ = Top_ Int [Occ]
data Occ_ = Occ_ Occ
data App_  = App_ TLF TLF



type instance Codomain Top_ = TLF
type instance Codomain Occ_  = TLF
type instance Codomain App_  = TLF

type instance Tag Top_ = $(return $ encode "Top")
type instance Tag Occ_ = $(return $ encode "Occ")
type instance Tag App_  = $(return $ encode "App")

concat `fmap` mapM derive [''TLF, ''Top_, ''Occ_, ''App_]



type instance Rep Top_ = Dep Int :*: Dep [Occ]
instance Generic Top_ where
  rep (Top_ i os) = Dep i :*: Dep os
  obj (Dep i :*: Dep os) = Top_ i os
type instance Rep Occ_ = Dep Occ
instance Generic Occ_ where
  rep (Occ_ o) = Dep o
  obj (Dep o) = Occ_ o
type instance Rep App_ = Rec TLF :*: Rec TLF
instance Generic App_ where
  rep (App_ tm1 tm2) = Rec tm1 :*: Rec tm2
  obj (Rec tm1 :*: Rec tm2) = App_ tm1 tm2



type instance DCs TLF = (N Top_ :+: N Occ_) :+: N App_
instance DT TLF where
  disband (Top i os )   = {-DCsOf . -}inject $ Top_ i os
  disband (Occ o)       = {-DCsOf . -}inject $ Occ_ o
  disband (App tm1 tm2) = {-DCsOf . -}inject $ App_ tm1 tm2
instance DC Top_ where rejoin (Top_ i os)    = Top i os
instance DC Occ_ where rejoin (Occ_  o)      = Occ o
instance DC App_ where rejoin (App_ tm1 tm2) = App tm1 tm2
