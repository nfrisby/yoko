{-# LANGUAGE TypeFamilies, TemplateHaskell, TypeOperators #-}

module LambdaLift.ULC where

import Data.Yoko
import Data.Yoko.TypeBasics (encode, derive)
import LambdaLift.Common



data ULC = Lam Type ULC | Var Int
         | Let [Decl] ULC
         | App ULC ULC deriving Show

data Decl = Decl Type ULC deriving Show


data Lam_ = Lam_ Type ULC
data Var_ = Var_ Int
data Let_ = Let_ [Decl] ULC
data App_ = App_ ULC ULC

data Decl_ = Decl_ Type ULC



type instance Codomain Lam_ = ULC
type instance Codomain Var_ = ULC
type instance Codomain Let_ = ULC
type instance Codomain App_ = ULC

type instance Codomain Decl_ = Decl

type instance Tag Lam_ = $(return $ encode "Lam")
type instance Tag Var_ = $(return $ encode "Var")
type instance Tag Let_ = $(return $ encode "Let")
type instance Tag App_ = $(return $ encode "App")

type instance Tag Decl_ = $(return $ encode "Decl")

concat `fmap` mapM derive [''ULC, ''Decl, ''Lam_, ''Var_, ''Let_, ''App_, ''Decl_]



type instance Rep Lam_ = Dep Type :*: Rec ULC
instance Generic Lam_ where
  rep (Lam_ ty tm) = Dep ty :*: Rec tm
  obj (Dep ty :*: Rec tm) = Lam_ ty tm
type instance Rep Var_ = Dep Int
instance Generic Var_ where
  rep (Var_ i) = Dep i
  obj (Dep i) = Var_ i
type instance Rep Let_ = Par1 [] (Rec Decl) :*: Rec ULC
instance Generic Let_ where
  rep (Let_ ds tm) = Par1 (map Rec ds) :*: Rec tm
  obj (Par1 ds :*: Rec tm) = Let_ (fmap unRec ds) tm
type instance Rep App_ = Rec ULC :*: Rec ULC
instance Generic App_ where
  rep (App_ tm1 tm2) = Rec tm1 :*: Rec tm2
  obj (Rec tm1 :*: Rec tm2) = App_ tm1 tm2

type instance Rep Decl_ = Dep Type :*: Rec ULC
instance Generic Decl_ where
  rep (Decl_ ty tm) = Dep ty :*: Rec tm
  obj (Dep ty :*: Rec tm) = Decl_ ty tm



type instance DCs ULC =
  (N Lam_ :+: N Var_) :+: (N Let_ :+: N App_)
instance DT ULC where
  disband (Lam ty tm)   = {-DCsOf . -}inject $ Lam_ ty tm
  disband (Var i)       = {-DCsOf . -}inject $ Var_ i
  disband (Let ds tm)   = {-DCsOf . -}inject $ Let_ ds tm
  disband (App tm1 tm2) = {-DCsOf . -}inject $ App_ tm1 tm2
instance DC Lam_ where rejoin (Lam_ ty tm)   = Lam ty tm
instance DC Var_ where rejoin (Var_ i)       = Var i
instance DC Let_ where rejoin (Let_ ds tm)   = Let ds tm
instance DC App_ where rejoin (App_ tm1 tm2) = App tm1 tm2

type instance DCs Decl = N Decl_
instance DT Decl where
  disband (Decl ty tm) = {-DCsOf . -}N $ Decl_ ty tm
instance DC Decl_ where rejoin (Decl_ ty tm) = Decl ty tm
