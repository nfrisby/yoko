module LambdaLift.Common where

data Type = TyUnit | TyInt | TyFun Type Type deriving Show
