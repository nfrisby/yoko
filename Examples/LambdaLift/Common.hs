{-# LANGUAGE TemplateHaskell, DataKinds, TypeFamilies #-}

{- |

Module      :  LambdaLift.Common
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

An example lambba lifter using @hcompos@.

-}

module LambdaLift.Common where

import Data.Yoko



data Type = TyUnit | TyInt | TyFun Type Type deriving Show

yokoTH ''Type
