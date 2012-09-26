{-# LANGUAGE TemplateHaskell, TypeFamilies, UndecidableInstances, DataKinds, TypeOperators, MagicHash #-}

module Data.Yoko.MinCtorsTest where

import Data.Yoko
import Data.Yoko.MinCtors
import Data.Yoko.TH (yokoTH)

import qualified Data.List as List

import Language.Haskell.TH.Syntax

import qualified GHC.Types as Types

import Data.Yoko.MinCtors.Prims1 ()





yokoTH ''TyLit
instance MinCtors TyLit

yokoTH ''NameSpace
instance MinCtors NameSpace

yokoTH ''PkgName
instance MinCtors PkgName

yokoTH ''ModName
instance MinCtors ModName

yokoTH_with (yokoDefaults {dcInsts = (List.\\ ['NameU, 'NameL])}) ''NameFlavour
type instance Rep NameU_ = C NameU_ (T0 Dep Int)
instance Generic NameU_ where
  rep = W0  $ \(NameU_ x) -> C (T0 (Types.I# x))
  obj = W'0 $ \(C (T0 (Types.I# x))) -> NameU_ x
type instance Rep NameL_ = C NameL_ (T0 Dep Int)
instance Generic NameL_ where
  rep = W0  $ \(NameL_ x) -> C (T0 (Types.I# x))
  obj = W'0 $ \(C (T0 (Types.I# x))) -> NameL_ x

instance MinCtors NameFlavour

yokoTH ''OccName
instance MinCtors OccName

yokoTH ''Name
instance MinCtors Name

concat `fmap` mapM yokoTH [''Pred, ''TyVarBndr, ''Type]
instance MinCtors Pred
instance MinCtors TyVarBndr
instance MinCtors Type

yokoTH ''RuleBndr
instance MinCtors RuleBndr

yokoTH ''Phases
instance MinCtors Phases

yokoTH ''RuleMatch
instance MinCtors RuleMatch

yokoTH ''Inline
instance MinCtors Inline

yokoTH ''Lit
instance MinCtors Lit

yokoTH ''FamFlavour
instance MinCtors FamFlavour

yokoTH ''Fixity
instance MinCtors Fixity

yokoTH ''FixityDirection
instance MinCtors FixityDirection

yokoTH ''Foreign
instance MinCtors Foreign

yokoTH ''Safety
instance MinCtors Safety

yokoTH ''FunDep
instance MinCtors FunDep

yokoTH ''Callconv
instance MinCtors Callconv

yokoTH ''Con
instance MinCtors Con

yokoTH ''Strict
instance MinCtors Strict

concat `fmap` mapM yokoTH [''Body, ''Clause, ''Dec, ''Exp, ''Guard, ''Match,
                           ''Pat, ''Pragma, ''Range, ''Stmt]
instance MinCtors Body
instance MinCtors Clause
instance MinCtors Dec
instance MinCtors Exp
instance MinCtors Guard
instance MinCtors Match
instance MinCtors Pat
instance MinCtors Pragma
instance MinCtors Range
instance MinCtors Stmt
