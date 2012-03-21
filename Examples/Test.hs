{-# LANGUAGE TypeFamilies, TemplateHaskell #-}

{-# OPTIONS_GHC -ddump-splices #-}

module Test where

import Data.Yoko
import Type.Ord.SpineSerialize (Compare)


data T a = T a

data X = X


concat `fmap` mapM derive [''T, ''X]



test :: (() ~ Compare a b) => a -> b -> ()
test _ _ = ()
