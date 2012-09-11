{-# LANGUAGE TypeFamilies, TemplateHaskell, UndecidableInstances #-}

{-# OPTIONS_GHC -ddump-splices #-}

module Test where

import Data.Yoko
import Type.Ord.SpineSerialize (Compare)


data T a = T a

data X = X


concat `fmap` mapM yokoTH [''T, ''X, ''Maybe]



test :: (() ~ Compare a b) => a -> b -> ()
test _ _ = ()
