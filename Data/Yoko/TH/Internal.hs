{-# LANGUAGE ViewPatterns #-}

module Data.Yoko.TH.Internal where

import Data.Maybe (fromMaybe)
import Control.Monad (mplus)

import Language.Haskell.TH



thFail :: String -> Q a
thFail s = fail $ "yokoTH: " ++ s



data DataType = DataType [TyVarBndr] (Either Con [Con])



dataType :: Name -> Q DataType
dataType n = do
  i <- reify n
  case i of
    TyConI d -> case d of
      DataD _ _ tvbs cons _   -> return $ DataType tvbs $ Right cons
      NewtypeD _ _ tvbs con _ -> return $ DataType tvbs $ Left con
      _ -> thFail $ "expecting name of newtype or data type, not: " ++ show d
    _ -> thFail $ "expecting name of newtype or data type, not: " ++ show i

dataType2Dec :: Name -> DataType -> Dec
dataType2Dec n (DataType tvbs cons) = case cons of
  Left  con  -> NewtypeD [] n tvbs con  []
  Right cons -> DataD    [] n tvbs cons []




tvbName :: TyVarBndr -> Name
tvbName (PlainTV n) = n
tvbName (KindedTV n _) = n



peelApp :: Type -> (Type, [Type])
peelApp = peelAppAcc []

peelAppAcc :: [Type] -> Type -> (Type, [Type])
peelAppAcc acc (AppT ty0 ty1) = peelAppAcc (ty1 : acc) ty0
peelAppAcc acc ty             = (ty, acc)



expandSyn :: Type -> [Type] -> Q (Maybe (Type, [Type]))
expandSyn (ConT n) tys = do
  i <- reify n
  case i of
    TyConI (TySynD _ (map tvbName -> formals) rhs) ->
      -- formals <= tys because type synonyms must be fully applied.
      -- peelAppAcc handles both formals < tys and formals == tys.
      let tytys = peelAppAcc (drop (length formals) tys) $
                  msubst (zip formals tys) rhs
      in (`mplus` Just tytys) `fmap` uncurry expandSyn tytys
    _ -> return Nothing
expandSyn _ _ = return Nothing



msubst :: [(Name, Type)] -> Type -> Type
msubst sigma = w where
  w ty@(VarT n) = fromMaybe ty $ lookup n sigma
  w (ForallT tvbs cxt ty) =
    ForallT tvbs cxt $ msubst (filter p sigma) ty
    where p = (`elem` map tvbName tvbs) . fst
  w (AppT ty1 ty2) = AppT (w ty1) (w ty2)
  w (SigT ty k) = SigT (w ty) k
  w ty = ty
