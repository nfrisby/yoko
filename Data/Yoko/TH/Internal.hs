module Data.Yoko.TH.Internal where

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
