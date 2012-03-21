{-# LANGUAGE TypeOperators, ViewPatterns, TemplateHaskell, PatternGuards #-}

{- |

Module      :  Data.Yoko.TH
Copyright   :  (c) The University of Kansas 2011
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

This bundled Template Haskell derives all fields types and @yoko@ instances for
users' data types.

'yokoTH' is the prinicpal deriver, but it can be customized via 'yokoTH_with',
which lets the user specify how to represent composite fields that include
applications of type with higher-kinds than @*->*@.

For instance, @yokoTH@ cannot handle @data T = C0 | C1 [(Int, T T)]@.

The following invocation of @yokoTH_with@ does. @Par2@ is declared in
"Data.Yoko.Representation", but @Bifunctor@ is not.

@
class Bifunctor f where
  bifmap :: (a -> c) -> (b -> d) -> f a b -> f c d

instance Bifunctor ((,,) a) where
  bifmap f g ~(a, x, y) = (a, f x, g y)

yokoTH_with (yokoDefaults {mappings = ((2, Mapping ''Par2 'Par2 'bifmap) :)}) ''T
@

As always, use @{- OPTIONS_GHC -ddump-splices -}@ to inspect the generated
code.

-}

module Data.Yoko.TH
  (-- * Derivers
   yokoTH, yokoTH_with,
   -- * Options
   YokoOptions(..), Mapping(..), yokoDefaults
  ) where

import Type.Spine.Stage0 (Spine, spineType_, kTypeG)
import Type.Serialize (serializeTypeAsHash_)
import qualified Type.Ord as Ord

import Data.Yoko.TypeBasics (encode)
import Data.Yoko.Representation
import Data.Yoko.View

import Language.Haskell.TH as TH hiding (Range)
import Language.Haskell.TH.Syntax as TH hiding (Range)
import qualified Language.Haskell.TH.SCCs as SCCs

import qualified Data.Yoko.TH.Internal as Int

import qualified Control.Monad.Writer as Writer
import qualified Control.Monad.Trans as Trans

import qualified Control.Arrow as Arrow

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List

import Data.Kind (KindStar(..))
import Data.TypeFun
import Data.Record hiding (convert, Name)
import qualified Data.Record as R
import qualified Data.Record.Combinators as R
import Data.Record.Combinators ((!!!))





convert r = R.convert $ R.withStyle r (Id KindStar)

data Target = Target deriving Show
data Renamer = Renamer deriving Show
data Mappings = Mappings deriving Show
data BindingGroup = BindingGroup deriving Show
data TargetData = TargetData deriving Show
data TargetType = TargetType deriving Show
data TargetKind = TargetKind deriving Show
instance R.Name Target where name = Target
instance R.Name Renamer where name = Renamer
instance R.Name Mappings where name = Mappings
instance R.Name BindingGroup where name = BindingGroup
instance R.Name TargetData where name = TargetData
instance R.Name TargetType where name = TargetType
instance R.Name TargetKind where name = TargetKind



-- | A 'Mapping' identifies the representation type, its constructor, and the
-- associated mapping function. For example, 'Par1' is represented with
-- @Mapping ''Par1 'Par1 'fmap@.
data Mapping = Mapping
  {containerTypeName :: Name, containerCtor :: Name,
   methodName :: Name}

-- | The default @yoko@ derivations can be customised.
data YokoOptions = YokoOptions
  { -- | How fields type names are derived from constructor names. Defaults to
    -- @(++ \"_\")@.
   renamer :: (String -> String) -> (String -> String),
    -- | How applications of higher-rank data types are represented. Defaults
    -- to @[(1, 'Mapping' ''Par1 'Par1 'fmap)]@.
   mappings :: [(Int, Mapping)] -> [(Int, Mapping)]}

-- | The default options. @yokoDefaults = YokoOptions id id@.
yokoDefaults :: YokoOptions
yokoDefaults = YokoOptions id id

type M r = Writer.WriterT [Dec] Q

liftQ :: Q a -> M r a
liftQ = Trans.lift

runM :: M r () -> Q [Dec]
runM = fmap snd . Writer.runWriterT

generate :: [Dec] -> M r ()
generate = Writer.tell



-- | Derive fields types and all @yoko@ instances for a given data type.
yokoTH :: Name -> Q [Dec]
yokoTH n = yokoTH_with yokoDefaults n

-- | Customized derivation.
yokoTH_with :: YokoOptions -> Name -> Q [Dec]
yokoTH_with options n = runM $ yoko0 $ X :&
  Target := n :& Renamer := (mkName . renamer options (++ "_") . TH.nameBase)
         :& Mappings := mappings options [(1, Mapping ''Par1 'Par1 'fmap)]




-- gather reflective information about the target type
yoko0 r@(convert -> X :& Target := n) = do
  names <- liftQ $ SCCs.binding_group n
  datatype@(Int.DataType tvbs _) <- liftQ $ Int.dataType n

  let ty = applyConT2TVBs n tvbs

  -- get the kind of the target type; each fields type has the same kind
  cxt <- flip mapM tvbs $ \tvb -> liftQ $
    EqualP (ConT ''Ord.EQ) `fmap` do
      let tv = [t| Spine ($(kTypeG (tvbKind tvb)) $(return $ tvbType tvb)) |]
      [t| Ord.Compare $tv $tv |]

  yoko1 $ r :&
    BindingGroup := names :&
    TargetData := datatype :&
    TargetType := ty :&
    TargetKind := (map tvbKind tvbs, cxt)

-- generate fields types
conName :: Con -> Name
conName (NormalC n _) = n
conName (RecC n _) = n
conName (InfixC _ n _) = n
conName (ForallC _ _ c) = conName c

renameCon :: (Name -> Name) -> Con -> Con
renameCon f (NormalC n fields) = NormalC (f n) fields
renameCon f (RecC n fields) = RecC (f n) fields
renameCon f (InfixC fieldL n fieldR) = InfixC fieldL (f n) fieldR
renameCon f (ForallC tvbs cxt c) = ForallC tvbs cxt $ renameCon f c

tvbName :: TyVarBndr -> Name
tvbName (PlainTV n) = n
tvbName (KindedTV n _) = n

tvbKind :: TyVarBndr -> Kind
tvbKind (PlainTV _) = StarK
tvbKind (KindedTV _ k) = k

tvbType :: TyVarBndr -> Type
tvbType = VarT . tvbName

applyConT2TVBs :: Name -> [TyVarBndr] -> Type
applyConT2TVBs n tvbs = foldl ((. tvbType) . AppT) (ConT n) tvbs

conFields :: Con -> Q [StrictType]
conFields (NormalC _ fds)    = return fds
conFields (RecC _ fds)       = return $ map (\(_, x, y) -> (x, y)) fds
conFields (InfixC fdl _ fdr) = return [fdl, fdr]
conFields ForallC{}          = Int.thFail "no support for existential types."

pat_exp :: Name -> Name -> Int -> (Pat, Exp)
pat_exp np ne k = (ConP np $ map VarP ns,
                   foldl ((. VarE) . AppE) (ConE ne) ns) where
  ns = [ mkName $ "x" ++ show i | i <- [0..k - 1] ]

simpleClause pats exp = Clause pats (NormalB exp) []

halves :: [a] -> b -> (b -> b -> b) -> (a -> b) -> b
halves as nil app each = w (length as) as where
  w _ []  = nil
  w _ [a] = each a
  w k as  = w lk l `app` w rk r
    where lk = k `div` 2   ;   rk = k - lk
          (l, r) = List.splitAt lk as

peelApp :: Type -> (Type, [Type])
peelApp = peelAppAcc []

peelAppAcc acc (AppT ty0 ty1) = peelAppAcc (ty1 : acc) ty0
peelAppAcc acc ty             = (ty, acc)

data FieldRO = FieldRO {repF :: Exp, objF :: Exp}

fieldRO :: [(Int, Mapping)] -> Set Name -> Type -> Q (Type, FieldRO)
fieldRO maps bg = w' where
  w' = uncurry w . peelApp

  isRec n = Set.member n bg

  simple b ty tys = return $ (ConT tyn `AppT` foldl AppT ty tys,
    if b then FieldRO (ConE 'Rec) (VarE 'unRec)
         else FieldRO (ConE 'Dep) (VarE 'unDep))
    where tyn = if b then ''Rec else ''Dep

  w ty tys = case ty of
    AppT{}              -> Int.thFail $ "impossible: AppT is guarded by peelApp."
    SigT ty _           -> uncurry w $ peelAppAcc tys ty
    ForallT{}           -> Int.thFail $ "no support for ForallT."
    ConT n
      | isRec n -> if not (null recs) then Int.thFail "does not support nested recursion."
                   else simple True ty tys
    _ 
      | not (null recs) -> case lookup (length recs) maps of
        Nothing -> Int.thFail $ "no case in the given YokoOptions for type constructors with " ++ show (length recs) ++ " arguments."
        Just (Mapping {containerTypeName = tyn, containerCtor = ctor,
                       methodName = mn}) -> do
          recs <- mapM w' recs
          let snoc (tyL, fROL) (tyR, fROR) =
                (tyL `AppT` tyR, fROL `appRO` fROR)
              appRO l r = FieldRO {repF = repF l `AppE` repF r,
                                   objF = objF l `AppE` objF r}
              post fRO = FieldRO {repF = ConE ctor `compose` repF fRO,
                                  objF = objF fRO `compose` dtor}
          return $ Arrow.second post $ foldl snoc
            (ConT tyn `AppT` container,
             FieldRO {repF = VarE mn, objF = VarE mn}) recs
          where dtor = LamE [ConP ctor [VarP x]] (VarE x)
                  where x = mkName "x"
      | otherwise -> simple False ty tys
    where (foldl AppT ty -> container, recs) =
            List.break (any isRec . Set.toList . SCCs.type_dependencies) tys

data ConRO = ConRO {repP :: [Pat], repE :: Exp, objP :: Pat, objE :: [Exp]}

yoko1 r@(convert -> X :&
  Renamer := rn :&
  Mappings := maps :&
  BindingGroup := bg :&
  TargetData := Int.DataType tvbs cons :&
  TargetType := ty :&
  TargetKind := (ks, cxt)
        ) = do
  loc <- liftQ TH.location

  -- make a name into a NameG for a type in the current module; NB the fields
  -- types need not be declared in the same module as the target type
  let mkG n = Name (mkOccName $ nameBase n) $
              NameG TcClsName (mkPkgName $ loc_package loc)
                      (mkModName $ loc_module loc)

  liftQ (sequence [do
    let n = conName con
        n' = rn n
        fd = applyConT2TVBs n' tvbs

    fields <- conFields con

    -- declare the fields type and its Range/Tag/DC instances
    let yokoD = 
          [Int.dataType2Dec n' (Int.DataType tvbs (Right [renameCon rn con])),
           TySynInstD ''Range [fd] ty,
           TySynInstD ''Tag   [fd] $ encode $ TH.nameBase n,
           InstanceD cxt (ConT ''DC `AppT` fd)
             [let (pat, exp) = pat_exp n' n $ length fields
              in FunD 'rejoin [simpleClause [pat] exp]]
          ]

    -- declare the Rep and Generic instances
    (repTy, (conRO, _)) <- Arrow.second ($ 0) `fmap` halves fields
          (return (ConT ''U, \s ->
                   (ConRO {repP = [], repE = ConE 'U,
                           objP = WildP, objE = []}, s)))
          (\l r -> l >>= \(tyL, roL) -> r >>= \(tyR, roR) -> return $
            (ConT ''(:*:) `AppT` tyL `AppT` tyR,
             \s -> case roL s of
               (roL, s) -> case roR s of
                 (roR, s) ->
                   (ConRO {repP = repP roL ++ repP roR,
                           repE = ConE '(:*:) `AppE` repE roL `AppE` repE roR,
                           objP = ConP '(:*:) [objP roL, objP roR],
                           objE = objE roL ++ objE roR}, s)))
          (\(_, ty) ->
             let post fRO s =
                   (ConRO {repP = [VarP n], repE = repF fRO `AppE` VarE n,
                           objP = VarP n, objE = [objF fRO `AppE` VarE n]},
                    s + 1)
                   where n = mkName $ "x" ++ show s
             in Arrow.second post `fmap` fieldRO maps bg ty)

    let genD = [TySynInstD ''Rep [fd] repTy,
                InstanceD cxt (ConT ''Generic `AppT` fd)
                 [FunD 'rep [simpleClause [ConP n' (repP conRO)] $ repE conRO],
                  FunD 'obj [simpleClause [objP conRO] $
                               foldl AppE (ConE n') $ objE conRO]]]

    -- integrate with type-spine and type-cereal
    spineD <- spineType_ (mkG n') ks StarK
    cerealD <- serializeTypeAsHash_ (mkG n') ks StarK

    return $ yokoD ++ spineD ++ cerealD ++ genD
       | con <- either (:[]) id cons ]) >>= generate . concat

  yoko2 r

-- generate DCs/DT instances
compose l r = VarE '(.) `AppE` l `AppE` r

postConE :: Name -> Exp -> Exp
postConE n inj = compose (ConE n) inj

yoko2 r@(convert -> X :&
  Renamer := rn :&
  TargetData := Int.DataType tvbs cons :&
  TargetType := ty :&
  TargetKind := (_, cxt)
        ) = do
  (dcs, cases) <- liftQ $ halves (either (:[]) id cons)
    (Int.thFail $ "`" ++ show (r !!! Target :: Name) ++ "' must have constructors.")
    (\l r -> do
      (l, ls) <- l; (r, rs) <- r
      return $
        (ConT ''(:+:) `AppT` l `AppT` r,
         map (Arrow.first (postConE 'L)) ls ++
         map (Arrow.first (postConE 'R)) rs))
    (\con -> do
       fields <- length `fmap` conFields con
       return $ let n = conName con
                in (ConT ''N `AppT` applyConT2TVBs (rn n) tvbs,
                    [(ConE 'N, (n, fields))]))

  cases <- return $ flip map cases $ \(inj, (n, fds)) ->
    let (pat, exp) = pat_exp n (rn n) fds
    in simpleClause [pat] $ postConE 'DCsOf inj `AppE` exp
  generate $ [TySynInstD ''DCs [ty] dcs,
              InstanceD cxt (ConT ''DT `AppT` ty) [FunD 'disband cases]]
