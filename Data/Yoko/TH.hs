{-# LANGUAGE TypeOperators, ViewPatterns, TemplateHaskell, PatternGuards,
  DataKinds, LambdaCase #-}

{- |

Module      :  Data.Yoko.TH
Copyright   :  (c) The University of Kansas 2012
License     :  BSD3

Maintainer  :  nicolas.frisby@gmail.com
Stability   :  experimental
Portability :  see LANGUAGE pragmas (... GHC)

This bundled Template Haskell derives all fields types and @yoko@ instances for
users' data types.

'yokoTH' is the principal deriver, but it can be customized in two ways via
'yokoTH_with'. First, the user can specify how to derive the names of fields
types from the original constructor name -- the default is @(++ \"_\")@.
Second, the user can specify how to represent composite fields that include
applications of types with higher-kinds. This is done by providing a 'Mapping'.

Each 'Mapping' specifies a representation type, its constructor, and a
structure-preserving mapping function. The default options handle applications
of @*->*@ and @*->*->*@ types with the 'T1' and 'T2' types from
"Data.Yoko.Representation" and uses the 'invmap' and 'invmap2' mapping
functions from the @invariant@ package.

For example, @yokoTH@ cannot handle @data T = C0 | C1 (T, T, T)@, since '(,,)'
is applied at kind @*->*->*@. It can, however handle @data U = C0 | C1 (Int, U,
U)@, since @(,,) Int@ is applied at kind @*->*->*@ -- the kind of the
application is determined by the leftmost argument with a recursive
occurrence. In this case, @yokoTH@ uses the default @Mapping ''T2 'T2
'invmap2@.

The following invocation of @yokoTH_with@ can handle @T@, since it provides an
additional mapping to be used with 3-argument applications.

@
class Invariant3 f where
  invmap3 :: (a -> x) -> (x -> a) ->
             (b -> y) -> (y -> b) ->
             (c -> z) -> (z -> c) ->
             f a b c -> f x y z

instance Invariant3 (,,) where
  invmap3 f _ g _ h _ ~(x, y, z) = (f x, g y, h z)

newtype Par3 f a b c = Par3 (f a b c)

yokoTH_with (yokoDefaults {mappings = ((3, Mapping ''Par3 'Par3 'invmap3) :)}) ''T
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

import Type.Spine (Spine, spineType_d_)
import Type.Serialize (serializeTypeAsHash_data)
import qualified Type.Ord as Ord

import Data.Yoko.TypeBasics (encode, Nat(..))
import Data.Yoko.Representation
import Data.Yoko.View

import Data.Yoko.Invariant

import Language.Haskell.TH as TH hiding (Codomain)
import Language.Haskell.TH.Syntax as TH hiding (Codomain)
import qualified Language.Haskell.TH.SCCs as SCCs

import qualified Data.Yoko.TH.Internal as Int
import Data.Yoko.TH.Internal (tvbName, peelApp, peelAppAcc, expandSyn)

import qualified Control.Monad.Writer as Writer
import qualified Control.Monad.Trans as Trans
import Control.Monad (liftM, when, foldM)

import qualified Control.Arrow as Arrow

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

import Data.Maybe (catMaybes)

import Data.Kind (KindStar(..))
import Data.TypeFun
import Data.Record hiding (convert, Name)
import qualified Data.Record as R
import qualified Data.Record.Combinators as R
import Data.Record.Combinators ((!!!))





convert r = R.convert $ R.withStyle r (Id KindStar)

data Target   = Target   deriving Show
data Renamer  = Renamer  deriving Show
data Mappings = Mappings deriving Show
data InvInsts = InvInsts deriving Show
data DCInsts = DCInsts deriving Show
data BindingGroup = BindingGroup deriving Show
data TargetData   = TargetData   deriving Show
data TargetType   = TargetType   deriving Show
data TargetCxt    = TargetCxt    deriving Show
data TargetTVBs   = TargetTVBs   deriving Show
data TargetPars   = TargetPars   deriving Show
data ConName      = ConName      deriving Show
data ConFields    = ConFields    deriving Show
instance R.Name Target   where name = Target
instance R.Name Renamer  where name = Renamer
instance R.Name Mappings where name = Mappings
instance R.Name InvInsts where name = InvInsts
instance R.Name DCInsts  where name = DCInsts
instance R.Name BindingGroup where name = BindingGroup
instance R.Name TargetData   where name = TargetData
instance R.Name TargetType   where name = TargetType
instance R.Name TargetCxt    where name = TargetCxt
instance R.Name TargetTVBs   where name = TargetTVBs
instance R.Name TargetPars   where name = TargetPars
instance R.Name ConName      where name = ConName
instance R.Name ConFields    where name = ConFields



-- | A 'Mapping' identifies the representation type, its constructor, and the
-- associated mapping function. For example, 'T1' is represented with @Mapping
-- ''T1 'T1 'invmap@.
data Mapping = Mapping
  {containerTypeName :: Name, containerCtor :: Name, methodName :: Name}

-- | The default @yoko@ derivations can be customised.
data YokoOptions = YokoOptions
  { -- | How fields type names are derived from constructor names. Defaults to
    -- @(++ \"_\")@.
   renamer :: (String -> String) -> (String -> String),
    -- | How applications of higher-rank data types are represented. Defaults
    -- to @[(1, 'Mapping' ''T1 'T1 'invmap), (2, 'Mapping' ''T2 'T2
    -- 'invmap2)]@.
   mappings :: [(Int, Mapping)] -> [(Int, Mapping)],
    -- | Should instances of 'Invariant' also be automatically derived for this
    -- type? Defaults to @True@.
   invInsts :: Bool -> Bool,
    -- | For which constructors should instances of 'Rep' and 'Generic' be
    -- automatically derived? Defaults to the set of all constructors.
   dcInsts :: [Name] -> [Name]}

-- | The default options. @yokoDefaults = YokoOptions id id id@.
yokoDefaults :: YokoOptions
yokoDefaults = YokoOptions id id id id

type M r = Writer.WriterT [Dec] Q

liftQ :: Q a -> M r a
liftQ = Trans.lift

runM :: M r () -> Q [Dec]
runM = fmap snd . Writer.runWriterT

generate :: [Dec] -> M r ()
generate = Writer.tell



concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f



-- | Derive fields types and all @yoko@ instances for a given data type.
yokoTH :: Name -> Q [Dec]
yokoTH n = yokoTH_with yokoDefaults n

-- | Customized derivation.
yokoTH_with :: YokoOptions -> Name -> Q [Dec]
yokoTH_with options n = runM $ yoko0 $ X :&
  Target := n :& Renamer := (mkName . renamer options (++ "_") . TH.nameBase)
         :& Mappings := mappings options [(1, Mapping ''T1 'T1 'invmap),
                                          (2, Mapping ''T2 'T2 'invmap2)]
         :& InvInsts := invInsts options True
         :& DCInsts := dcInsts options




-- gather reflective information about the target type
yoko0 r@(convert -> X :& Target := n) = do
  datatype <- liftQ $ Int.dataType n

  scc      <- do
    scc <- liftQ $ SCCs.scc n
    case scc of
      Left n   -> return $ Left n
      Right ns -> fmap (Right . fst) $ foldM snoc (Map.empty, 0) $ Set.toAscList ns
        where snoc (m, acc) n = liftQ (reify n) >>= return . \case
                TyConI TySynD{} -> (Map.insert n Nothing    m, acc)
                _               -> (Map.insert n (Just acc) m, acc + 1)

  yoko1 $ r :& TargetData := datatype :& BindingGroup := scc

-- generate fields types
conName :: Con -> Name
conName (NormalC  n _)  = n
conName (RecC     n _)  = n
conName (InfixC _ n _)  = n
conName (ForallC _ _ c) = conName c

renameCon :: (Name -> Name) -> Con -> Con
renameCon f (NormalC n fields) = NormalC (f n) fields
renameCon f (RecC n fields) = RecC (f n) fields
renameCon f (InfixC fieldL n fieldR) = InfixC fieldL (f n) fieldR
renameCon f (ForallC tvbs cxt c) = ForallC tvbs cxt $ renameCon f c

tvbKind :: TyVarBndr -> Kind
tvbKind (PlainTV _) = StarT
tvbKind (KindedTV _ k) = k

tvbType :: TyVarBndr -> Type
tvbType = VarT . tvbName

compose :: Exp -> Exp -> Exp
compose l r = VarE '(.) `AppE` l `AppE` r

postConE :: Name -> Exp -> Exp
postConE n inj = compose (ConE n) inj

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
halves as nil appnd single = w (length as) as where
  w _ []  = nil
  w _ [a] = single a
  w k as  = w lk l `appnd` w rk r
    where lk = k `div` 2   ;   rk = k - lk
          (l, r) = List.splitAt lk as

toNat 0 = PromotedT 'Z
toNat n = PromotedT 'S `AppT` toNat (n - 1)

data FieldRO = FieldRO {repF :: Exp, objF :: Exp}

namesIn :: Type -> Set Name
namesIn (ForallT tvbs _ ty) = namesIn ty `Set.difference` Set.fromList (map tvbName tvbs)
namesIn (AppT ty1 ty2) = namesIn ty1 `Set.union` namesIn ty2
namesIn (SigT ty _) = namesIn ty
namesIn (VarT n) = Set.singleton n
namesIn (ConT n) = Set.singleton n
namesIn _ = Set.empty

fieldRO :: [(Int, Mapping)] -> Either Name (Map Name (Maybe Int)) ->
           [Name] -> -- just the represented parameters (ie Par1 and Par0)
           Type -> Q (Type, FieldRO)
fieldRO maps bg parNs = w' where
  w' = uncurry w . peelApp

  isRec = case bg of
    Left _   -> const False
    Right bg -> \n -> Map.member n bg
  isPar n = n `elem` parNs
  isImportant n = isRec n || isPar n

  (nRecTy, nRecCtor) = case length parNs of
    0 -> (''T0, 'T0)
    1 -> (''T1, 'T1)
    2 -> (''T2, 'T2)

  w ty tys = case ty of
    PromotedT{}      -> Int.thFail $ "no support for promoted types."
    PromotedTupleT{} -> Int.thFail $ "no support for promoted types."
    PromotedNilT{}   -> Int.thFail $ "no support for promoted types."
    PromotedConsT{}  -> Int.thFail $ "no support for promoted types."
    StarT{}          -> Int.thFail $ "no support for kinds."
    ConstraintT{}    -> Int.thFail $ "no support for constraint kinds."
    LitT{}           -> Int.thFail $ "no support for type literals."
    AppT{}           -> Int.thFail $ "impossible: AppT is guarded by peelApp."
    ForallT{}        -> Int.thFail $ "no support for ForallT."
    UnboxedTupleT{}  -> Int.thFail $ "no support for unboxed tuples."

    SigT ty _        -> uncurry w $ peelAppAcc tys ty

    VarT n | Just k <- List.findIndex (== n) $ reverse parNs ->
      if null tys then return $
        let (tyn, ctor, dtor) = case k of
              0 -> (''Par0, 'Par0, 'unPar0)
              1 -> (''Par1, 'Par1, 'unPar1)
        in (ConT tyn, FieldRO (ConE ctor) (VarE dtor))
      else Int.thFail $ "no support for poly- or higher-kinded parameters."

    ConT n | Just lbl <- case bg of Left _ -> Nothing; Right bg -> Map.lookup n bg -> case lbl of
      Nothing -> expandSyn ty tys >>= \case
        Just (ty, tys) -> w ty tys
        Nothing -> Int.thFail "impossible: expandSyn is guarded by yoko0."
      Just lbl -> appliedRec lbl container tys'
        where (foldl AppT ty -> container, tys') =
                List.splitAt (length tys - length parNs) tys

    -- NB cannot be recursive ... TODO unless we're operating on []
    _ -> appliedDep container importants
      where (foldl AppT ty -> container, importants) =
              List.break (any isImportant . Set.toList . namesIn) tys

  appliedRec lbl container tys = case null tys of
    True -> return (ConT ''T0 `AppT` (PromotedT 'Rec `AppT` toNat lbl) `AppT` container, FieldRO (ConE 'T0) (VarE 'unT0))
    False -> case lookup (length tys) maps of
      Nothing -> Int.thFail $ "no case in the given YokoOptions for type constructors with " ++ show (length tys) ++ " arguments."
      Just (Mapping {methodName = mn}) -> appliedType (ConT nRecTy `AppT` (PromotedT 'Rec `AppT` toNat lbl), nRecCtor, mn) container tys

  appliedDep container tys = case null tys of
    True -> return (ConT ''T0 `AppT` PromotedT 'Dep `AppT` container, FieldRO (ConE 'T0) (VarE 'unT0))
    False -> case lookup (length tys) maps of
      Nothing -> Int.thFail $ "no case in the given YokoOptions for type constructors with " ++ show (length tys) ++ " arguments."
      Just (Mapping {containerTypeName = tyn, containerCtor = ctor, methodName = mn}) ->
        appliedType (ConT tyn `AppT` PromotedT 'Dep, ctor, mn) container tys

  appliedType (rTy, nCtor, nMap) ty tys = do
    tys <- mapM w' tys
    let snoc (tyL, fROL) (tyR, fROR) = (tyL `AppT` tyR, fROL `appRO` fROR)
        appRO l r = FieldRO {repF = repF l `AppE` repF r `AppE` objF r,
                             objF = objF l `AppE` objF r `AppE` repF r}
        post fRO = FieldRO {repF = ConE nCtor `compose` repF fRO,
                            objF = objF fRO `compose` dtor}
          where dtor = let x = mkName "x" in LamE [ConP nCtor [VarP x]] (VarE x)
    return $ Arrow.second post $ foldl snoc
      (rTy `AppT` ty,
       FieldRO {repF = VarE nMap, objF = VarE nMap}) tys

data ConRO = ConRO {repP :: [Pat], repE :: Exp, objP :: Pat, objE :: [Exp]}

yoko1 r@(convert -> X :&
  Target       := tyn :&
  Renamer      := rn :&
  Mappings     := maps :&
  TargetData   := Int.DataType tvbs cons :&
  DCInsts      := dcInsts
        ) = do
  let activated = dcInsts $ either ((:[]) . conName) (map conName) cons

  -- make a name into a NameG for a type in the current module; NB the fields
  -- types need not be declared in the same module as the target type
  loc <- liftQ TH.location
  let mkG n = Name (mkOccName $ nameBase n) $
              NameG TcClsName (mkPkgName $ loc_package loc)
                      (mkModName $ loc_module loc)

  -- extract the ctors' fields and declare the fields types
  nAndFieldss <- flip mapM (either (:[]) id cons) $ \con -> do
    let n = conName con
        n' = rn n
    generate [Int.dataType2Dec n' $ Int.DataType tvbs $ Right [renameCon rn con]]
    (>>= generate) $ liftQ $ serializeTypeAsHash_data (mkG n')
    fmap ((,) n)   $ liftQ $ conFields con

  let tvbSplits = [ List.splitAt k tvbs
         | k <- [length (drop 2 tvbs)..length tvbs] ]
  -- eg tvbs = [a,b,c]: [   ([a,b,c], []),   ([a,b], [c]),   ([a], [b,c])   ]
  -- eg tvbs = [a,b]:   [   ([a,b]  , []),   ([a]  , [b]),   ([] , [a,b])   ]
  -- eg tvbs = [a]:     [   ([a]    , []),   ([]   , [a])                   ]
  -- eg tvbs = []:      [   ([]     , [])                                   ]

  (>>= generate) $ liftQ $ spineType_d_ tyn $ map tvbKind tvbs
  (>>= generate) $ liftQ $ serializeTypeAsHash_data tyn

  flip mapM_ tvbSplits $ \(tvbs, pars) ->
    (flip mapM (either (:[]) id cons) $ \con -> do
      let n = conName con
          n' = rn n
      ((>>= generate) $ liftQ $ spineType_d_ (mkG n') $ map tvbKind tvbs)) >>

    case filter ((/= StarT) . tvbKind) pars of
    offenders@(_:_) -> liftQ $ Int.thWarn $ "not representing " ++ nameBase tyn ++ " with " ++ msg (length pars) ++ " because [" ++ List.intercalate "," (map (nameBase . tvbName) offenders) ++ "] involves poly- or higher-kinds."
      where msg 1 = "1 parameter"
            msg n = show n ++ " parameters"
    [] -> do
      -- the pervasive context of the reflective Compare constraints
      cxt <- liftQ $ flip mapM tvbs $ \tvb ->
        EqualP (PromotedT 'EQ) `fmap` do
          let tv = [t| Spine $(return $ tvbType tvb) |]
          [t| Ord.Compare $tv $tv |]

      -- for every fields type, generate the fields types instances
      flip mapM_ nAndFieldss $ \(n, fields) -> do
        yoko2 (n `elem` activated) $ r :&
          TargetTVBs := tvbs :&
          TargetPars := pars :&
          TargetType := applyConT2TVBs tyn tvbs :&
          TargetCxt  := cxt :&
          ConName    := n :&
          ConFields  := fields

      -- generate the DCs, DTs, DT instances
      yoko3 $ r :&
          TargetTVBs := tvbs :&
          TargetPars := pars :&
          TargetType := applyConT2TVBs tyn tvbs :&
          TargetCxt  := cxt


yoko2 activated (convert -> X :&
  Renamer      := rn :&
  Mappings     := maps :&
  BindingGroup := bg :&
  TargetType   := ty :&
  TargetPars   := pars :&
  TargetTVBs   := tvbs :&
  TargetCxt    := cxt :&
  ConName      := n :&
  ConFields    := fields
        ) = do
  let (nDC, nRejoin) = case length pars of
        0 -> (''DC0, 'rejoin0)
        1 -> (''DC1, 'rejoin1)
        2 -> (''DC2, 'rejoin2)

  let (nGeneric, nRep, nObj) = case length pars of
        0 -> (''Generic0, 'rep0, 'obj0)
        1 -> (''Generic1, 'rep1, 'obj1)
        2 -> (''Generic2, 'rep2, 'obj2)

  let n' = rn n   ;   fd = applyConT2TVBs n' tvbs

  -- declare the fields type's Codomain/Tag/DC instances
  generate
    [TySynInstD ''Codomain [fd] ty,
     TySynInstD ''Tag   [fd] $ encode $ TH.nameBase n,
     InstanceD cxt (ConT nDC `AppT` fd)
       [let (pat, exp) = pat_exp n' n $ length fields
        in FunD nRejoin [simpleClause [pat] exp]]
    ]

  -- declare the Rep and Generic RHSs
  when activated $ (>>= generate) $ do
    (repTy, (conRO, _)) <- liftQ $ Arrow.second ($ 0) `fmap` halves fields
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
         in Arrow.second post `fmap`
            fieldRO maps bg (map tvbName pars) ty)

    return
      [ TySynInstD ''Rep [fd] (ConT ''C `AppT` fd `AppT` repTy),
        InstanceD cxt (ConT nGeneric `AppT` fd)
        [FunD nRep [simpleClause [ConP n' (repP conRO)] $ ConE 'C `AppE` repE conRO],
         FunD nObj [simpleClause [ConP 'C [objP conRO]] $ foldl AppE (ConE n') $ objE conRO]]]

-- generate DCs/DT instances
yoko3 r@(convert -> X :&
  Target       := tyn :&
  Renamer      := rn :&
  InvInsts     := invInsts :&
  TargetData   := Int.DataType _ cons :&
  BindingGroup := bg :&
  TargetType   := ty :&
  TargetPars   := pars :&
  TargetTVBs   := tvbs :&
  TargetCxt    := cxt
        ) = do
  let (nDT, nDisband, nN, nNCtor) = case length pars of
        0 -> (''DT0, 'disband0, ''N0, 'N0)
        1 -> (''DT1, 'disband1, ''N1, 'N1)
        2 -> (''DT2, 'disband2, ''N2, 'N2)

  let invInst = case length pars of
        0 -> Nothing
        1 -> Just (''Invariant, 'invmap, 'gen_invmap)
        2 -> Just (''Invariant2, 'invmap2, 'gen_invmap2)

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
                in (ConT nN `AppT` applyConT2TVBs (rn n) tvbs,
                    [(ConE nNCtor, (n, fields))]))

  cases <- return $ flip map cases $ \(inj, (n, fds)) ->
    let (pat, exp) = pat_exp n (rn n) fds
    in simpleClause [pat] $ inj `AppE` exp
  generate $ [TySynInstD ''DCs [ty] dcs,
              InstanceD cxt (ConT nDT `AppT` ty) [FunD nDisband cases]]

  when invInsts $ flip (maybe (return ())) invInst $ \(cls, method, rhs) ->
    generate [InstanceD cxt (ConT cls `AppT` ty) [ValD (VarP method) (NormalB (VarE rhs)) []]]

  (>>= generate) $ do
    rhs <- case fmap (Set.toAscList . Map.keysSet) bg of
      Left  _  -> return $ PromotedT 'NonRecDT
      Right ns -> do
        -- filter out the type synonyms
        ns <- fmap catMaybes $ flip mapM ns $ \n -> liftQ (reify n) >>= \case
          TyConI TySynD{} -> return Nothing
          _               -> return $ Just n
        let (l, _:r) = List.break (== tyn) ns
            promo = foldr cons PromotedNilT where
              cons n sofar = PromotedConsT `AppT` foldl AppT (ConT n) (map (VarT . tvbName) tvbs) `AppT` sofar
        return $ PromotedT 'RecDT `AppT` promo l `AppT` promo r
    return [TySynInstD ''DTs [ty] rhs]
