{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Turns 'SetupValue's back into 'MIRVal's.
module SAWScript.Crucible.MIR.ResolveSetupValue
  ( MIRVal(..)
  , ppMIRVal
  , resolveSetupVal
  , typeOfSetupValue
  , lookupAllocIndex
  , toMIRType
  , resolveTypedTerm
  , resolveBoolTerm
  , resolveSAWPred
  , equalRefsPred
  , equalValsPred
  , checkCompatibleTys
  , readMaybeType
  , doAlloc
  , doPointsTo
  , firstPointsToReferent
  , MIRTypeOfError(..)
  ) where

import           Control.Lens
import           Control.Monad (guard, zipWithM)
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.State (MonadState(..), StateT(..))
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Data.BitVector.Sized as BV
import           Data.Foldable (foldrM)
import qualified Data.Functor.Product as Functor
import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TraversableFC.WithIndex as FCI
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Vector (Vector)
import           Data.Void (absurd)
import           Numeric.Natural (Natural)
import qualified Prettyprinter as PP

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Type, Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)
import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.Simulator (AnyValue(..), RegValue, RegValue'(..), SymGlobalState)
import Lang.Crucible.Types (MaybeType, TypeRepr(..))
import qualified Mir.DefId as Mir
import qualified Mir.Generator as Mir
import qualified Mir.Intrinsics as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir
import qualified Mir.TransTy as Mir

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

import Verifier.SAW.Cryptol (importType, emptyEnv)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Simulator.What4.ReturnTrip
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.MethodSpec (AllocIndex(..))
import SAWScript.Crucible.Common.ResolveSetupValue (resolveBoolTerm)
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Panic

-- | A pair of a simulation-time MIR value ('RegValue') and its corresponding
-- type ('TypeShape'), where the @tp@ type parameter is closed over
-- existentially. SAW's MIR backend passes around 'MIRVal's at simulation time.
data MIRVal where
  MIRVal :: TypeShape tp -> RegValue Sym tp -> MIRVal

ppMIRVal ::
  forall ann.
  Sym ->
  MIRVal ->
  PP.Doc ann
ppMIRVal sym (MIRVal shp val) =
  case shp of
    UnitShape _ ->
      PP.pretty val
    PrimShape _ _ ->
      W4.printSymExpr val
    TupleShape _ _ fldShp ->
      PP.parens $ prettyStructOrTuple fldShp val
    ArrayShape _ _ shp' ->
      case val of
        Mir.MirVector_Vector vec ->
          PP.brackets $ commaList $ V.toList $
          fmap (\v -> ppMIRVal sym (MIRVal shp' v)) vec
        Mir.MirVector_PartialVector vec ->
          PP.braces $ commaList $ V.toList $
          fmap (\v -> let v' = readMaybeType sym "vector element" (shapeType shp') v in
                      ppMIRVal sym (MIRVal shp' v')) vec
        Mir.MirVector_Array arr ->
          W4.printSymExpr arr
    StructShape _ _ fldShp
      |  AnyValue (StructRepr fldTpr) fldVals <- val
      ,  Just Refl <- W4.testEquality (FC.fmapFC fieldShapeType fldShp) fldTpr
      -> PP.braces $ prettyStructOrTuple fldShp fldVals

      | otherwise
      -> error "Malformed MIRVal struct"
    TransparentShape _ shp' ->
      ppMIRVal sym $ MIRVal shp' val
    RefShape _ _ _ _  ->
      "<reference>"
    FnPtrShape _ _ _ ->
      PP.viaShow val
  where
    commaList :: [PP.Doc ann] -> PP.Doc ann
    commaList []     = PP.emptyDoc
    commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

    prettyStructOrTuple ::
      forall ctx.
      Ctx.Assignment FieldShape ctx ->
      Ctx.Assignment (RegValue' Sym) ctx ->
      PP.Doc ann
    prettyStructOrTuple fldShp fldVals =
      commaList $
      map (\(Some (Functor.Pair shp' (RV v))) -> prettyField shp' v) $
      FC.toListFC Some $
      Ctx.zipWith Functor.Pair fldShp fldVals

    prettyField ::
      forall tp.
      FieldShape tp ->
      RegValue Sym tp ->
      PP.Doc ann
    prettyField fldShp val' =
      case fldShp of
        OptField shp' ->
          ppMIRVal sym $ MIRVal shp' $
          readMaybeType sym "field" (shapeType shp') val'
        ReqField shp' ->
          ppMIRVal sym $ MIRVal shp' val'

type SetupValue = MS.SetupValue MIR

data MIRTypeOfError
  = MIRPolymorphicType Cryptol.Schema
  | MIRNonRepresentableType Cryptol.Type ToMIRTypeErr
  | MIRInvalidTypedTerm TypedTermType

instance Show MIRTypeOfError where
  show (MIRPolymorphicType s) =
    unlines
    [ "Expected monomorphic term"
    , "instead got:"
    , show (Cryptol.pp s)
    ]
  show (MIRNonRepresentableType ty err) =
    unlines
    [ "Type not representable in MIR:"
    , show (Cryptol.pp ty)
    , toMIRTypeErrToString err
    ]
  show (MIRInvalidTypedTerm tp) =
    unlines
    [ "Expected typed term with Cryptol-representable type, but got"
    , show (MS.ppTypedTermType tp)
    ]

instance X.Exception MIRTypeOfError

typeOfSetupValue ::
  X.MonadThrow m =>
  MIRCrucibleContext ->
  Map AllocIndex (Some MirAllocSpec) ->
  Map AllocIndex Text ->
  SetupValue ->
  m Mir.Ty
typeOfSetupValue _mcc env _nameEnv val =
  case val of
    MS.SetupVar i ->
      case Map.lookup i env of
        Nothing -> panic "MIRSetup" ["typeOfSetupValue", "Unresolved prestate variable:" ++ show i]
        Just (Some alloc) ->
          return $ Mir.TyRef (alloc^.maMirType) (alloc^.maMutbl)
    MS.SetupTerm tt ->
      case ttType tt of
        TypedTermSchema (Cryptol.Forall [] [] ty) ->
          case toMIRType (Cryptol.evalValType mempty ty) of
            Left err -> X.throwM (MIRNonRepresentableType ty err)
            Right mirTy -> return mirTy
        TypedTermSchema s -> X.throwM (MIRPolymorphicType s)
        tp -> X.throwM (MIRInvalidTypedTerm tp)

    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct _ _ _              -> panic "typeOfSetupValue" ["structs not yet implemented"]
    MS.SetupArray _ _                 -> panic "typeOfSetupValue" ["arrays not yet implemented"]
    MS.SetupElem _ _ _                -> panic "typeOfSetupValue" ["elems not yet implemented"]
    MS.SetupField _ _ _               -> panic "typeOfSetupValue" ["fields not yet implemented"]
    MS.SetupCast empty _ _            -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty

lookupAllocIndex :: Map AllocIndex a -> AllocIndex -> a
lookupAllocIndex env i =
  case Map.lookup i env of
    Nothing -> panic "MIRSetup" ["Unresolved prestate variable:" ++ show i]
    Just x -> x

-- | Translate a SetupValue into a Crucible MIR value, resolving
-- references
resolveSetupVal ::
  MIRCrucibleContext ->
  Map AllocIndex (Some (MirPointer Sym)) ->
  Map AllocIndex (Some MirAllocSpec) ->
  Map AllocIndex Text ->
  SetupValue ->
  IO MIRVal
resolveSetupVal mcc env tyenv nameEnv val =
  case val of
    MS.SetupVar i -> do
      Some ptr <- pure $ lookupAllocIndex env i
      let pointeeType = ptr ^. mpMirType
      pure $ MIRVal (RefShape
                        (Mir.TyRef pointeeType (ptr ^. mpMutbl))
                        pointeeType
                        (ptr ^. mpMutbl)
                        (ptr ^. mpType))
                    (ptr ^. mpRef)
    MS.SetupTerm tm -> resolveTypedTerm mcc tm
    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct _ _ _              -> panic "resolveSetupValue" ["structs not yet implemented"]
    MS.SetupArray () [] -> fail "resolveSetupVal: invalid empty array"
    MS.SetupArray () vs -> do
      vals <- V.mapM (resolveSetupVal mcc env tyenv nameEnv) (V.fromList vs)

      Some (shp :: TypeShape tp) <-
        case V.head vals of
          MIRVal shp _ -> pure (Some shp)

      let mirTy :: Mir.Ty
          mirTy = shapeMirTy shp

          vals' :: Vector (RegValue Sym tp)
          vals' = V.map (\(MIRVal shp' val') ->
                          case W4.testEquality shp shp' of
                            Just Refl -> val'
                            Nothing -> error $ unlines
                              [ "resolveSetupVal: internal error"
                              , show shp
                              , show shp'
                              ])
                        vals
      return $ MIRVal (ArrayShape (Mir.TyArray mirTy (V.length vals)) mirTy shp)
                      (Mir.MirVector_Vector vals')
    MS.SetupElem _ _ _                -> panic "resolveSetupValue" ["elems not yet implemented"]
    MS.SetupField _ _ _               -> panic "resolveSetupValue" ["fields not yet implemented"]
    MS.SetupCast empty _ _            -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty

resolveTypedTerm ::
  MIRCrucibleContext ->
  TypedTerm       ->
  IO MIRVal
resolveTypedTerm mcc tm =
  case ttType tm of
    TypedTermSchema (Cryptol.Forall [] [] ty) ->
      resolveSAWTerm mcc (Cryptol.evalValType mempty ty) (ttTerm tm)
    tp -> fail $ unlines
            [ "resolveTypedTerm: expected monomorphic term"
            , "but got a term of type"
            , show (MS.ppTypedTermType tp)
            ]

resolveSAWPred ::
  MIRCrucibleContext ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc tm =
  do let sym = cc^.mccSym
     st <- sawCoreState sym
     bindSAWTerm sym st W4.BaseBoolRepr tm

resolveSAWTerm ::
  MIRCrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO MIRVal
resolveSAWTerm mcc tp tm =
  case tp of
    Cryptol.TVBit ->
      do b <- resolveBoolTerm sym tm
         pure $ MIRVal (PrimShape Mir.TyBool W4.BaseBoolRepr) b
    Cryptol.TVInteger ->
      fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
    Cryptol.TVIntMod _ ->
      fail "resolveSAWTerm: unimplemented type Z n (FIXME)"
    Cryptol.TVFloat{} ->
      fail "resolveSAWTerm: unimplemented type Float e p (FIXME)"
    Cryptol.TVArray{} ->
      fail "resolveSAWTerm: unimplemented type Array a b (FIXME)"
    Cryptol.TVRational ->
      fail "resolveSAWTerm: unimplemented type Rational (FIXME)"
    Cryptol.TVSeq sz Cryptol.TVBit ->
      case sz of
        8   -> bv_term Mir.B8   $ W4.knownNat @8
        16  -> bv_term Mir.B16  $ W4.knownNat @16
        32  -> bv_term Mir.B32  $ W4.knownNat @32
        64  -> bv_term Mir.B64  $ W4.knownNat @64
        128 -> bv_term Mir.B128 $ W4.knownNat @128
        _   -> fail ("Invalid bitvector width: " ++ show sz)
      where
        bv_term :: forall w. 1 W4.<= w
                => Mir.BaseSize -> W4.NatRepr w -> IO MIRVal
        bv_term b n =
         MIRVal (PrimShape (Mir.TyUint b) (W4.BaseBVRepr n)) <$>
         resolveBitvectorTerm sym n tm
    Cryptol.TVSeq sz tp' -> do
      st <- sawCoreState sym
      let sc = saw_ctx st
      sz_tm <- scNat sc (fromIntegral sz)
      tp_tm <- importType sc emptyEnv (Cryptol.tValTy tp')
      case toMIRType tp' of
        Left e -> fail ("In resolveSAWTerm: " ++ toMIRTypeErrToString e)
        Right mirTy -> do
          Some (shp :: TypeShape tp) <- pure $ tyToShape col mirTy

          let sz' = fromInteger sz

              f :: Int -> IO (RegValue Sym tp)
              f i = do
                i_tm <- scNat sc (fromIntegral i)
                tm' <- scAt sc sz_tm tp_tm tm i_tm
                MIRVal shp' val <- resolveSAWTerm mcc tp' tm'
                Refl <- case W4.testEquality shp shp' of
                          Just r -> pure r
                          Nothing -> fail $ unlines
                            [ "resolveSAWTerm: internal error"
                            , show shp
                            , show shp'
                            ]
                pure val

          vals <- V.generateM sz' f
          pure $ MIRVal (ArrayShape (Mir.TyArray mirTy sz') mirTy shp)
               $ Mir.MirVector_Vector vals
    Cryptol.TVStream _tp' ->
      fail "resolveSAWTerm: unsupported infinite stream type"
    Cryptol.TVTuple tps -> do
      st <- sawCoreState sym
      let sc = saw_ctx st
      tms <- traverse (\i -> scTupleSelector sc tm i (length tps)) [1 .. length tps]
      vals <- zipWithM (resolveSAWTerm mcc) tps tms
      if null vals
        then pure $ MIRVal (UnitShape (Mir.TyTuple [])) ()
        else do
          let mirTys = map (\(MIRVal shp _) -> shapeMirTy shp) vals
          let mirTupleTy = Mir.TyTuple mirTys
          Some fldAssn <-
            pure $ Ctx.fromList $
            map (\(MIRVal shp val) ->
                  Some $ Functor.Pair (OptField shp) (RV (W4.justPartExpr sym val)))
                vals
          let (fldShpAssn, valAssn) = Ctx.unzip fldAssn
          pure $ MIRVal (TupleShape mirTupleTy mirTys fldShpAssn) valAssn
    Cryptol.TVRec _flds ->
      fail "resolveSAWTerm: unsupported record type"
    Cryptol.TVFun _ _ ->
      fail "resolveSAWTerm: unsupported function type"
    Cryptol.TVAbstract _ _ ->
      fail "resolveSAWTerm: unsupported abstract type"
    Cryptol.TVNewtype{} ->
      fail "resolveSAWTerm: unsupported newtype"
  where
    sym = mcc ^. mccSym
    col = mcc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection

resolveBitvectorTerm ::
  forall w.
  (1 W4.<= w) =>
  Sym ->
  W4.NatRepr w ->
  Term ->
  IO (W4.SymBV Sym w)
resolveBitvectorTerm sym w tm =
  do st <- sawCoreState sym
     let sc = saw_ctx st
     mx <- case getAllExts tm of
             -- concretely evaluate if it is a closed term
             [] ->
               do modmap <- scGetModuleMap sc
                  let v = Concrete.evalSharedTerm modmap mempty mempty tm
                  pure (Just (Prim.unsigned (Concrete.toWord v)))
             _ -> return Nothing
     case mx of
       Just x  -> W4.bvLit sym w (BV.mkBV w x)
       Nothing -> bindSAWTerm sym st (W4.BaseBVRepr w) tm

data ToMIRTypeErr = NotYetSupported String | Impossible String

toMIRTypeErrToString :: ToMIRTypeErr -> String
toMIRTypeErrToString =
  \case
    NotYetSupported ty ->
      unwords [ "SAW doesn't yet support translating Cryptol's"
              , ty
              , "type(s) into crucible-mir's type system."
              ]
    Impossible ty ->
      unwords [ "User error: It's impossible to store Cryptol"
              , ty
              , "values in crucible-mir's memory model."
              ]

toMIRType ::
  Cryptol.TValue ->
  Either ToMIRTypeErr Mir.Ty
toMIRType tp =
  case tp of
    Cryptol.TVBit -> Right Mir.TyBool
    Cryptol.TVInteger -> Left (NotYetSupported "integer")
    Cryptol.TVIntMod _ -> Left (Impossible "integer (mod n)")
    Cryptol.TVFloat{} -> Left (NotYetSupported "float e p")
    Cryptol.TVArray{} -> Left (NotYetSupported "array a b")
    Cryptol.TVRational -> Left (NotYetSupported "rational")
    Cryptol.TVSeq n Cryptol.TVBit ->
      case n of
        8   -> Right $ Mir.TyUint Mir.B8
        16  -> Right $ Mir.TyUint Mir.B16
        32  -> Right $ Mir.TyUint Mir.B32
        64  -> Right $ Mir.TyUint Mir.B64
        128 -> Right $ Mir.TyUint Mir.B128
        _   -> Left (Impossible ("unsupported bitvector size: " ++ show n))
    Cryptol.TVSeq n t -> do
      t' <- toMIRType t
      let n' = fromIntegral n
      Right $ Mir.TyArray t' n'
    Cryptol.TVStream _tp' -> Left (Impossible "stream")
    Cryptol.TVTuple tps -> do
      tps' <- traverse toMIRType tps
      Right $ Mir.TyTuple tps'
    Cryptol.TVRec _flds -> Left (NotYetSupported "record")
    Cryptol.TVFun _ _ -> Left (Impossible "function")
    Cryptol.TVAbstract _ _ -> Left (Impossible "abstract")
    Cryptol.TVNewtype{} -> Left (Impossible "newtype")

-- | Check if two MIR references are equal.
equalRefsPred ::
  MIRCrucibleContext ->
  MirPointer Sym tp1 ->
  MirPointer Sym tp2 ->
  IO (W4.Pred Sym)
equalRefsPred cc mp1 mp2 =
  mccWithBackend cc $ \bak ->
  let sym = backendGetSym bak in
  case W4.testEquality (mp1^.mpType) (mp2^.mpType) of
    Nothing -> pure $ W4.falsePred sym
    Just Refl -> Mir.mirRef_eqIO bak (mp1^.mpRef) (mp2^.mpRef)

equalValsPred ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO (W4.Pred Sym)
equalValsPred cc mv1 mv2 =
  case (mv1, mv2) of
    (MIRVal shp1 v1, MIRVal shp2 v2) -> do
      mbEq <- runMaybeT $ do
        guard $ checkCompatibleTys (shapeMirTy shp1) (shapeMirTy shp2)
        Refl <- testEquality shp1 shp2
        goTy shp1 v1 v2
      pure $ fromMaybe (W4.falsePred sym) mbEq
  where
    sym = cc^.mccSym

    testEquality :: forall k (f :: k -> Type) (a :: k) (b :: k)
                  . W4.TestEquality f
                 => f a -> f b -> MaybeT IO (a :~: b)
    testEquality v1 v2 = MaybeT $ pure $ W4.testEquality v1 v2

    goTy :: TypeShape tp
         -> RegValue Sym tp
         -> RegValue Sym tp
         -> MaybeT IO (W4.Pred Sym)
    goTy (UnitShape _) () () =
      pure $ W4.truePred sym
    goTy (PrimShape _ _) v1 v2 =
      liftIO $ W4.isEq sym v1 v2
    goTy (TupleShape _ _ fldShp) fldAssn1 fldAssn2 =
      goFldAssn fldShp fldAssn1 fldAssn2
    goTy (ArrayShape _ _ shp) vec1 vec2 =
      goVec shp vec1 vec2
    goTy (StructShape _ _ fldShp) any1 any2 =
      case (any1, any2) of
        (AnyValue (StructRepr fldCtx1) fldAssn1,
         AnyValue (StructRepr fldCtx2) fldAssn2) -> do
          Refl <- testEquality fldCtx1 fldCtx2
          Refl <- testEquality (FC.fmapFC fieldShapeType fldShp) fldCtx1
          goFldAssn fldShp fldAssn1 fldAssn2
        (_, _) ->
          pure $ W4.falsePred sym
    goTy (TransparentShape _ shp) v1 v2 =
      goTy shp v1 v2
    goTy (RefShape _ _ _ _) ref1 ref2 =
      mccWithBackend cc $ \bak ->
        liftIO $ Mir.mirRef_eqIO bak ref1 ref2
    goTy (FnPtrShape _ _ _) _fh1 _fh2 =
      error "Function pointers not currently supported in overrides"

    goVec :: TypeShape tp
          -> Mir.MirVector Sym tp
          -> Mir.MirVector Sym tp
          -> MaybeT IO (W4.Pred Sym)
    goVec shp (Mir.MirVector_Vector vec1)
              (Mir.MirVector_Vector vec2) = do
      eqs <- V.zipWithM (goTy shp) vec1 vec2
      liftIO $ foldrM (W4.andPred sym) (W4.truePred sym) eqs
    goVec shp (Mir.MirVector_PartialVector vec1)
              (Mir.MirVector_PartialVector vec2) = do
      eqs <- V.zipWithM
               (\v1 v2 -> do
                 let readElem v = readMaybeType sym "vector element" (shapeType shp) v
                 let v1' = readElem v1
                 let v2' = readElem v2
                 goTy shp v1' v2')
               vec1
               vec2
      liftIO $ foldrM (W4.andPred sym) (W4.truePred sym) eqs
    goVec _shp (Mir.MirVector_Array vec1) (Mir.MirVector_Array vec2) =
      liftIO $ W4.arrayEq sym vec1 vec2
    goVec _shp _vec1 _vec2 =
      pure $ W4.falsePred sym

    goFldAssn :: Ctx.Assignment FieldShape ctx
              -> Ctx.Assignment (RegValue' Sym) ctx
              -> Ctx.Assignment (RegValue' Sym) ctx
              -> MaybeT IO (W4.Pred Sym)
    goFldAssn fldShp fldAssn1 fldAssn2 =
      FCI.ifoldrMFC
        (\idx (Functor.Pair (RV fld1) (RV fld2)) z -> do
          let shp = fldShp Ctx.! idx
          eq <- goFld shp fld1 fld2
          liftIO $ W4.andPred sym eq z)
        (W4.truePred sym)
        (Ctx.zipWith Functor.Pair fldAssn1 fldAssn2)

    goFld :: FieldShape tp
          -> RegValue Sym tp
          -> RegValue Sym tp
          -> MaybeT IO (W4.Pred Sym)
    goFld shp v1 v2 =
      case shp of
        ReqField shp' ->
          goTy shp' v1 v2
        OptField shp' -> do
          let readField v = readMaybeType sym "field" (shapeType shp') v
          let v1' = readField v1
          let v2' = readField v2
          goTy shp' v1' v2'

-- | Check if two 'Mir.Ty's are compatible in SAW. This is a slightly coarser
-- notion of equality to reflect the fact that MIR's type system is richer than
-- Cryptol's type system, and some types which would be distinct in MIR are in
-- fact equal when converted to the equivalent Cryptol types. In particular:
--
-- 1. A @u<N>@ type is always compatible with an @i<N>@ type. For instance, @u8@
--    is compatible with @i8@, and @u16@ is compatible with @i16@. Note that the
--    bit sizes of both types must be the same. For instance, @u8@ is /not/
--    compatible with @i16@.
--
-- 2. The @usize@/@isize@ types are always compatible with @u<N>@/@i<N>@, where
--    @N@ is the number of bits corresponding to the 'Mir.SizeBits' type in
--    "Mir.Intrinsics". (This is a bit unsavory, as the actual size of
--    @usize@/@isize@ is platform-dependent, but this is the current approach.)
--
-- 3. Compatibility applies recursively. For instance, @[ty_1; N]@ is compatible
--    with @[ty_2; N]@ iff @ty_1@ and @ty_2@ are compatibile. Similarly, a tuple
--    typle @(ty_1_a, ..., ty_n_a)@ is compatible with @(ty_1_b, ..., ty_n_b)@
--    iff @ty_1_a@ is compatible with @ty_1_b@, ..., and @ty_n_a@ is compatible
--    with @ty_n_b@.
--
-- See also @checkRegisterCompatibility@ in "SAWScript.Crucible.LLVM.Builtins"
-- and @registerCompatible@ in "SAWScript.Crucible.JVM.Builtins", which fill a
-- similar niche in the LLVM and JVM backends, respectively.
checkCompatibleTys :: Mir.Ty -> Mir.Ty -> Bool
checkCompatibleTys ty1 ty2 = tyView ty1 == tyView ty2

-- | Like 'Mir.Ty', but where:
--
-- * The 'TyInt' and 'TyUint' constructors have been collapsed into a single
--   'TyViewInt' constructor.
--
-- * 'TyViewInt' uses 'BaseSizeView' instead of 'Mir.BaseSize'.
--
-- * Recursive occurrences of 'Mir.Ty' use 'TyView' instead. This also applies
--   to fields of type 'SubstsView' and 'FnSigView', which also replace 'Mir.Ty'
--   with 'TyView' in their definitions.
--
-- This provides a coarser notion of equality than what the 'Eq' instance for
-- 'Mir.Ty' provides, which distinguishes the two sorts of integer types.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data TyView
  = TyViewBool
  | TyViewChar
    -- | The sole integer type. Both 'TyInt' and 'TyUint' are mapped to
    -- 'TyViewInt', and 'BaseSizeView' is used instead of 'Mir.BaseSize'.
  | TyViewInt !BaseSizeView
  | TyViewTuple ![TyView]
  | TyViewSlice !TyView
  | TyViewArray !TyView !Int
  | TyViewRef !TyView !Mir.Mutability
  | TyViewAdt !Mir.DefId !Mir.DefId !SubstsView
  | TyViewFnDef !Mir.DefId
  | TyViewClosure [TyView]
  | TyViewStr
  | TyViewFnPtr !FnSigView
  | TyViewDynamic !Mir.TraitName
  | TyViewRawPtr !TyView !Mir.Mutability
  | TyViewFloat !Mir.FloatKind
  | TyViewDowncast !TyView !Integer
  | TyViewNever
  | TyViewForeign
  | TyViewLifetime
  | TyViewConst
  | TyViewErased
  | TyViewInterned Mir.TyName
  deriving Eq

-- | Like 'Mir.BaseSize', but without a special case for @usize@/@isize@.
-- Instead, these are mapped to their actual size, which is determined by the
-- number of bits in the 'Mir.SizeBits' type in "Mir.Intrinsics". (This is a bit
-- unsavory, as the actual size of @usize@/@isize@ is platform-dependent, but
-- this is the current approach.)
data BaseSizeView
  = B8View
  | B16View
  | B32View
  | B64View
  | B128View
  deriving Eq

-- | Like 'Mir.Substs', but using 'TyView's instead of 'Mir.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
newtype SubstsView = SubstsView [TyView]
  deriving Eq

-- | Like 'Mir.FnSig', but using 'TyView's instead of 'Mir.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data FnSigView = FnSigView {
    _fsvarg_tys    :: ![TyView]
  , _fsvreturn_ty  :: !TyView
  , _fsvabi        :: Mir.Abi
  , _fsvspreadarg  :: Maybe Int
  }
  deriving Eq

-- | Convert a 'Mir.Ty' value to a 'TyView' value.
tyView :: Mir.Ty -> TyView
-- The two most important cases. Both sorts of integers are mapped to TyViewInt.
tyView (Mir.TyInt  bs) = TyViewInt (baseSizeView bs)
tyView (Mir.TyUint bs) = TyViewInt (baseSizeView bs)
-- All other cases are straightforward.
tyView Mir.TyBool = TyViewBool
tyView Mir.TyChar = TyViewChar
tyView (Mir.TyTuple tys) = TyViewTuple (map tyView tys)
tyView (Mir.TySlice ty) = TyViewSlice (tyView ty)
tyView (Mir.TyArray ty n) = TyViewArray (tyView ty) n
tyView (Mir.TyRef ty mut) = TyViewRef (tyView ty) mut
tyView (Mir.TyAdt monoDid origDid substs) =
  TyViewAdt monoDid origDid (substsView substs)
tyView (Mir.TyFnDef did) = TyViewFnDef did
tyView (Mir.TyClosure tys) = TyViewClosure (map tyView tys)
tyView Mir.TyStr = TyViewStr
tyView (Mir.TyFnPtr sig) = TyViewFnPtr (fnSigView sig)
tyView (Mir.TyDynamic trait) = TyViewDynamic trait
tyView (Mir.TyRawPtr ty mut) = TyViewRawPtr (tyView ty) mut
tyView (Mir.TyFloat fk) = TyViewFloat fk
tyView (Mir.TyDowncast ty n) = TyViewDowncast (tyView ty) n
tyView Mir.TyNever = TyViewNever
tyView Mir.TyForeign = TyViewForeign
tyView Mir.TyLifetime = TyViewLifetime
tyView Mir.TyConst = TyViewConst
tyView Mir.TyErased = TyViewErased
tyView (Mir.TyInterned nm) = TyViewInterned nm

-- | Convert a 'Mir.BaseSize' value to a 'BaseSizeView' value.
baseSizeView :: Mir.BaseSize -> BaseSizeView
baseSizeView Mir.B8    = B8View
baseSizeView Mir.B16   = B16View
baseSizeView Mir.B32   = B32View
baseSizeView Mir.B64   = B64View
baseSizeView Mir.B128  = B128View
baseSizeView Mir.USize =
  case Map.lookup (W4.natValue sizeBitsRepr) bitSizesMap of
    Just bsv -> bsv
    Nothing ->
      error $ "Mir.Intrinsics.BaseSize bit size not supported: " ++ show sizeBitsRepr
  where
    sizeBitsRepr = W4.knownNat @Mir.SizeBits

    bitSizesMap :: Map Natural BaseSizeView
    bitSizesMap = Map.fromList
      [ (W4.natValue (W4.knownNat @8),   B8View)
      , (W4.natValue (W4.knownNat @16),  B16View)
      , (W4.natValue (W4.knownNat @32),  B32View)
      , (W4.natValue (W4.knownNat @64),  B64View)
      , (W4.natValue (W4.knownNat @128), B128View)
      ]

-- | Convert a 'Mir.Substs' value to a 'SubstsView' value.
substsView :: Mir.Substs -> SubstsView
substsView (Mir.Substs tys) = SubstsView (map tyView tys)

-- | Convert a 'Mir.FnSig' value to a 'FnSigView' value.
fnSigView :: Mir.FnSig -> FnSigView
fnSigView (Mir.FnSig argTys retTy abi spreadarg) =
  FnSigView (map tyView argTys) (tyView retTy) abi spreadarg

readMaybeType ::
     IsSymInterface sym
  => sym
  -> String
  -> TypeRepr tp
  -> RegValue sym (MaybeType tp)
  -> RegValue sym tp
readMaybeType sym desc tpr rv =
  case readPartExprMaybe sym rv of
    Just x -> x
    Nothing -> error $ "readMaybeType: accessed possibly-uninitialized " ++ desc ++
        " of type " ++ show tpr

readPartExprMaybe ::
     IsSymInterface sym
  => sym
  -> W4.PartExpr (W4.Pred sym) a
  -> Maybe a
readPartExprMaybe _sym W4.Unassigned = Nothing
readPartExprMaybe _sym (W4.PE p v)
  | Just True <- W4.asConstantPred p = Just v
  | otherwise = Nothing

-- | Allocate memory for each 'mir_alloc' or 'mir_alloc_mut'.
doAlloc ::
     MIRCrucibleContext
  -> Some MirAllocSpec
  -> StateT (SymGlobalState Sym) IO (Some (MirPointer Sym))
doAlloc cc (Some ma) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
     let halloc = cc^.mccHandleAllocator
     let sym = backendGetSym bak
     let iTypes = Mir.mirIntrinsicTypes
     Some tpr <- pure $ Mir.tyToRepr col (ma^.maMirType)

     -- Create an uninitialized `MirVector_PartialVector` of length 1 and
     -- return a pointer to its element.
     ref <- liftIO $
       Mir.newMirRefIO sym halloc (Mir.MirVectorRepr tpr)

     globals <- get
     globals' <- liftIO $ do
       one <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 1
       vec <- Mir.mirVector_uninitIO bak one
       Mir.writeMirRefIO bak globals iTypes ref vec
     put globals'

     ptr <- liftIO $ do
       zero <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 0
       Mir.subindexMirRefIO bak iTypes tpr ref zero
     pure $ Some MirPointer
       { _mpType = tpr
       , _mpMutbl = ma^.maMutbl
       , _mpMirType = ma^.maMirType
       , _mpRef = ptr
       }

doPointsTo ::
     MS.CrucibleMethodSpecIR MIR
  -> MIRCrucibleContext
  -> Map MS.AllocIndex (Some (MirPointer Sym))
  -> SymGlobalState Sym
  -> MirPointsTo
  -> IO (SymGlobalState Sym)
doPointsTo mspec cc env globals (MirPointsTo _ allocIdx referents) =
  mccWithBackend cc $ \bak -> do
    referent <- firstPointsToReferent referents
    MIRVal referentTy referentVal <-
      resolveSetupVal cc env tyenv nameEnv referent
    Some mp <- pure $ lookupAllocIndex env allocIdx
    -- By the time we reach here, we have already checked (in mir_points_to)
    -- that the type of the reference is compatible with the right-hand side
    -- value, so the equality check below should never fail.
    Refl <-
      case W4.testEquality (mp^.mpType) (shapeType referentTy) of
        Just r -> pure r
        Nothing ->
          panic "setupPrePointsTos"
                [ "Unexpected type mismatch between reference and referent"
                , "Reference type: " ++ show (mp^.mpType)
                , "Referent type:  " ++ show (shapeType referentTy)
                ]
    Mir.writeMirRefIO bak globals Mir.mirIntrinsicTypes (mp^.mpRef) referentVal
  where
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

-- | @mir_points_to@ always creates a 'MirPointsTo' value with exactly one
-- referent on the right-hand side. As a result, this function should never
-- fail.
firstPointsToReferent ::
  MonadFail m => [MS.SetupValue MIR] -> m (MS.SetupValue MIR)
firstPointsToReferent referents =
  case referents of
    [referent] -> pure referent
    _ -> fail $
      "Unexpected mir_points_to statement with " ++ show (length referents) ++
      " referent(s)"
