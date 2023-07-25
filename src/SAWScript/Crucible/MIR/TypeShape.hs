{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-} -- TODO RGS: Ugh. Remove this.

-- | TODO RGS: Docs
module SAWScript.Crucible.MIR.TypeShape
  ( TypeShape(..)
  , FieldShape(..)
  , tyToShape
  , tyToShapeEq
  , shapeType
  , fieldShapeType
  , shapeMirTy
  , fieldShapeMirTy
  ) where

import Control.Lens ((^.), (^..), each)
import qualified Data.Map as Map
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import GHC.Stack (HasCallStack)

import Lang.Crucible.Types

import Mir.Intrinsics
import qualified Mir.Mir as M
import Mir.TransTy ( tyListToCtx, tyToRepr, tyToReprCont, canInitialize
                   , isUnsized, reprTransparentFieldTy )

-- TODO RGS: Consolidate with SAWScript.Crucible.MIR.TypeShape
-- | TypeShape is used to classify MIR `Ty`s and their corresponding
-- CrucibleTypes into a few common cases.  We don't use `Ty` directly because
-- there are some `Ty`s that have identical structure (such as TyRef vs.
-- TyRawPtr) or similar enough structure that we'd rather write only one case
-- (such as `u8` vs `i8` vs `i32`, all primitives/BaseTypes).  And we don't use
-- TypeRepr directly because it's lacking information in some cases (notably
-- `TyAdt`, which is always AnyRepr, concealing the actual field types of the
-- struct).
--
-- In each constructor, the first `M.Ty` is the overall MIR type (e.g., for
-- ArrayShape, this is the TyArray type).  The overall `TypeRepr tp` isn't
-- stored directly, but can be computed with `shapeType`.
data TypeShape (tp :: CrucibleType) where
    UnitShape :: M.Ty -> TypeShape UnitType
    PrimShape :: M.Ty -> BaseTypeRepr btp -> TypeShape (BaseToType btp)
    TupleShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape (StructType ctx)
    ArrayShape :: M.Ty -> M.Ty -> TypeShape tp -> TypeShape (MirVectorType tp)
    StructShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape AnyType
    TransparentShape :: M.Ty -> TypeShape tp -> TypeShape tp
    -- | Note that RefShape contains only a TypeRepr for the pointee type, not
    -- a TypeShape.  None of our operations need to recurse inside pointers,
    -- and also this saves us from some infinite recursion.
    RefShape :: M.Ty
             -- ^ The reference type
             -> M.Ty
             -- ^ The pointee type
             -> M.Mutability
             -- ^ Is the reference mutable or immutable?
             -> TypeRepr tp
             -- ^ The Crucible representation of the pointee type
             -> TypeShape (MirReferenceType tp)
    -- | Note that 'FnPtrShape' contains only 'TypeRepr's for the argument and
    -- result types, not 'TypeShape's, as none of our operations need to recurse
    -- inside them.
    FnPtrShape :: M.Ty -> CtxRepr args -> TypeRepr ret
               -> TypeShape (FunctionHandleType args ret)

instance TestEquality TypeShape where
  testEquality (UnitShape ty1) (UnitShape ty2)
    | ty1 == ty2
    = Just Refl
  testEquality (PrimShape ty1 btpr1) (PrimShape ty2 btpr2)
    | ty1 == ty2
    , Just Refl <- testEquality btpr1 btpr2
    = Just Refl
  testEquality (TupleShape tupleTy1 fieldTys1 shp1) (TupleShape tupleTy2 fieldTys2 shp2)
    | tupleTy1 == tupleTy2
    , fieldTys1 == fieldTys2
    , Just Refl <- testEquality shp1 shp2
    = Just Refl
  testEquality (ArrayShape arrayTy1 elemTy1 shp1) (ArrayShape arrayTy2 elemTy2 shp2)
    | arrayTy1 == arrayTy2
    , elemTy1 == elemTy2
    , Just Refl <- testEquality shp1 shp2
    = Just Refl
  testEquality (StructShape structTy1 fieldTys1 shp1) (StructShape structTy2 fieldTys2 shp2)
    | structTy1 == structTy2
    , fieldTys1 == fieldTys2
    , Just Refl <- testEquality shp1 shp2
    = Just Refl
  testEquality (TransparentShape ty1 shp1) (TransparentShape ty2 shp2)
    | ty1 == ty2
    , Just Refl <- testEquality shp1 shp2
    = Just Refl
  testEquality (RefShape refTy1 pointeeTy1 mutbl1 tpr1) (RefShape refTy2 pointeeTy2 mutbl2 tpr2)
    | refTy1 == refTy2
    , pointeeTy1 == pointeeTy2
    , mutbl1 == mutbl2
    , Just Refl <- testEquality tpr1 tpr2
    = Just Refl
  testEquality (FnPtrShape ty1 args1 ret1) (FnPtrShape ty2 args2 ret2)
    | ty1 == ty2
    , Just Refl <- testEquality args1 args2
    , Just Refl <- testEquality ret1 ret2
    = Just Refl
  testEquality _ _
    = Nothing

-- | The TypeShape of a struct field, which might have a MaybeType wrapper to
-- allow for partial initialization.
data FieldShape (tp :: CrucibleType) where
    OptField :: TypeShape tp -> FieldShape (MaybeType tp)
    ReqField :: TypeShape tp -> FieldShape tp

instance TestEquality FieldShape where
  testEquality (OptField tpr1) (OptField tpr2)
    | Just Refl <- testEquality tpr1 tpr2
    = Just Refl
  testEquality (ReqField tpr1) (ReqField tpr2)
    | Just Refl <- testEquality tpr1 tpr2
    = Just Refl
  testEquality _ _
    = Nothing

-- | Return the `TypeShape` of `ty`.
--
-- It is guaranteed that the `tp :: CrucibleType` index of the resulting
-- `TypeShape` matches that returned by `tyToRepr`.
tyToShape :: M.Collection -> M.Ty -> Some TypeShape
tyToShape col ty = go ty
  where
    go :: M.Ty -> Some TypeShape
    go ty = case ty of
        M.TyBool -> goPrim ty
        M.TyChar -> goPrim ty
        M.TyInt _ -> goPrim ty
        M.TyUint _ -> goPrim ty
        M.TyTuple [] -> goUnit ty
        M.TyTuple tys -> goTuple ty tys
        M.TyClosure tys -> goTuple ty tys
        M.TyFnDef _ -> goUnit ty
        M.TyArray ty' _ | Some shp <- go ty' -> Some $ ArrayShape ty ty' shp
        M.TyAdt nm _ _ -> case Map.lookup nm (col ^. M.adts) of
            Just adt | Just ty' <- reprTransparentFieldTy col adt ->
                mapSome (TransparentShape ty) $ go ty'
            Just (M.Adt _ M.Struct [v] _ _ _ _) -> goStruct ty (v ^.. M.vfields . each . M.fty)
            Just (M.Adt _ ak _ _ _ _ _) -> error $ "tyToShape: AdtKind " ++ show ak ++ " NYI"
            Nothing -> error $ "tyToShape: bad adt: " ++ show ty
        M.TyRef ty' mutbl -> goRef ty ty' mutbl
        M.TyRawPtr ty' mutbl -> goRef ty ty' mutbl
        M.TyFnPtr sig -> goFnPtr ty sig
        _ -> error $ "tyToShape: " ++ show ty ++ " NYI"

    goPrim :: M.Ty -> Some TypeShape
    goPrim ty | Some tpr <- tyToRepr col ty, AsBaseType btpr <- asBaseType tpr =
        Some $ PrimShape ty btpr
    goPrim ty | Some tpr <- tyToRepr col ty =
        error $ "tyToShape: type " ++ show ty ++ " produced non-primitive type " ++ show tpr

    goUnit :: M.Ty -> Some TypeShape
    goUnit ty = Some $ UnitShape ty

    goTuple :: M.Ty -> [M.Ty] -> Some TypeShape
    goTuple ty tys | Some flds <- loop tys Empty = Some $ TupleShape ty tys flds
      where
        loop :: forall ctx. [M.Ty] -> Assignment FieldShape ctx -> Some (Assignment FieldShape)
        loop [] flds = Some flds
        loop (ty:tys) flds | Some fld <- go ty = loop tys (flds :> OptField fld)

    goStruct :: M.Ty -> [M.Ty] -> Some TypeShape
    goStruct ty tys | Some flds <- loop tys Empty = Some $ StructShape ty tys flds
      where
        loop :: forall ctx. [M.Ty] -> Assignment FieldShape ctx -> Some (Assignment FieldShape)
        loop [] flds = Some flds
        loop (ty:tys) flds | Some fld <- goField ty = loop tys (flds :> fld)

    goField :: M.Ty -> Some FieldShape
    goField ty | Some shp <- go ty = case canInitialize col ty of
        True -> Some $ ReqField shp
        False -> Some $ OptField shp

    goRef :: M.Ty -> M.Ty -> M.Mutability -> Some TypeShape
    goRef ty ty' mutbl
      | M.TySlice slicedTy <- ty'
      , Some tpr <- tyToRepr col slicedTy
      = Some $
         TupleShape ty [refTy, usizeTy]
             (Empty
                :> ReqField (RefShape refTy slicedTy mutbl tpr)
                :> ReqField (PrimShape usizeTy BaseUsizeRepr))
      | M.TyStr <- ty'
      = Some $
        TupleShape ty [refTy, usizeTy]
            (Empty
                :> ReqField (RefShape refTy (M.TyUint M.B8) mutbl (BVRepr (knownNat @8)))
                :> ReqField (PrimShape usizeTy BaseUsizeRepr))
      where
        -- We use a ref (of the same mutability as `ty`) when possible, to
        -- avoid unnecessary clobbering.
        refTy = case ty of
            M.TyRef _ _ -> M.TyRef ty' mutbl
            _ -> M.TyRef ty' mutbl
        usizeTy = M.TyUint M.USize
    goRef ty ty' _ | isUnsized ty' = error $
        "tyToShape: fat pointer " ++ show ty ++ " NYI"
    goRef ty ty' mutbl | Some tpr <- tyToRepr col ty' = Some $ RefShape ty ty' mutbl tpr

    goFnPtr :: M.Ty -> M.FnSig -> Some TypeShape
    goFnPtr ty (M.FnSig args ret _abi _spread) =
        tyListToCtx col args $ \argsr  ->
        tyToReprCont col ret $ \retr ->
           Some (FnPtrShape ty argsr retr)

-- | Given a `Ty` and the result of `tyToRepr ty`, produce a `TypeShape` with
-- the same index `tp`.  Raises an `error` if the `TypeRepr` doesn't match
-- `tyToRepr ty`.
tyToShapeEq :: HasCallStack => M.Collection -> M.Ty -> TypeRepr tp -> TypeShape tp
tyToShapeEq col ty tpr | Some shp <- tyToShape col ty =
    case testEquality (shapeType shp) tpr of
        Just Refl -> shp
        Nothing -> error $ "tyToShapeEq: type " ++ show ty ++
            " does not have representation " ++ show tpr ++
            " (got " ++ show (shapeType shp) ++ " instead)"

shapeType :: TypeShape tp -> TypeRepr tp
shapeType shp = go shp
  where
    go :: forall tp. TypeShape tp -> TypeRepr tp
    go (UnitShape _) = UnitRepr
    go (PrimShape _ btpr) = baseToType btpr
    go (TupleShape _ _ flds) = StructRepr $ fmapFC fieldShapeType flds
    go (ArrayShape _ _ shp) = MirVectorRepr $ shapeType shp
    go (StructShape _ _ _flds) = AnyRepr
    go (TransparentShape _ shp) = go shp
    go (RefShape _ _ _ tpr) = MirReferenceRepr tpr
    go (FnPtrShape _ args ret) = FunctionHandleRepr args ret

fieldShapeType :: FieldShape tp -> TypeRepr tp
fieldShapeType (ReqField shp) = shapeType shp
fieldShapeType (OptField shp) = MaybeRepr $ shapeType shp

shapeMirTy :: TypeShape tp -> M.Ty
shapeMirTy (UnitShape ty) = ty
shapeMirTy (PrimShape ty _) = ty
shapeMirTy (TupleShape ty _ _) = ty
shapeMirTy (ArrayShape ty _ _) = ty
shapeMirTy (StructShape ty _ _) = ty
shapeMirTy (TransparentShape ty _) = ty
shapeMirTy (RefShape ty _ _ _) = ty
shapeMirTy (FnPtrShape ty _ _) = ty

fieldShapeMirTy :: FieldShape tp -> M.Ty
fieldShapeMirTy (ReqField shp) = shapeMirTy shp
fieldShapeMirTy (OptField shp) = shapeMirTy shp
