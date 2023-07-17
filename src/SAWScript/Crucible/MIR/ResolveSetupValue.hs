{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | TODO RGS: Docs
module SAWScript.Crucible.MIR.ResolveSetupValue
  ( MIRVal
  , resolveSetupVal
  , typeOfSetupValue
  , lookupAllocIndex
  , toMIRType
  , resolveTypedTerm
  , resolveBoolTerm
  {-
  -- TODO RGS: Docs
  , resolveSAWPred
  -- , resolveSetupFieldIndex
  , equalValsPred
  -}
  , MIRTypeOfError(..)
  ) where

import           Control.Lens
import           Control.Monad (zipWithM)
import qualified Control.Monad.Catch as X
import qualified Data.BitVector.Sized as BV
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Void (absurd)

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Type, Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4

import Verifier.SAW.Cryptol (importType, emptyEnv)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Simulator.What4.ReturnTrip
import Verifier.SAW.TypedTerm

-- crucible
import Lang.Crucible.Simulator (RegValue)

-- crucible-mir
import qualified Mir.Generator as Mir
import Mir.Intrinsics (MIR, MirVector(..), pattern MirVectorRepr)
import qualified Mir.Mir as Mir

-- what4
import qualified What4.Partial as W4

import SAWScript.Crucible.Common
import SAWScript.Crucible.Common.MethodSpec (AllocIndex(..))

import SAWScript.Panic
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.TypeShape
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.ResolveSetupValue (resolveBoolTerm)

-- | TODO RGS: Docs
data MIRVal where
  MIRVal :: TypeShape tp -> RegValue Sym tp -> MIRVal

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
    MS.SetupStruct _ _ _              -> error "TODO RGS: Structs"
    MS.SetupArray _ _                 -> error "TODO RGS: Arrays"
    MS.SetupElem _ _ _                -> error "TODO RGS: Elems"
    MS.SetupField _ _ _               -> error "TODO RGS: Fields"
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
resolveSetupVal mcc env _tyenv _nameEnv val =
  case val of
    MS.SetupVar i -> do
      Some ptr <- pure $ lookupAllocIndex env i
      let pointeeType = ptr ^. mpMirType
      pure $ MIRVal (RefShape
                        (Mir.TyRef pointeeType (ptr ^. mpMutbl))
                        pointeeType
                        (ptr ^. mpType))
                    (ptr ^. mpRef)
    MS.SetupTerm tm -> resolveTypedTerm mcc tm
    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct _ _ _              -> error "TODO RGS: Structs"
    MS.SetupArray _ _                 -> error "TODO RGS: Arrays"
    MS.SetupElem _ _ _                -> error "TODO RGS: Elems"
    MS.SetupField _ _ _               -> error "TODO RGS: Fields"
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
                            -- TODO RGS: Print shapes
                            ]
                pure val

          vals <- V.generateM sz' f
          pure $ MIRVal (ArrayShape (Mir.TyArray mirTy sz') mirTy shp)
               $ MirVector_Vector vals
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
          error "TODO RGS: Finish me"
          {-
          mirTys <- traverse (tyToShape col) tps
          pure $ MIRVal (StructShape M.Adt
          -}
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
    col = mcc ^. mccCollectionState ^. Mir.collection
{-
  case tp of
    Cryptol.TVBit ->
      fail "resolveSAWTerm: unimplemented type Bit (FIXME)"
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
      case someNat sz of
        Just (Some w)
          | Just LeqProof <- isPosNat w ->
            do v <- resolveSAWSymBV cc w tm
               Crucible.ptrToPtrVal <$> Crucible.llvmPointer_bv sym v
        _ -> fail ("Invalid bitvector width: " ++ show sz)
    Cryptol.TVSeq sz tp' ->
      do st <- sawCoreState sym
         let sc = saw_ctx st
         sz_tm <- scNat sc (fromIntegral sz)
         tp_tm <- importType sc emptyEnv (Cryptol.tValTy tp')
         let f i = do i_tm <- scNat sc (fromIntegral i)
                      tm' <- scAt sc sz_tm tp_tm tm i_tm
                      resolveSAWTerm cc tp' tm'
         case toLLVMType dl tp' of
           Left e -> fail ("In resolveSAWTerm: " ++ toLLVMTypeErrToString e)
           Right memTy -> do
             gt <- Crucible.toStorableType memTy
             Crucible.LLVMValArray gt . V.fromList <$> traverse f [ 0 .. (sz-1) ]
    Cryptol.TVStream _tp' ->
      fail "resolveSAWTerm: invalid infinite stream type"
    Cryptol.TVTuple tps ->
      do st <- sawCoreState sym
         let sc = saw_ctx st
         tms <- traverse (\i -> scTupleSelector sc tm i (length tps)) [1 .. length tps]
         vals <- zipWithM (resolveSAWTerm cc) tps tms
         storTy <-
           case toLLVMType dl tp of
             Left e -> fail ("In resolveSAWTerm: " ++ toLLVMTypeErrToString e)
             Right memTy -> Crucible.toStorableType memTy
         fields <-
           case Crucible.storageTypeF storTy of
             Crucible.Struct fields -> return fields
             _ -> fail "resolveSAWTerm: impossible: expected struct"
         return (Crucible.LLVMValStruct (V.zip fields (V.fromList vals)))
    Cryptol.TVRec _flds ->
      fail "resolveSAWTerm: unimplemented record type (FIXME)"
    Cryptol.TVFun _ _ ->
      fail "resolveSAWTerm: invalid function type"
    Cryptol.TVAbstract _ _ ->
      fail "resolveSAWTerm: invalid abstract type"
    Cryptol.TVNewtype{} ->
      fail "resolveSAWTerm: invalid newtype"
  where
    sym = cc^.ccSym
    dl = Crucible.llvmDataLayout (ccTypeCtx cc)
-}

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
    Cryptol.TVIntMod _ -> Left (NotYetSupported "integer (mod n)")
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

{-
-- TODO RGS: Delete me?

equalValsPred ::
  JVMCrucibleContext ->
  JVMVal ->
  JVMVal ->
  IO (W4.Pred Sym)
equalValsPred cc v1 v2 = go (v1, v2)
  where
  go :: (JVMVal, JVMVal) -> IO (W4.Pred Sym)
  go (RVal r1, RVal r2) = CJ.refIsEqual sym r1 r2
  go (IVal i1, IVal i2) = W4.bvEq sym i1 i2
  go (LVal l1, LVal l2) = W4.bvEq sym l1 l2
  go _ = return (W4.falsePred sym)

  sym = cc^.jccSym
-}
