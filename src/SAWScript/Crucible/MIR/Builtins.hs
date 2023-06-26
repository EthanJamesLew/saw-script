{-# LANGUAGE ImplicitParams #-}

-- | Implementations of Crucible-related SAWScript primitives for MIR.
module SAWScript.Crucible.MIR.Builtins
  ( -- * Commands
    mir_execute_func
  , mir_load_module
    -- * Types
  , mir_array
  , mir_bool
  , mir_char
  , mir_i8
  , mir_i16
  , mir_i32
  , mir_i64
  , mir_i128
  , mir_isize
  , mir_f32
  , mir_f64
  , mir_ref
  , mir_ref_mut
  , mir_slice
  , mir_str
  , mir_tuple
  , mir_u8
  , mir_u16
  , mir_u32
  , mir_u64
  , mir_u128
  , mir_usize
  ) where

import           Control.Lens
import qualified Control.Monad.Catch as X
import           Control.Monad.State (MonadState(..))
import qualified Data.ByteString.Lazy as BSL

import Mir.Mir (BaseSize(..), FloatKind(..), Mutability(..), Ty(..))
import Mir.Generator
import Mir.Intrinsics (MIR)
import Mir.ParseTranslate

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Builtins as Setup
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import SAWScript.Options
import SAWScript.Value

type SetupValue = MS.SetupValue MIR

-----
-- Commands
-----

-- | TODO RGS: Docs
mir_execute_func :: [SetupValue] -> MIRSetupM ()
mir_execute_func args =
  MIRSetupM $
  {-
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     let argTys = mspec ^. MS.csArgs
     let
       checkArg i expectedTy val =
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (registerCompatible expectedTy valTy) $
              X.throwM (JVMArgTypeMismatch i expectedTy valTy)
     let
       checkArgs _ [] [] = pure ()
       checkArgs i [] vals =
         X.throwM (JVMArgNumberWrong i (i + length vals))
       checkArgs i tys [] =
         X.throwM (JVMArgNumberWrong (i + length tys) i)
       checkArgs i (ty : tys) (val : vals) =
         do checkArg i ty val
            checkArgs (i + 1) tys vals
     checkArgs 0 argTys args
     Setup.crucible_execute_func args
  -}
  undefined

-- | Load a MIR JSON file and return a handle to it.
mir_load_module :: String -> TopLevel RustModule
mir_load_module inputFile = do
   b <- io $ BSL.readFile inputFile

   opts <- getOptions
   let ?debug = simVerbose opts
   -- For now, we use the same default settings for implicit parameters as in
   -- crux-mir. We may want to add options later that allow configuring these.
   let ?assertFalseOnError = True
   let ?printCrucible = False

   halloc <- getHandleAlloc
   col <- io $ parseMIR inputFile b
   io $ translateMIR mempty col halloc

-----
-- Types
-----

mir_array :: Int -> Ty -> Ty
mir_array n t = TyArray t n

mir_bool :: Ty
mir_bool = TyBool

mir_char :: Ty
mir_char = TyChar

mir_i8 :: Ty
mir_i8 = TyInt B8

mir_i16 :: Ty
mir_i16 = TyInt B16

mir_i32 :: Ty
mir_i32 = TyInt B32

mir_i64 :: Ty
mir_i64 = TyInt B64

mir_i128 :: Ty
mir_i128 = TyInt B128

mir_isize :: Ty
mir_isize = TyInt USize

mir_f32 :: Ty
mir_f32 = TyFloat F32

mir_f64 :: Ty
mir_f64 = TyFloat F64

mir_ref :: Ty -> Ty
mir_ref ty = TyRef ty Immut

mir_ref_mut :: Ty -> Ty
mir_ref_mut ty = TyRef ty Mut

mir_slice :: Ty -> Ty
mir_slice = TySlice

mir_str :: Ty
mir_str = TyStr

mir_tuple :: [Ty] -> Ty
mir_tuple = TyTuple

mir_u8 :: Ty
mir_u8 = TyUint B8

mir_u16 :: Ty
mir_u16 = TyUint B16

mir_u32 :: Ty
mir_u32 = TyUint B32

mir_u64 :: Ty
mir_u64 = TyUint B64

mir_u128 :: Ty
mir_u128 = TyUint B128

mir_usize :: Ty
mir_usize = TyUint USize
