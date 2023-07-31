{-# LANGUAGE GADTs #-}

-- | TODO RGS: Docs
module SAWScript.Crucible.MIR.Override
  ( OverrideMatcher
  , OverrideMatcher'(..)
  , runOverrideMatcher

  , setupValueSub
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , decodeMIRVal
  ) where

import Control.Lens ((^.))
import Data.Parameterized.Some (Some(..))
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import Data.Void (absurd)

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType, evalValType)

import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir

import qualified Lang.Crucible.Simulator as Crucible

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as Ov (getSymInterface)
import SAWScript.Crucible.Common.Override hiding (getSymInterface)
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.ResolveSetupValue
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Options

-- A few convenient synonyms
type SetupValue = MS.SetupValue MIR
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR MIR
type StateSpec = MS.StateSpec MIR

decodeMIRVal :: Mir.Collection -> Mir.Ty -> Crucible.AnyValue Sym -> Maybe MIRVal
decodeMIRVal col ty (Crucible.AnyValue repr rv)
  | Some shp <- tyToShape col ty
  = case testEquality repr (shapeType shp) of
      Just Refl -> Just (MIRVal shp rv)
      Nothing   -> Nothing

-- learn pre/post condition
learnCond ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  MS.PrePost ->
  StateSpec ->
  OverrideMatcher MIR w ()
learnCond _opts _sc _cc _cs _prepost _ss =
  pure ()
{-
learnCond _opts _sc _cc _cs _prepost _ss =
  error "TODO RGS: learnCond"
-}
{-
learnCond opts sc cc cs prepost ss =
  do let loc = cs ^. MS.csLoc
     matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss
-}

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  MIRCrucibleContext    {- ^ context for interacting with Crucible -} ->
  CrucibleMethodSpecIR {- ^ specification for current function override  -} ->
  MS.PrePost                                                          ->
  MS.ConditionMetadata ->
  MIRVal             {- ^ concrete simulation value             -} ->
  Mir.Ty             {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher MIR w ()

matchArg _opts _sc _cc _cs _prepost _md _actual _expectedTy _expected =
  pure ()

{-
matchArg _opts _sc _cc _cs _prepost _md _actual _expectedTy _expected =
  error "TODO RGS: matchArg"
-}

{-
matchArg opts sc cc cs prepost md actual expectedTy expected@(MS.SetupTerm expectedTT)
  | TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym <- Ov.getSymInterface
       failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
       realTerm <- valueToSC sym md failMsg tval actual
       matchTerm sc cc md prepost realTerm (ttTerm expectedTT)

matchArg opts sc cc cs prepost md actual@(MIRVal (RefShape{}) ref) expectedTy setupval =
  case setupval of
    MS.SetupVar var ->
      do assignVar cc md var ref

    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupCast empty _ _            -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty

    _ -> failure (cs ^. MS.csLoc) =<<
           mkStructuralMismatch opts cc sc cs actual setupval expectedTy

matchArg opts sc cc cs _prepost md actual expectedTy expected =
  failure (MS.conditionLoc md) =<<
    mkStructuralMismatch opts cc sc cs actual expected expectedTy
-}

-- | Try to translate the spec\'s 'SetupValue' into a 'MIRVal', pretty-print
--   the 'MIRVal'.
mkStructuralMismatch ::
  Options              {- ^ output/verbosity options -} ->
  MIRCrucibleContext ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  CrucibleMethodSpecIR {- ^ for name and typing environments -} ->
  MIRVal {- ^ the value from the simulator -} ->
  SetupValue {- ^ the value from the spec -} ->
  Mir.Ty     {- ^ the expected type -} ->
  OverrideMatcher MIR w (OverrideFailureReason MIR)
mkStructuralMismatch opts cc sc spec jvmval setupval jty = error "TODO RGS: mkStructuralMismatch"
{-
mkStructuralMismatch opts cc sc spec jvmval setupval jty = do
  setupTy <- typeOfSetupValueJVM cc spec setupval
  setupJVal <- resolveSetupValueJVM opts cc sc spec setupval
  pure $ StructuralMismatch
            (ppJVMVal jvmval)
            (ppJVMVal setupJVal)
            (Just setupTy)
            jty
-}
