{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

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

import qualified Control.Exception as X
import Control.Lens
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (for_, traverse_)
import Data.List (tails)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Parameterized.Some (Some(..))
import qualified Data.Set as Set
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import Data.Void (absurd)

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType, evalValType)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Mir.Intrinsics as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4

import Verifier.SAW.Prelude (scEq)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.What4.ReturnTrip (saw_ctx, toSC)
import Verifier.SAW.TypedAST
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.MethodSpec (AllocIndex(..))
import qualified SAWScript.Crucible.Common.Override as Ov (getSymInterface)
import SAWScript.Crucible.Common.Override hiding (getSymInterface)
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.ResolveSetupValue
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Options
import SAWScript.Utils (handleException)

-- A few convenient synonyms
type SetupValue = MS.SetupValue MIR
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR MIR
type StateSpec = MS.StateSpec MIR
type SetupCondition = MS.SetupCondition MIR

-- | Assign the given reference value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a reference-equality constraint.
assignVar ::
  MIRCrucibleContext {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  AllocIndex {- ^ variable index -} ->
  Some (MirPointer Sym) {- ^ concrete value -} ->
  OverrideMatcher MIR w ()

assignVar cc md var sref@(Some ref) =
  do old <- OM (setupValueSub . at var <<.= Just sref)
     let loc = MS.conditionLoc md
     for_ old $ \(Some ref') ->
       do p <- liftIO (equalRefsPred cc ref ref')
          addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased references" ""))

assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  MIRCrucibleContext    {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  MS.PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher MIR w ()

assignTerm sc cc md prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val)
       Just old ->
         matchTerm sc cc md prepost val old

decodeMIRVal :: Mir.Collection -> Mir.Ty -> Crucible.AnyValue Sym -> Maybe MIRVal
decodeMIRVal col ty (Crucible.AnyValue repr rv)
  | Some shp <- tyToShape col ty
  = case testEquality repr (shapeType shp) of
      Just Refl -> Just (MIRVal shp rv)
      Nothing   -> Nothing

-- | Verify that all of the fresh variables for the given
-- state spec have been "learned". If not, throws
-- 'AmbiguousVars' exception.
--
-- TODO RGS: This is copy-pasted among all the backends. Factor out.
enforceCompleteSubstitution :: W4.ProgramLoc -> StateSpec -> OverrideMatcher MIR w ()
enforceCompleteSubstitution loc ss =

  do sub <- OM (use termSub)

     let -- predicate matches terms that are not covered by the computed
         -- term substitution
         isMissing tt = ecVarIndex (tecExt tt) `Map.notMember` sub

         -- list of all terms not covered by substitution
         missing = filter isMissing (view MS.csFreshVars ss)

     unless (null missing) (failure loc (AmbiguousVars missing))

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness ::
  MIRCrucibleContext -> W4.ProgramLoc -> StateSpec -> OverrideMatcher MIR w ()
enforceDisjointness cc loc ss =
  do let sym = cc^.mccSym
     sub <- OM (use setupValueSub)
     let mems = Map.elems $ Map.intersectionWith (,) (view MS.csAllocs ss) sub

     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = mempty
              , MS.conditionType = "memory region disjointness"
              , MS.conditionContext = ""
              }
     -- Ensure that all regions are disjoint from each other.
     sequence_
        [ do c <- liftIO $ W4.notPred sym =<< equalRefsPred cc p q
             addAssert c md a

        | let a = Crucible.SimError loc $
                    Crucible.AssertFailureSimError "Memory regions not disjoint" ""
        , (_, Some p) : ps <- tails mems
        , (_, Some q)      <- ps
        ]

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
--
-- TODO RGS: This might be copypasta
instantiateSetupValue ::
  SharedContext     ->
  Map VarIndex Term ->
  SetupValue        ->
  IO SetupValue
instantiateSetupValue sc s v =
  case v of
    MS.SetupVar _                     -> return v
    MS.SetupTerm tt                   -> MS.SetupTerm <$> doTerm tt
    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct _ _ _              -> return v
    MS.SetupArray _ _                 -> return v
    MS.SetupElem _ _ _                -> return v
    MS.SetupField _ _ _               -> return v
    MS.SetupCast empty _ _            -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

-- learn pre/post condition
learnCond ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  MS.PrePost ->
  StateSpec ->
  OverrideMatcher MIR w ()
learnCond opts sc cc cs prepost ss =
  do let loc = cs ^. MS.csLoc
     matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss

-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Options                                          ->
  SharedContext                                    ->
  MIRCrucibleContext                               ->
  CrucibleMethodSpecIR                             ->
  MS.ConditionMetadata                             ->
  MS.PrePost                                       ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher MIR w ()
learnEqual opts sc cc spec md prepost v1 v2 =
  do val1 <- resolveSetupValueMIR opts cc sc spec v1
     val2 <- resolveSetupValueMIR opts cc sc spec v2
     p <- liftIO (equalValsPred cc val1 val2)
     let name = "equality " ++ stateCond prepost
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError name ""))

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  Options                    ->
  SharedContext              ->
  MIRCrucibleContext         ->
  CrucibleMethodSpecIR       ->
  MS.PrePost                 ->
  MirPointsTo                ->
  OverrideMatcher MIR w ()
learnPointsTo _opts _sc _cc _spec _prepost _pt = error "TODO RGS: learnPointsTo"

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  MIRCrucibleContext                                                  ->
  MS.ConditionMetadata                                                ->
  MS.PrePost                                                          ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher MIR w ()
learnPred sc cc md prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveBoolTerm (cc ^. mccSym) u
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError (stateCond prepost) ""))

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  Options                    ->
  SharedContext              ->
  MIRCrucibleContext         ->
  CrucibleMethodSpecIR       ->
  MS.PrePost                 ->
  SetupCondition             ->
  OverrideMatcher MIR w ()
learnSetupCondition opts sc cc spec prepost (MS.SetupCond_Equal md val1 val2)  = learnEqual opts sc cc spec md prepost val1 val2
learnSetupCondition _opts sc cc _    prepost (MS.SetupCond_Pred md tm)         = learnPred sc cc md prepost (ttTerm tm)
learnSetupCondition _opts _ _ _ _ (MS.SetupCond_Ghost empty _ _ _) = absurd empty

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

matchArg opts sc cc cs prepost md actual expectedTy expected@(MS.SetupTerm expectedTT)
  | TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym <- Ov.getSymInterface
       failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
       realTerm <- valueToSC sym md failMsg tval actual
       matchTerm sc cc md prepost realTerm (ttTerm expectedTT)

matchArg opts sc cc cs prepost md actual@(MIRVal (RefShape _refTy pointeeTy mutbl tpr) ref) expectedTy setupval =
  case setupval of
    MS.SetupVar var ->
      do assignVar cc md var (Some (MirPointer tpr mutbl pointeeTy ref))

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

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext    {- ^ term construction context -} ->
  MIRCrucibleContext  {- ^ simulator context     -}  ->
  CrucibleMethodSpecIR                               ->
  MS.PrePost                                         ->
  [MirPointsTo]       {- ^ points-tos                -} ->
  OverrideMatcher MIR w ()
matchPointsTos opts sc cc spec prepost = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [MirPointsTo] {- delayed conditions -} ->
      [MirPointsTo] {- queued conditions  -} ->
      OverrideMatcher MIR w ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (spec ^. MS.csLoc) (AmbiguousPointsTos delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next points-to in the work queue
    go progress delayed (c:cs) =
      do ready <- checkPointsTo c
         if ready then
           do learnPointsTo opts sc cc spec prepost c
              go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: MirPointsTo -> OverrideMatcher MIR w Bool
    checkPointsTo = error "TODO RGS: matchPointsTos.checkPointsTo"

    checkAllocIndex :: AllocIndex -> OverrideMatcher MIR w Bool
    checkAllocIndex i =
      do m <- OM (use setupValueSub)
         return (Map.member i m)

matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  MS.PrePost                                                    ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher MIR md ()

matchTerm _ _ _ _ real expect | real == expect = return ()
matchTerm sc cc md prepost real expect =
  do let loc = MS.conditionLoc md
     free <- OM (use osFree)
     case unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc cc md prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            let msg = unlines $
                  [ "Literal equality " ++ stateCond prepost
--                  , "Expected term: " ++ prettyTerm expect
--                  , "Actual term:   " ++ prettyTerm real
                  ]
            addTermEq t md $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

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
mkStructuralMismatch opts cc sc spec mirval setupval mty = do
  setupTy <- typeOfSetupValueMIR cc spec setupval
  setupJVal <- resolveSetupValueMIR opts cc sc spec setupval
  pure $ StructuralMismatch
            ({-_ppJVMVal-} error "TODO RGS: mkStructuralMismatch" mirval)
            ({-_ppJVMVal-} error "TODO RGS: mkStructuralMismatch" setupJVal)
            (Just setupTy)
            mty

resolveSetupValueMIR ::
  Options              ->
  MIRCrucibleContext   ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher MIR w MIRVal
resolveSetupValueMIR opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     sval' <- liftIO $ instantiateSetupValue sc s sval
     liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts

-- | TODO RGS: This is definitely copypasta
stateCond :: MS.PrePost -> String
stateCond MS.PreState = "precondition"
stateCond MS.PostState = "postcondition"

typeOfSetupValueMIR ::
  MIRCrucibleContext   ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher MIR w Mir.Ty
typeOfSetupValueMIR cc spec sval =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     liftIO $ typeOfSetupValue cc tyenv nameEnv sval

-- | TODO RGS: Finish me
valueToSC ::
  Sym ->
  MS.ConditionMetadata ->
  OverrideFailureReason MIR ->
  Cryptol.TValue ->
  MIRVal ->
  OverrideMatcher MIR w Term
valueToSC sym md failMsg tval (MIRVal shp val) =
  case (tval, shp) of
    (Cryptol.TVBit, PrimShape _ W4.BaseBoolRepr) ->
      liftIO (toSC sym st val)
    (Cryptol.TVSeq n Cryptol.TVBit, PrimShape _ (W4.BaseBVRepr w))
      |  n == 8, Just Refl <- testEquality w (W4.knownNat @8)
      -> liftIO (toSC sym st val)
      |  n == 16, Just Refl <- testEquality w (W4.knownNat @16)
      -> liftIO (toSC sym st val)
      |  n == 32, Just Refl <- testEquality w (W4.knownNat @32)
      -> liftIO (toSC sym st val)
      |  n == 64, Just Refl <- testEquality w (W4.knownNat @64)
      -> liftIO (toSC sym st val)
      |  n == 128, Just Refl <- testEquality w (W4.knownNat @128)
      -> liftIO (toSC sym st val)
    (Cryptol.TVTuple [], UnitShape _) ->
      liftIO (scUnitValue sc)
    (Cryptol.TVTuple _tys, TupleShape _ _ _) ->
      error "TODO RGS: valueToSC tuples"
    (Cryptol.TVSeq _n _cryty, ArrayShape _ _ _) ->
      error "TODO RGS: valueToSC arrays"
    _ ->
      failure (MS.conditionLoc md) failMsg
  where
    st = sym ^. W4.userState
    sc = saw_ctx st
