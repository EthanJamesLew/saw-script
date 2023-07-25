{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Implementations of Crucible-related SAWScript primitives for MIR.
module SAWScript.Crucible.MIR.Builtins
  ( -- * Commands
    -- ** Setup
    mir_alloc
  , mir_alloc_mut
  , mir_assert
  , mir_execute_func
  , mir_fresh_var
  , mir_load_module
  , mir_postcond
  , mir_precond
  , mir_return
  , mir_verify
    -- ** MIR types
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

import Control.Lens
import Control.Monad (forM, unless, when)
import qualified Control.Monad.Catch as X
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (MonadState(..), execStateT, gets)
import Control.Monad.Trans.Class (MonadTrans(..))
import qualified Data.ByteString.Lazy as BSL
import Data.Foldable (for_)
import Data.IORef
import qualified Data.List.Extra as List (groupOn)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr (knownNat, natValue)
import Data.Parameterized.Some (Some(..))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Type.Equality (TestEquality(..))
import Data.Void (absurd)
import qualified Prettyprinter as PP
import System.IO (stdout)

import qualified Cryptol.TypeCheck.Type as Cryptol

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified Mir.DefId as Mir
import qualified Mir.Mir as Mir
import Mir.Generator
import Mir.Intrinsics (MIR)
import qualified Mir.Intrinsics as Mir
import Mir.ParseTranslate
import qualified Mir.TransTy as Mir

import qualified What4.Concrete as W4
import qualified What4.Config as W4
import qualified What4.Expr.Builder as W4
import qualified What4.FunctionName as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Utils.StringLiteral as W4S

import Verifier.SAW.FiniteValue (ppFirstOrderValue)
import Verifier.SAW.Name (toShortName)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.What4.ReturnTrip
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.Override
import qualified SAWScript.Crucible.Common.Setup.Builtins as Setup
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.Override
import SAWScript.Crucible.MIR.ResolveSetupValue
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Exceptions
import SAWScript.Options
import qualified SAWScript.Position as SS
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.Value

type AssumptionReason = (MS.ConditionMetadata, String)
type SetupValue = MS.SetupValue MIR
type Lemma = MS.ProvedSpec MIR
type MethodSpec = MS.CrucibleMethodSpecIR MIR
type SetupCondition = MS.SetupCondition MIR

-- TODO: something useful with the global pair?
ppMIRAbortedResult :: MIRCrucibleContext
                   -> Crucible.AbortedResult Sym a
                   -> PP.Doc ann
ppMIRAbortedResult _cc = ppAbortedResult (\_gp -> mempty)

-----
-- Commands
-----

-- | TODO RGS: Docs
mir_alloc :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc = mir_alloc_internal Mir.Immut

-- | TODO RGS: Docs
mir_alloc_mut :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc_mut = mir_alloc_internal Mir.Mut

-- | TODO RGS: Docs
mir_alloc_internal :: Mir.Mutability -> Mir.Ty -> MIRSetupM SetupValue
mir_alloc_internal mut mty =
  MIRSetupM $
  do st <- get
     let mcc = st ^. Setup.csCrucibleContext
     let col = mcc^.mccRustModule^.rmCS^.collection
     {-
     loc <- SS.toW4Loc "mir_alloc" <$> lift (lift getPosition)
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "fresh allocation"
              , MS.conditionContext = ""
              }
     -}
     Some tpr <- pure $ Mir.tyToRepr col mty
     n <- Setup.csVarCounter <<%= MS.nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?=
       Some (MirAllocSpec { _maType = tpr
                          , _maMutbl = mut
                          , _maMirType = mty
                          , _maLen = 1 -- TODO RGS: Is this right?
                          })
     return (MS.SetupVar n)

-- | TODO RGS: Docs
mir_execute_func :: [SetupValue] -> MIRSetupM ()
mir_execute_func args =
  MIRSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     let argTys = mspec ^. MS.csArgs
     let
       checkArg i expectedTy val =
         do valTy <- typeOfSetupValue cc env nameEnv val
            -- TODO RGS: Consider using a coarser-grained equality test
            -- than this
            unless (expectedTy == valTy) $
              X.throwM (MIRArgTypeMismatch i expectedTy valTy)
     let
       checkArgs _ [] [] = pure ()
       checkArgs i [] vals =
         X.throwM (MIRArgNumberWrong i (i + length vals))
       checkArgs i tys [] =
         X.throwM (MIRArgNumberWrong (i + length tys) i)
       checkArgs i (ty : tys) (val : vals) =
         do checkArg i ty val
            checkArgs (i + 1) tys vals
     checkArgs 0 argTys args
     Setup.crucible_execute_func args

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
mir_fresh_var ::
  Text                {- ^ variable name    -} ->
  Mir.Ty              {- ^ variable type    -} ->
  MIRSetupM TypedTerm {- ^ fresh typed term -}
mir_fresh_var name mty =
  MIRSetupM $
  do sc <- lift $ lift getSharedContext
     case cryptolTypeOfActual mty of
       Nothing -> X.throwM $ MIRFreshVarInvalidType mty
       Just cty -> Setup.freshVariable sc name cty

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

-- | TODO RGS: Docs
mir_return :: SetupValue -> MIRSetupM ()
mir_return retVal =
  MIRSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     valTy <- typeOfSetupValue cc env nameEnv retVal
     case mspec ^. MS.csRet of
       Nothing ->
         X.throwM (MIRReturnUnexpected valTy)
       Just retTy ->
         -- TODO RGS: Consider using a coarser-grained equality test
         -- than this
         unless (retTy == valTy) $
         X.throwM (MIRReturnTypeMismatch retTy valTy)
     Setup.crucible_return retVal

mir_assert :: TypedTerm -> MIRSetupM ()
mir_assert term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_assert" <$> lift (lift getPosition)
  tags <- view Setup.croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "specification assertion"
           , MS.conditionContext = ""
           }
  Setup.addCondition (MS.SetupCond_Pred md term)

mir_precond :: TypedTerm -> MIRSetupM ()
mir_precond term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_precond" <$> lift (lift getPosition)
  Setup.crucible_precond loc term

mir_postcond :: TypedTerm -> MIRSetupM ()
mir_postcond term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_postcond" <$> lift (lift getPosition)
  Setup.crucible_postcond loc term

mir_verify ::
  RustModule ->
  String {- ^ method name -} ->
  [Lemma] {- ^ overrides -} ->
  Bool {- ^ path sat checking -} ->
  MIRSetupM () ->
  ProofScript () ->
  TopLevel Lemma
mir_verify rm nm lemmas checkSat setup tactic =
  do start <- io getCurrentTime
     -- cb <- getJavaCodebase
     opts <- getOptions

     -- set up the metadata map for tracking proof obligation metadata
     -- mdMap <- io $ newIORef mempty

     {-
     -- allocate all of the handles/static vars that are referenced
     -- (directly or indirectly) by this class
     allRefs <- io $ Set.toList <$> allClassRefs cb (J.className cls)
     let refs = CJ.initClasses ++ allRefs -- ++ superRefs
     mapM_ (prepareClassTopLevel . J.unClassName) refs
     -}

     cc <- setupCrucibleContext rm
     SomeOnlineBackend bak <- pure (cc^.mccBackend)
     let sym = cc^.mccSym
     -- let mc = cc^.mccJVMContext

     pos <- getPosition
     let loc = SS.toW4Loc "_SAW_verify_prestate" pos

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ setupProfiling sym "mir_verify" profFile

     {-
     (cls', method) <- io $ findMethod cb pos nm cls -- TODO: switch to crucible-jvm version
     let st0 = initialCrucibleSetupState cc (cls', method) loc

     -- execute commands of the method spec
     io $ W4.setCurrentProgramLoc sym loc
     methodSpec <- view Setup.csMethodSpec <$>
                     execStateT
                       (runReaderT (runJVMSetupM setup) Setup.makeCrucibleSetupRO)
                     st0

     -- construct the dynamic class table and declare static fields
     globals1 <- liftIO $ setupGlobalState sym jc

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame bak

     -- run the symbolic execution
     top_loc <- SS.toW4Loc "jvm_verify" <$> getPosition
     (ret, globals3) <-
       io $ verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals2 checkSat mdMap

     -- collect the proof obligations
     asserts <- verifyPoststate cc
                    methodSpec env globals3 ret mdMap

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame bak frameIdent

     -- attempt to verify the proof obligations
     (stats,vcstats) <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas)
     end <- io getCurrentTime
     let diff = diffUTCTime end start
     ps <- io (MS.mkProvedSpec MS.SpecProved methodSpec stats vcstats lemmaSet diff)
     returnProof ps
     -}
     error "TODO RGS: mir_verify"

-----
-- Mir.Types
-----

mir_array :: Int -> Mir.Ty -> Mir.Ty
mir_array n t = Mir.TyArray t n

mir_bool :: Mir.Ty
mir_bool = Mir.TyBool

mir_char :: Mir.Ty
mir_char = Mir.TyChar

mir_i8 :: Mir.Ty
mir_i8 = Mir.TyInt Mir.B8

mir_i16 :: Mir.Ty
mir_i16 = Mir.TyInt Mir.B16

mir_i32 :: Mir.Ty
mir_i32 = Mir.TyInt Mir.B32

mir_i64 :: Mir.Ty
mir_i64 = Mir.TyInt Mir.B64

mir_i128 :: Mir.Ty
mir_i128 = Mir.TyInt Mir.B128

mir_isize :: Mir.Ty
mir_isize = Mir.TyInt Mir.USize

mir_f32 :: Mir.Ty
mir_f32 = Mir.TyFloat Mir.F32

mir_f64 :: Mir.Ty
mir_f64 = Mir.TyFloat Mir.F64

mir_ref :: Mir.Ty -> Mir.Ty
mir_ref ty = Mir.TyRef ty Mir.Immut

mir_ref_mut :: Mir.Ty -> Mir.Ty
mir_ref_mut ty = Mir.TyRef ty Mir.Mut

mir_slice :: Mir.Ty -> Mir.Ty
mir_slice = Mir.TySlice

mir_str :: Mir.Ty
mir_str = Mir.TyStr

mir_tuple :: [Mir.Ty] -> Mir.Ty
mir_tuple = Mir.TyTuple

mir_u8 :: Mir.Ty
mir_u8 = Mir.TyUint Mir.B8

mir_u16 :: Mir.Ty
mir_u16 = Mir.TyUint Mir.B16

mir_u32 :: Mir.Ty
mir_u32 = Mir.TyUint Mir.B32

mir_u64 :: Mir.Ty
mir_u64 = Mir.TyUint Mir.B64

mir_u128 :: Mir.Ty
mir_u128 = Mir.TyUint Mir.B128

mir_usize :: Mir.Ty
mir_usize = Mir.TyUint Mir.USize

--------------------------------------------------------------------------------
-- mir_verify
--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'MIRVal's are equal.
assertEqualVals ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO Term
assertEqualVals cc v1 v2 =
  do let sym = cc^.mccSym
     st <- sawCoreState sym
     toSC sym st =<< equalValsPred cc v1 v2

equalValsPred ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO (W4.Pred Sym)
equalValsPred = error "TODO RGS: equalValsPred"
{-
equalValsPred cc (MIRVal shp1' v1') (MIRVal shp2' v2') =
  go shp1' shp2' v1' v2'
  where
    sym = cc^.mccSym

    go :: TypeShape tp1 -> TypeShape tp2
       -> Crucible.RegValue Sym tp1 -> Crucible.RegValue Sym tp2
       -> IO (W4.Pred Sym)
    go shp1 shp2 v1 v2 =
      case testEquality shp1 shp2 of
        Just Refl ->
          case shp1 of
            UnitShape{} ->
              pure (W4.truePred sym)
            PrimShape{} ->
              W4.isEq sym v1 v2
            -- TupleShape{}
            -- ArrayShape{}
            -- FnPtrShape{}
        Nothing ->
          pure (W4.falsePred sym)

    andAlso :: Bool -> IO (W4.Pred Sym) -> IO (W4.Pred Sym)
    andAlso b x = if b then x else pure (W4.falsePred sym)

    -- allEqual shp1 shp2 vs1 vs2 =
    --   foldM (\x y -> andPred sym <$> x <*> y) (truePred sym) =<<
    --     V.zipWithM (go shp1 shp2) vs1 vs2
-}

registerOverride ::
  Options ->
  MIRCrucibleContext ->
  Crucible.SimContext (SAWCruciblePersonality Sym) Sym MIR ->
  W4.ProgramLoc ->
  IORef MetadataMap {- ^ metadata map -} ->
  [MethodSpec] ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret ()
registerOverride opts cc _ctx top_loc mdMap cs =
  do let sym = cc^.mccSym
     let c0 = head cs
     let method = c0 ^. MS.csMethod
     let rm = cc^.mccRustModule
     let cfgMap = rm^.rmCFGs

     sc <- saw_ctx <$> liftIO (sawCoreState sym)

     -- TODO RGS: Factor out CFG lookup logic into its own function
     Crucible.AnyCFG cfg <- case Map.lookup (Mir.idText method) cfgMap of
         Just x -> return x
         Nothing -> fail $ "couldn't find cfg for " ++ show method
     let h = Crucible.cfgHandle cfg
     let retTy = Crucible.handleReturnType h

     Crucible.bindFnHandle h
       $ Crucible.UseOverride
       $ Crucible.mkOverride'
           (Crucible.handleName h)
           retTy
           ({-methodSpecHandler-} error "TODO RGS: registerOverride" opts sc cc top_loc mdMap cs h)

resolveArguments ::
  MIRCrucibleContext ->
  MethodSpec ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  IO [(Mir.Ty, MIRVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec ^. MS.csArgs))
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames
    nm = mspec ^. MS.csMethod

    checkArgTy i mt mt' =
      -- TODO RGS: Consider using a coarser-grained equality test
      -- than this
      unless (mt == mt') $
           fail $ unlines [ "Type mismatch in argument " ++ show i ++ " when verifying " ++ show nm
                          , "Argument is declared with type: " ++ show mt
                          , "but provided argument has incompatible type: " ++ show mt'
                          , "Note: this may be because the signature of your " ++
                            "function changed during compilation."
                          ]
    resolveArg i =
      case Map.lookup i (mspec ^. MS.csArgBindings) of
        Just (mt, sv) -> do
          mt' <- typeOfSetupValue cc tyenv nameEnv sv
          checkArgTy i mt mt'
          v <- resolveSetupVal cc env tyenv nameEnv sv
          return (mt, v)
        Nothing -> fail $ unwords ["Argument", show i, "unspecified when verifying", show nm]

{-
-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos :: forall arch.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  Options ->
  LLVMCrucibleContext arch       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  [MS.PointsTo (LLVM arch)]                 ->
  MemImpl                    ->
  IO MemImpl
setupPrePointsTos mspec opts cc env pts mem0 = foldM go mem0 pts
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    go :: MemImpl -> MS.PointsTo (LLVM arch) -> IO MemImpl
    go mem (LLVMPointsTo _loc cond ptr val) =
      do ptr' <- resolveSetupVal cc mem env tyenv nameEnv ptr
         ptr'' <- unpackPtrVal ptr'

         cond' <- mapM (resolveSAWPred cc . ttTerm) cond

         storePointsToValue opts cc env tyenv nameEnv mem cond' ptr'' val Nothing
    go mem (LLVMPointsToBitfield _loc ptr fieldName val) =
      do (bfIndex, ptr') <- resolveSetupValBitfield cc mem env tyenv nameEnv ptr fieldName
         ptr'' <- unpackPtrVal ptr'

         storePointsToBitfieldValue opts cc env tyenv nameEnv mem ptr'' bfIndex val

    unpackPtrVal :: LLVMVal -> IO (LLVMPtr (Crucible.ArchWidth arch))
    unpackPtrVal (Crucible.LLVMValInt blk off)
        | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth
        = return (Crucible.LLVMPointer blk off)
    unpackPtrVal _ = throwMethodSpec mspec "Non-pointer value found in points-to assertion"
-}

-- | Collects boolean terms that should be assumed to be true.
-- TODO RGS: This seems copy-pasted, deduplicate?
setupPrestateConditions ::
  MethodSpec ->
  MIRCrucibleContext ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  [SetupCondition] ->
  IO [Crucible.LabeledPred Term AssumptionReason]
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc [] = return acc

    aux acc (MS.SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (loc, "equality precondition")
         aux (lp:acc) xs

    aux acc (MS.SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (loc, "precondition") in
      aux (lp:acc) xs

    aux _ (MS.SetupCond_Ghost empty_ _ _ _ : _) = absurd empty_

verifyObligations ::
  MIRCrucibleContext ->
  MethodSpec ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  [(String, MS.ConditionMetadata, Term)] ->
  TopLevel (SolverStats, [MS.VCStats])
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.mccSym
     st <- io $ sawCoreState sym
     let sc = saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm = show $ mspec ^. MS.csMethod
     outs <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, md, assert)) -> do
       goal   <- io $ scImplies sc assume assert
       goal'  <- io $ boolToProp sc [] goal -- TODO, generalize over inputs
       let ploc = MS.conditionLoc md
       let gloc = (unwords [show (W4.plSourceLoc ploc)
                          ,"in"
                          , show (W4.plFunction ploc)]) ++
                  (if Prelude.null (MS.conditionContext md) then [] else
                     "\n" ++ MS.conditionContext md)
       let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
       let proofgoal = ProofGoal
                       { goalNum  = n
                       , goalType = MS.conditionType md
                       , goalName = nm
                       , goalLoc  = gloc
                       , goalDesc = msg
                       , goalSequent = propToSequent goal'
                       , goalTags = MS.conditionTags md
                       }
       res <- runProofScript tactic goal' proofgoal (Just ploc)
                (Text.unwords
                 ["MIR verification condition:", Text.pack (show n), Text.pack goalname])
                False -- do not record in the theorem database
                False -- TODO, useSequentGoals...
       case res of
         ValidProof stats thm ->
           return (stats, MS.VCStats md stats (thmSummary thm) (thmNonce thm) (thmDepends thm) (thmElapsedTime thm))
         InvalidProof stats vals _pst -> do
           printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
           printOutLnTop Info (show stats)
           printOutLnTop OnlyCounterExamples "----------Counterexample----------"
           opts <- sawPPOpts <$> rwPPOpts <$> getTopLevelRW
           let showEC ec = Text.unpack (toShortName (ecName ec))
           let showAssignment (name, val) = "  " ++ showEC name ++ ": " ++ show (ppFirstOrderValue opts val)
           mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
           io $ fail "Proof failed." -- Mirroring behavior of llvm_verify
         UnfinishedProof pst ->
           io $ fail $ "Proof failed " ++ show (length (psGoals pst)) ++ " goals remaining."

     printOutLnTop Info $ unwords ["Proof succeeded!", nm]

     let stats = mconcat (map fst outs)
     let vcstats = map snd outs
     return (stats, vcstats)

-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'mir_alloc' statement.
--
-- * Record an equality precondition for each 'mir_equal'
-- statement.
--
-- * Write to memory for each 'mir_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'mir_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
{-
verifyPrestate ::
  Options ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  Crucible.SymGlobalState Sym ->
  IO ([(Crucible.MemType, LLVMVal)],
      [Crucible.LabeledPred Term AssumptionReason],
      Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)),
      Crucible.SymGlobalState Sym)
-}
verifyPrestate opts cc mspec globals =
  do -- let ?lc = ccTypeCtx cc
     let sym = cc^.mccSym
     let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
     liftIO $ W4.setCurrentProgramLoc sym prestateLoc

     {-
     let lvar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem <-
       case Crucible.lookupGlobal lvar globals of
         Nothing  -> fail "internal error: LLVM Memory global not found"
         Just mem -> pure mem
     -}

     {-
     -- Allocate LLVM memory for each 'llvm_alloc'
     (env, mem') <- runStateT
       (Map.traverseWithKey (doAlloc cc) (mspec ^. MS.csPreState . MS.csAllocs))
       mem

     mem'' <- setupGlobalAllocs cc mspec mem'

     mem''' <- setupPrePointsTos mspec opts cc env (mspec ^. MS.csPreState . MS.csPointsTos) mem''

     let globals1 = Crucible.insertGlobal lvar mem''' globals
     (globals2,cs) <-
       setupPrestateConditions mspec cc mem''' env globals1 (mspec ^. MS.csPreState . MS.csConditions)
     args <- resolveArguments cc mem''' mspec env

     return (args, cs, env, globals2)
     -}
     error "TODO RGS: verifyPrestate"

verifySimulate ::
  Options ->
  MIRCrucibleContext ->
  [Crucible.GenericExecutionFeature Sym] ->
  MethodSpec ->
  [(a, MIRVal)] ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  W4.ProgramLoc ->
  [Lemma] ->
  Crucible.SymGlobalState Sym ->
  Bool {- ^ path sat checking -} ->
  IORef MetadataMap {- ^ metadata map -} ->
  IO (Maybe (Mir.Ty, MIRVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals _checkSat mdMap =
  mccWithBackend cc $ \bak ->
  do let rm = cc^.mccRustModule
     let cfgMap = rm^.rmCFGs
     let col = rm^.rmCS^.collection
     let method = mspec ^. MS.csMethod
     let verbosity = simVerbose opts
     let halloc = cc^.mccHandleAllocator

     -- executeCrucibleJVM

     when (verbosity > 2) $
          putStrLn "starting executeCrucibleMIR"

     -- Find and run the target function
     -- TODO RGS: Factor out CFG lookup logic into its own function
     Crucible.AnyCFG cfg <- case Map.lookup (Mir.idText method) cfgMap of
         Just x -> return x
         Nothing -> fail $ "couldn't find cfg for " ++ show method
     let hf = Crucible.cfgHandle cfg
     let argTys = Crucible.handleArgTypes hf
     let retTy = Crucible.handleReturnType hf

     regmap <- prepareArgs argTys (map snd args)
     res <-
       do let feats = pfs
          let simctx = Crucible.initSimContext bak Mir.mirIntrinsicTypes halloc stdout
                         (Crucible.FnBindings Crucible.emptyHandleMap) Mir.mirExtImpl
                         SAWCruciblePersonality
          let simSt = Crucible.InitialState simctx globals Crucible.defaultAbortHandler retTy
          let fnCall = Crucible.regValue <$> Crucible.callFnVal (Crucible.HandleFnVal hf) regmap
          let overrideSim =
                do -- TODO RGS: Consider removing these putStrLns
                   liftIO $ putStrLn "registering standard overrides"
                   liftIO $ putStrLn "registering user-provided overrides"
                   mapM_ (registerOverride opts cc simctx top_loc mdMap)
                           (List.groupOn (view MS.csMethod) (map (view MS.psSpec) lemmas))
                   liftIO $ putStrLn "registering assumptions"
                   liftIO $
                     for_ assumes $ \(Crucible.LabeledPred p (md, reason)) ->
                       do expr <- resolveSAWPred cc p
                          let loc = MS.conditionLoc md
                          Crucible.addAssumption bak (Crucible.GenericAssumption loc reason expr)
                   liftIO $ putStrLn "simulating function"
                   fnCall
          Crucible.executeCrucible (map Crucible.genericToExecutionFeature feats)
            (simSt (Crucible.runOverrideSim retTy overrideSim))

     case res of
       Crucible.FinishedResult _ pr ->
         do Crucible.GlobalPair retval globals1 <-
              case pr of
                Crucible.TotalRes gp -> return gp
                Crucible.PartialRes _ _ gp _ ->
                  do printOutLn opts Info "Symbolic simulation completed with side conditions."
                     return gp
            let ret_ty = mspec ^. MS.csRet
            retval' <-
              case ret_ty of
                Nothing -> return Nothing
                Just ret_mt ->
                  case retval of
                    Crucible.RegEntry ty val ->
                      case decodeMIRVal col ret_mt (Crucible.AnyValue ty val) of
                        Nothing -> error $ "FIXME: Unsupported return type: " ++ show ret_ty
                        Just v -> return (Just (ret_mt, v))
            return (retval', globals1)

       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppMIRAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

       Crucible.TimeoutResult _cxt -> fail "Symbolic execution timed out."

  where
    prepareArg :: forall tp. Crucible.TypeRepr tp -> MIRVal -> IO (Crucible.RegValue Sym tp)
    prepareArg ty (MIRVal vTy vVal) =
      case testEquality ty (shapeType vTy) of
        Just Refl -> pure vVal
        Nothing   -> fail "argument type mismatch"

    prepareArgs ::
      forall xs.
      Ctx.Assignment Crucible.TypeRepr xs ->
      [MIRVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx xs | length xs /= Ctx.sizeInt (Ctx.size ctx) =
      fail $ "Wrong number of arguments: found " ++ show (length xs) ++ ", expected " ++ show (Ctx.sizeInt (Ctx.size ctx))
    prepareArgs ctx xs =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do v <- prepareArg tr (xs !! Ctx.indexVal idx)
           return (Crucible.RegEntry tr v))
      ctx

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Returns the Cryptol type of a MIR type, returning 'Nothing' if it is not
-- easily expressible in Cryptol's type system or if it is not currently
-- supported.
cryptolTypeOfActual :: Mir.Ty -> Maybe Cryptol.Type
cryptolTypeOfActual mty =
  case mty of
    Mir.TyBool      -> Just Cryptol.tBit
    Mir.TyChar      -> Just $ Cryptol.tWord $ Cryptol.tNum (32 :: Integer)
    Mir.TyUint bs   -> baseSizeType bs
    Mir.TyInt  bs   -> baseSizeType bs
    Mir.TyArray t n -> Cryptol.tSeq (Cryptol.tNum n) <$> cryptolTypeOfActual t
    Mir.TyTuple tys -> Cryptol.tTuple <$> traverse cryptolTypeOfActual tys

    Mir.TyFloat _      -> Nothing
    Mir.TyStr          -> Nothing
    Mir.TyAdt _ _ _    -> Nothing
    Mir.TyRef _ _      -> Nothing
    Mir.TyFnDef _      -> Nothing
    Mir.TyFnPtr _      -> Nothing
    Mir.TyRawPtr _ _   -> Nothing
    Mir.TyClosure _    -> Nothing
    Mir.TySlice _      -> Nothing
    Mir.TyDowncast _ _ -> Nothing
    Mir.TyNever        -> Nothing
    Mir.TyForeign      -> Nothing
    Mir.TyLifetime     -> Nothing
    Mir.TyConst        -> Nothing
    Mir.TyErased       -> Nothing
    Mir.TyInterned _   -> Nothing
    Mir.TyDynamic _    -> Nothing
  where
    baseSizeType :: Mir.BaseSize -> Maybe Cryptol.Type
    baseSizeType Mir.B8    = Just $ Cryptol.tWord $ Cryptol.tNum (8 :: Integer)
    baseSizeType Mir.B16   = Just $ Cryptol.tWord $ Cryptol.tNum (16 :: Integer)
    baseSizeType Mir.B32   = Just $ Cryptol.tWord $ Cryptol.tNum (32 :: Integer)
    baseSizeType Mir.B64   = Just $ Cryptol.tWord $ Cryptol.tNum (64 :: Integer)
    baseSizeType Mir.B128  = Just $ Cryptol.tWord $ Cryptol.tNum (128 :: Integer)
    baseSizeType Mir.USize = Just $ Cryptol.tWord $ Cryptol.tNum $ natValue $ knownNat @Mir.SizeBits

setupCrucibleContext :: RustModule -> TopLevel MIRCrucibleContext
setupCrucibleContext rm =
  do halloc <- getHandleAlloc
     sc <- getSharedContext
     pathSatSolver <- gets rwPathSatSolver
     sym <- io $ newSAWCoreExprBuilder sc
     bak <- io $ newSAWCoreBackend pathSatSolver sym
     opts <- getOptions
     -- TODO RGS: Sigh, this is copy-pasted. File an issue about this.
     io $ do let cfg = W4.getConfiguration sym
             verbSetting <- W4.getOptionSetting W4.verbosity cfg
             _ <- W4.setOpt verbSetting $ toInteger $ simVerbose opts
             return ()

     -- TODO! there's a lot of options setup we need to replicate
     --  from SAWScript.Crucible.LLVM.Builtins

     return MIRCrucibleContext { _mccRustModule = rm
                               , _mccBackend = bak
                               , _mccHandleAllocator = halloc
                               }

--------------------------------------------------------------------------------
-- Errors
--------------------------------------------------------------------------------

data MIRSetupError
  = MIRFreshVarInvalidType Mir.Ty
  | MIRArgTypeMismatch Int Mir.Ty Mir.Ty -- argument position, expected, found
  | MIRArgNumberWrong Int Int -- number expected, number found
  | MIRReturnUnexpected Mir.Ty -- found
  | MIRReturnTypeMismatch Mir.Ty Mir.Ty -- expected, found

instance X.Exception MIRSetupError where
  toException = topLevelExceptionToException
  fromException = topLevelExceptionFromException

instance Show MIRSetupError where
  show err =
    case err of
      MIRFreshVarInvalidType jty ->
        "mir_fresh_var: Invalid type: " ++ show jty
      MIRArgTypeMismatch i expected found ->
        unlines
        [ "mir_execute_func: Argument type mismatch"
        , "Argument position: " ++ show i
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]
      MIRArgNumberWrong expected found ->
        unlines
        [ "mir_execute_func: Wrong number of arguments"
        , "Expected: " ++ show expected
        , "Given: " ++ show found
        ]
      MIRReturnUnexpected found ->
        unlines
        [ "mir_return: Unexpected return value for void method"
        , "Given type: " ++ show found
        ]
      MIRReturnTypeMismatch expected found ->
        unlines
        [ "mir_return: Return type mismatch"
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]
