{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Override matching and application for MIR.
module SAWScript.Crucible.MIR.Override
  ( OverrideMatcher
  , OverrideMatcher'(..)
  , runOverrideMatcher

  , setupValueSub
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , methodSpecHandler
  , decodeMIRVal
  ) where

import qualified Control.Exception as X
import Control.Lens
import Control.Monad (filterM, forM, forM_, zipWithM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State (StateT(..))
import Data.Either (partitionEithers)
import qualified Data.Foldable as F
import Data.Foldable (for_, traverse_)
import qualified Data.Functor.Product as Functor
import Data.IORef (IORef, modifyIORef)
import Data.List (tails)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (catMaybes)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Set as Set
import qualified Data.Vector as V
import Data.Void (absurd)
import qualified Prettyprinter as PP

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Mir.Generator as Mir
import qualified Mir.Intrinsics as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
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
import SAWScript.Utils (bullets, handleException)

-- A few convenient synonyms
type SetupValue = MS.SetupValue MIR
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR MIR
type StateSpec = MS.StateSpec MIR
type SetupCondition = MS.SetupCondition MIR

assertTermEqualities ::
  SharedContext ->
  MIRCrucibleContext ->
  OverrideMatcher MIR md ()
assertTermEqualities sc cc = do
  let assertTermEquality (t, md, e) = do
        p <- instantiateExtResolveSAWPred sc cc t
        addAssert p md e
  traverse_ assertTermEquality =<< OM (use termEqs)

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

computeReturnValue ::
  Options                     {- ^ saw script debug and print options     -} ->
  MIRCrucibleContext          {- ^ context of the crucible simulation     -} ->
  SharedContext               {- ^ context for generating saw terms       -} ->
  MS.CrucibleMethodSpecIR MIR {- ^ method specification                   -} ->
  Crucible.TypeRepr ret       {- ^ representation of function return type -} ->
  Maybe SetupValue            {- ^ optional symbolic return value         -} ->
  OverrideMatcher MIR md (Crucible.RegValue Sym ret)
                              {- ^ concrete return value                  -}
computeReturnValue opts cc sc spec ty mbVal =
  case mbVal of
    Nothing ->
      case ty of
        Crucible.UnitRepr -> return ()
        _ -> fail_
    Just val -> do
      MIRVal shp val' <- resolveSetupValueMIR opts cc sc spec val
      case W4.testEquality ty (shapeType shp) of
        Just Refl -> pure val'
        Nothing   -> fail_
  where
    fail_ = failure (spec ^. MS.csLoc) (BadReturnSpecification (Some ty))

decodeMIRVal :: Mir.Collection -> Mir.Ty -> Crucible.AnyValue Sym -> Maybe MIRVal
decodeMIRVal col ty (Crucible.AnyValue repr rv)
  | Some shp <- tyToShape col ty
  = case W4.testEquality repr (shapeType shp) of
      Just Refl -> Just (MIRVal shp rv)
      Nothing   -> Nothing

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

-- | Perform an allocation as indicated by a 'mir_alloc'
-- statement from the postcondition section.
executeAllocation ::
  Options ->
  MIRCrucibleContext ->
  (AllocIndex, Some MirAllocSpec) ->
  OverrideMatcher MIR w ()
executeAllocation opts cc (var, someAlloc@(Some alloc)) =
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show alloc]
     globals <- OM (use overrideGlobals)
     (ptr, globals') <- liftIO $ runStateT (doAlloc cc someAlloc) globals
     OM (overrideGlobals .= globals')
     assignVar cc (alloc^.maConditionMetadata) var ptr

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  MirPointsTo ->
  OverrideMatcher MIR w ()
executePointsTo _opts _sc cc spec pt = do
  env <- OM (use setupValueSub)
  globals <- OM (use overrideGlobals)
  globals' <- liftIO $ doPointsTo spec cc env globals pt
  OM (overrideGlobals .= globals')

-- execute a pre/post condition
executeCond ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  StateSpec ->
  OverrideMatcher MIR w ()
executeCond opts sc cc cs ss =
  do refreshTerms sc ss
     traverse_ (executeAllocation opts cc) (Map.assocs (ss ^. MS.csAllocs))
     traverse_ (executePointsTo opts sc cc cs) (ss ^. MS.csPointsTos)
     traverse_ (executeSetupCondition opts sc cc cs) (ss ^. MS.csConditions)

-- | Process a "mir_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Options                                          ->
  SharedContext                                    ->
  MIRCrucibleContext                               ->
  CrucibleMethodSpecIR                             ->
  MS.ConditionMetadata ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher MIR w ()
executeEqual opts sc cc spec md v1 v2 =
  do val1 <- resolveSetupValueMIR opts cc sc spec v1
     val2 <- resolveSetupValueMIR opts cc sc spec v2
     p <- liftIO (equalValsPred cc val1 val2)
     addAssume p md

-- | Process a "mir_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext   ->
  MIRCrucibleContext ->
  MS.ConditionMetadata ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher MIR w ()
executePred sc cc md tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveBoolTerm (cc ^. mccSym) t
     addAssume p md

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  Options                    ->
  SharedContext              ->
  MIRCrucibleContext         ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher MIR w ()
executeSetupCondition opts sc cc spec (MS.SetupCond_Equal md val1 val2) = executeEqual opts sc cc spec md val1 val2
executeSetupCondition _    sc cc _    (MS.SetupCond_Pred md tm)         = executePred sc cc md tm
executeSetupCondition _    _  _  _    (MS.SetupCond_Ghost empty _ _ _)  = absurd empty

handleSingleOverrideBranch :: forall rtp args ret.
  Options            {- ^ output/verbosity options                      -} ->
  SharedContext      {- ^ context for constructing SAW terms            -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible         -} ->
  W4.ProgramLoc      {- ^ Location of the call site for error reporting -} ->
  IORef MetadataMap ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  OverrideWithPreconditions MIR ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret
     (Crucible.RegValue Sym ret)
handleSingleOverrideBranch opts sc cc call_loc mdMap h (OverrideWithPreconditions preconds cs st) =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = cs ^. MS.csMethod
  let retTy = Crucible.handleReturnType h

  liftIO $ printOutLn opts Info $ unwords
    [ "Found a single potential override for"
    , show fnName
    ]

  -- First assert the override preconditions
  liftIO $ forM_ preconds $ \(md,W4.LabeledPred p r) ->
    do (ann,p') <- W4.annotateTerm sym p
       let caller = unwords ["Override called from:", show (W4.plSourceLoc call_loc)]
       let md' = md{ MS.conditionContext = MS.conditionContext md ++ caller }
       modifyIORef mdMap (Map.insert ann md')
       Crucible.addAssertion bak (Crucible.LabeledPred p' r)

  g <- Crucible.readGlobals
  res <- liftIO $ runOverrideMatcher sym g
     (st^.setupValueSub)
     (st^.termSub)
     (st^.osFree)
     (st^.osLocation)
     (methodSpecHandler_poststate opts sc cc retTy cs)
  case res of
    Left (OF loc rsn)  ->
      -- TODO, better pretty printing for reasons
      liftIO
        $ Crucible.abortExecBecause
        $ Crucible.AssertionFailure
        $ Crucible.SimError loc
        $ Crucible.AssertFailureSimError "assumed false" (show rsn)
    Right (ret,st') ->
      do liftIO $ forM_ (st'^.osAssumes) $ \(_md,asum) ->
           Crucible.addAssumption bak
            $ Crucible.GenericAssumption (st^.osLocation) "override postcondition" asum
         Crucible.writeGlobals (st'^.overrideGlobals)
         Crucible.overrideReturn' (Crucible.RegEntry retTy ret)

handleOverrideBranches :: forall rtp args ret.
  Options            {- ^ output/verbosity options                      -} ->
  SharedContext      {- ^ context for constructing SAW terms            -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible         -} ->
  W4.ProgramLoc      {- ^ Location of the call site for error reporting -} ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR MIR)
    {- ^ specification for current function override -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  [OverrideWithPreconditions MIR] ->
  ([OverrideWithPreconditions MIR],[OverrideWithPreconditions MIR],[OverrideWithPreconditions MIR]) ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret
     (Crucible.RegValue Sym ret)

handleOverrideBranches opts sc cc call_loc css h branches (true, false, unknown) =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = show $ NE.head css ^. MS.csMethod
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- Collapse the preconditions to a single predicate
  branches' <- liftIO $ forM (true ++ unknown) $
    \(OverrideWithPreconditions preconds cs st) ->
      W4.andAllOf sym (folded . _2 . W4.labeledPred) preconds <&>
        \precond -> (precond, cs, st)

  -- Now use crucible's symbolic branching machinery to select between the branches.
  -- Essentially, we are doing an n-way if statement on the precondition predicates
  -- for each override, and selecting the first one whose preconditions hold.
  --
  -- Then, in the body of the branch, we run the poststate handler to update the
  -- memory state, compute return values and compute postcondition predicates.
  --
  -- For each override branch that doesn't fail outright, we assume the relevant
  -- postconditions, update the crucible global variable state, and return the
  -- computed return value.
  --
  -- We add a final default branch that simply fails unless some previous override
  -- branch has already succeeded.
  liftIO $ printOutLn opts Info $ unwords
    [ "Branching on"
    , show (length branches')
    , "override variants of"
    , fnName
    , "..."
    ]
  let retTy = Crucible.handleReturnType h
  res <- Crucible.regValue <$> Crucible.callOverride h
     (Crucible.mkOverride' "overrideBranches" retTy
       (Crucible.symbolicBranches Crucible.emptyRegMap $
         [ ( precond
           , do g <- Crucible.readGlobals
                res <- liftIO $ runOverrideMatcher sym g
                   (st^.setupValueSub)
                   (st^.termSub)
                   (st^.osFree)
                   (st^.osLocation)
                   (methodSpecHandler_poststate opts sc cc retTy cs)
                case res of
                  Left (OF loc rsn)  ->
                    -- TODO, better pretty printing for reasons
                    liftIO
                      $ Crucible.abortExecBecause
                      $ Crucible.AssertionFailure
                      $ Crucible.SimError loc
                      $ Crucible.AssertFailureSimError "assumed false" (show rsn)
                  Right (ret,st') ->
                    do liftIO $ forM_ (st'^.osAssumes) $ \(_md,asum) ->
                         Crucible.addAssumption bak
                          $ Crucible.GenericAssumption (st^.osLocation) "override postcondition" asum
                       Crucible.writeGlobals (st'^.overrideGlobals)
                       Crucible.overrideReturn' (Crucible.RegEntry retTy ret)
           , Just (W4.plSourceLoc (cs ^. MS.csLoc))
           )
         | (precond, cs, st) <- branches'
         ] ++
         [ let e prettyArgs symFalse unsat = show $ PP.vcat $ concat
                 [ [ PP.pretty $
                     "No override specification applies for " ++ fnName ++ "."
                   ]
                 , [ "Arguments:"
                   , bullets '-' prettyArgs
                   ]
                 , if | not (null false) ->
                        [ PP.vcat
                          [ PP.pretty (unwords
                              [ "The following overrides had some preconditions"
                              , "that failed concretely:"
                              ])
                          , bullets '-' (map ppConcreteFailure false)
                          ]
                        ]
                      -- See comment on ppSymbolicFailure: this needs more
                      -- examination to see if it's useful.
                      -- - | not (null symFalse) ->
                      --   [ PP.text (unwords
                      --       [ "The following overrides had some preconditions "
                      --       , "that failed symbolically:"
                      --       ]) PP.<$$> bullets '-' (map ppSymbolicFailure symFalse)
                      --   ]

                      -- Note that we only print these in case no override had
                      -- individually (concretely or symbolically) false
                      -- preconditions.
                      | not (null unsat) && null false && null symFalse ->
                        [ PP.vcat
                          [ PP.pretty (unwords
                            [ "The conjunction of these overrides' preconditions"
                            , "was unsatisfiable, meaning your override can never"
                            , "apply. You probably have unintentionally specified"
                            , "mutually exclusive/inconsistent preconditions."
                            ])
                          , bullets '-' (unsat ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                          ]
                        ]
                      | null false && null symFalse ->
                        [ PP.pretty (unwords
                            [ "No overrides had any single concretely or"
                            , "symbolically failing preconditions."
                            ])
                        ]
                      | otherwise -> []
                 , if | simVerbose opts < 3 ->
                        [ PP.pretty $ unwords
                          [ "Run SAW with --sim-verbose=3 to see a description"
                          , "of each override."
                          ]
                        ]
                      | otherwise ->
                        [ PP.vcat
                          [ "Here are the descriptions of each override:"
                          , bullets '-'
                            (branches ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                          ]
                        ]
                 ]
           in ( W4.truePred sym
              , liftIO $ do
                  -- Now that we're failing, do the additional work of figuring out
                  -- if any overrides had symbolically false preconditions
                  symFalse <- catMaybes <$> (forM unknown $ \owp ->
                    findFalsePreconditions bak owp <&>
                      \case
                        [] -> Nothing
                        ps -> Just (owp, ps))

                  prettyArgs <-
                    ppArgs sym cc (NE.head css) (Crucible.RegMap args)

                  unsat <-
                    filterM
                      (unsatPreconditions bak (owpPreconditions . each . _2 . W4.labeledPred))
                      branches

                  Crucible.addFailedAssertion bak
                    (Crucible.GenericSimError (e prettyArgs symFalse unsat))
              , Just (W4.plSourceLoc call_loc)
              )
         ]))
     (Crucible.RegMap args)
  liftIO $ printOutLn opts Info $ unwords ["Applied override!", fnName]
  return res

instantiateExtResolveSAWPred ::
  SharedContext ->
  MIRCrucibleContext ->
  Term ->
  OverrideMatcher MIR md (W4.Pred Sym)
instantiateExtResolveSAWPred sc cc cond = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWPred cc =<< scInstantiateExt sc sub cond

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
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
     assertTermEqualities sc cc
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss

-- | Process a "mir_equal" statement from the precondition
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
     let name = "equality " ++ MS.stateCond prepost
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
learnPointsTo opts sc cc spec prepost (MirPointsTo md allocIdx referents) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule . Mir.rmCS ^. Mir.collection
     globals <- OM (use overrideGlobals)
     Some mp <- resolveAllocIndexMIR allocIdx
     let mpMirTy = mp^.mpMirType
     let mpTpr = tyToShapeEq col mpMirTy (mp^.mpType)
     val <- firstPointsToReferent referents
     v <- liftIO $ Mir.readMirRefIO bak globals Mir.mirIntrinsicTypes (mp^.mpType) (mp^.mpRef)
     matchArg opts sc cc spec prepost md (MIRVal mpTpr v) mpMirTy val

-- | Process a "mir_precond" statement from the precondition
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
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError (MS.stateCond prepost) ""))

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

matchArg opts sc cc cs _prepost md actual@(MIRVal (RefShape _refTy pointeeTy mutbl tpr) ref) expectedTy setupval =
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
    checkPointsTo (MirPointsTo _ allocIdx _) = checkAllocIndex allocIdx

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
                  [ "Literal equality " ++ MS.stateCond prepost
--                  , "Expected term: " ++ prettyTerm expect
--                  , "Actual term:   " ++ prettyTerm real
                  ]
            addTermEq t md $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

-- | This function is responsible for implementing the \"override\" behavior
--   of method specifications.  The main work done in this function to manage
--   the process of selecting between several possible different override
--   specifications that could apply.  We want a proof to succeed if _any_
--   choice of method spec allows the proof to go through, which is a slightly
--   awkward thing to fit into the symbolic simulation framework.
--
--   The main work of determining the preconditions, postconditions, memory
--   updates and return value for a single specification is done by
--   the @methodSpecHandler_prestate@ and @methodSpecHandler_poststate@ functions.
--
--   In a first phase, we attempt to apply the precondition portion of each of
--   the given method specifications.  Each of them that might apply generate
--   a substitution for the setup variables and a collection of preconditions
--   that guard the specification.  We use these preconditions to compute
--   a multiway symbolic branch, one for each override which might apply.
--
--   In the body of each of the individual branches, we compute the postcondition
--   actions of the corresponding method specification.  This will update memory
--   and compute function return values, in addition to assuming postcondition
--   predicates.
methodSpecHandler ::
  forall rtp args ret.
  (?singleOverrideSpecialCase :: Bool) =>
  Options            {- ^ output/verbosity options                     -} ->
  SharedContext      {- ^ context for constructing SAW terms           -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible        -} ->
  IORef MetadataMap ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR MIR)
    {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc mdMap css h =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = NE.head css ^. MS.csMethod
  call_loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ printOutLn opts Info $ unwords
    [ "Matching"
    , show (length css)
    , "overrides of "
    , show fnName
    , "..."
    ]
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- First, run the precondition matcher phase.  Collect together a list of the results.
  -- For each override, this will either be an error message, or a matcher state and
  -- a method spec.
  prestates <-
    do g0 <- Crucible.readGlobals
       forM css $ \cs -> liftIO $
         let initialFree = Set.fromList (map (ecVarIndex . tecExt)
                                           (view (MS.csPreState . MS.csFreshVars) cs))
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view MS.csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <-
    let prettyError methodSpec failureReason = do
          prettyArgs <- liftIO $ ppArgs sym cc methodSpec (Crucible.RegMap args)
          pure $
            PP.vcat
            [ MS.ppMethodSpec methodSpec
            , "Arguments:"
            , bullets '-' prettyArgs
            , ppOverrideFailure failureReason
            ]
    in
      case partitionEithers (F.toList prestates) of
          (errs, []) -> do
            msgs <-
              mapM (\(cs, err) ->
                      ("*" PP.<>) . PP.indent 2 <$> prettyError cs err)
                   (zip (F.toList css) errs)
            fail $ show $
              PP.vcat ["All overrides failed during structural matching:", PP.vcat msgs]
          (_, ss) -> liftIO $
            forM ss $ \(cs,st) ->
              return (OverrideWithPreconditions (st^.osAsserts) cs st)

  -- Now we do a second phase of simple compatibility checking: we check to see
  -- if any of the preconditions of the various overrides are concretely false.
  -- If so, there's no use in branching on them with @symbolicBranches@.
  (true, false, unknown) <- liftIO $ partitionOWPsConcrete sym branches

  -- Check if there is only a single override branch that might apply at this
  -- point.  If so, commit to it and handle that case specially. If there is
  -- more than one (or zero) branches that might apply, go to the general case.
  case true ++ unknown of
    [singleBranch] | ?singleOverrideSpecialCase ->
         handleSingleOverrideBranch opts sc cc call_loc mdMap h singleBranch
    _ -> handleOverrideBranches opts sc cc call_loc css h branches (true, false, unknown)

-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall ret w.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  MIRCrucibleContext       {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher MIR w (Crucible.RegValue Sym ret)
methodSpecHandler_poststate opts sc cc retTy cs =
  do executeCond opts sc cc cs (cs ^. MS.csPostState)
     computeReturnValue opts cc sc cs retTy (cs ^. MS.csRetValue)

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall ctx w.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  MIRCrucibleContext       {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher MIR w ()
methodSpecHandler_prestate opts sc cc args cs =
  do let expectedArgTypes = Map.elems (cs ^. MS.csArgBindings)
     let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
     let aux ::
           (Mir.Ty, SetupValue) -> Crucible.AnyValue Sym ->
           IO (MIRVal, Mir.Ty, SetupValue)
         aux (argTy, setupVal) val =
           case decodeMIRVal col argTy val of
             Just val' -> return (val', argTy, setupVal)
             Nothing -> fail "unexpected type"

     -- todo: fail if list lengths mismatch
     xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

     let md = MS.ConditionMetadata
              { MS.conditionLoc = cs ^. MS.csLoc
              , MS.conditionTags = mempty
              , MS.conditionType = "formal argument matching"
              , MS.conditionContext = ""
              }

     sequence_ [ matchArg opts sc cc cs MS.PreState md x y z | (x, y, z) <- xs]

     learnCond opts sc cc cs MS.PreState (cs ^. MS.csPreState)

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
mkStructuralMismatch _opts cc _sc spec mirVal setupval mty = do
  let sym = cc^.mccSym
  setupTy <- typeOfSetupValueMIR cc spec setupval
  pure $ StructuralMismatch
            (ppMIRVal sym mirVal)
            (MS.ppSetupValue setupval)
            (Just setupTy)
            mty

-- | Pretty-print the arguments passed to an override
ppArgs ::
  forall args ann.
  Sym ->
  MIRCrucibleContext          {- ^ context for interacting with Crucible        -} ->
  MS.CrucibleMethodSpecIR MIR {- ^ specification for current function override  -} ->
  Crucible.RegMap Sym args    {- ^ arguments from the simulator                 -} ->
  IO [PP.Doc ann]
ppArgs sym cc cs (Crucible.RegMap args) = do
  let expectedArgTypes = map fst (Map.elems (cs ^. MS.csArgBindings))
  let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
  let aux memTy (Crucible.AnyValue tyrep val) =
        MIRVal (tyToShapeEq col memTy tyrep) val
  let vals = zipWith aux expectedArgTypes (assignmentToList args)
  pure $ map (ppMIRVal sym) vals

resolveAllocIndexMIR :: AllocIndex -> OverrideMatcher MIR w (Some (MirPointer Sym))
resolveAllocIndexMIR i =
  do m <- OM (use setupValueSub)
     pure $ lookupAllocIndex m i

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

typeOfSetupValueMIR ::
  MIRCrucibleContext   ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher MIR w Mir.Ty
typeOfSetupValueMIR cc spec sval =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     liftIO $ typeOfSetupValue cc tyenv nameEnv sval

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
      |  n == 8, Just _ <- W4.testEquality w (W4.knownNat @8)
      -> liftIO (toSC sym st val)
      |  n == 16, Just _ <- W4.testEquality w (W4.knownNat @16)
      -> liftIO (toSC sym st val)
      |  n == 32, Just _ <- W4.testEquality w (W4.knownNat @32)
      -> liftIO (toSC sym st val)
      |  n == 64, Just _ <- W4.testEquality w (W4.knownNat @64)
      -> liftIO (toSC sym st val)
      |  n == 128, Just _ <- W4.testEquality w (W4.knownNat @128)
      -> liftIO (toSC sym st val)
    (Cryptol.TVTuple [], UnitShape _) ->
      liftIO (scUnitValue sc)
    (Cryptol.TVTuple tys, TupleShape _ _ flds)
      |  length tys == Ctx.sizeInt (Ctx.size flds)
      -> do terms <-
              traverse
                fieldToSC
                (zip tys (FC.toListFC Some (Ctx.zipWith Functor.Pair flds val)))
            liftIO (scTupleReduced sc terms)
    (Cryptol.TVSeq n cryty, ArrayShape _ _ arrShp)
      |  Mir.MirVector_Vector vals <- val
      ,  toInteger (V.length vals) == n
      -> do terms <- V.toList <$>
              traverse (\v -> valueToSC sym md failMsg cryty (MIRVal arrShp v)) vals
            t <- shapeToTerm sc arrShp
            liftIO (scVectorReduced sc t terms)
      |  Mir.MirVector_PartialVector vals <- val
      ,  toInteger (V.length vals) == n
      -> do let vals' = V.toList $
                  fmap (readMaybeType sym "vector element" (shapeType arrShp)) vals
            terms <-
              traverse (\v -> valueToSC sym md failMsg cryty (MIRVal arrShp v)) vals'
            t <- shapeToTerm sc arrShp
            liftIO (scVectorReduced sc t terms)
      |  Mir.MirVector_Array{} <- val
      -> fail "valueToSC: Symbolic arrays not supported"
    _ ->
      failure (MS.conditionLoc md) failMsg
  where
    st = sym ^. W4.userState
    sc = saw_ctx st

    fieldToSC ::
         (Cryptol.TValue, Some (Functor.Product FieldShape (Crucible.RegValue' Sym)))
      -> OverrideMatcher MIR w Term
    fieldToSC (ty, Some (Functor.Pair fldShp (Crucible.RV tm))) = do
      mirVal <-
        case fldShp of
          ReqField shp' ->
            pure $ MIRVal shp' tm
          OptField shp' ->
            let tm' = readMaybeType sym "field" (shapeType shp') tm in
            pure $ MIRVal shp' tm'
      valueToSC sym md failMsg ty mirVal
