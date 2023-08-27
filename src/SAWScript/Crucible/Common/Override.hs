{- |
Module      : SAWScript.Crucible.Common.Override
Description : Language-neutral overrides
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.Override
  ( Pointer
  , Pointer'
  , OverrideState
  , OverrideState'(..)
  , osAsserts
  , osAssumes
  , osFree
  , osLocation
  , overrideGlobals
  , syminterface
  , setupValueSub
  , termSub
  , termEqs
  --
  , OverrideFailureReason(..)
  , ppOverrideFailureReason
  , OverrideFailure(..)
  , ppOverrideFailure
  --
  , OverrideMatcher
  , OverrideMatcher'(..)
  , throwOverrideMatcher
  , runOverrideMatcher
  , RO
  , RW
  , addTermEq
  , addAssert
  , addAssume
  , readGlobal
  , writeGlobal
  , failure
  , getSymInterface
  , enforceCompleteSubstitution
  , refreshTerms
  , OverrideWithPreconditions(..)
  , owpPreconditions
  , owpMethodSpec
  , partitionOWPsConcrete
  , partitionBySymbolicPreds
  , findFalsePreconditions
  , unsatPreconditions
  , ppConcreteFailure
  --
  , assignmentToList
  , MetadataMap
  ) where

import qualified Control.Exception as X
import           Control.Lens
import           Control.Monad (foldM, unless)
import           Control.Monad.Trans.State hiding (get, put)
import           Control.Monad.State.Class (MonadState(..))
import           Control.Monad.Error.Class (MonadError)
import           Control.Monad.Catch (MonadThrow)
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Data.Kind (Type)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))
import           Data.Set (Set)
import           Data.Typeable (Typeable)
import           Data.Void
import           GHC.Generics (Generic, Generic1)
import qualified Prettyprinter as PP

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some)
import           Data.Parameterized.TraversableFC (toListFC)

import           Verifier.SAW.SharedTerm as SAWVerifier
import           Verifier.SAW.TypedAST as SAWVerifier
import           Verifier.SAW.TypedTerm as SAWVerifier

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr, GlobalVar)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4

import           SAWScript.Exceptions
import           SAWScript.Crucible.Common (Backend, OnlineSolver, Sym)
import           SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Utils (bullets)

-- TODO, not sure this is the best place for this definition
type MetadataMap =
  Map (W4.SymAnnotation Sym W4.BaseBoolType) MS.ConditionMetadata

--------------------------------------------------------------------------------
-- ** OverrideState

type LabeledPred sym = W4.LabeledPred (W4.Pred sym) Crucible.SimError

type family Pointer' ext sym :: Type

type Pointer ext = Pointer' ext Sym

data OverrideState' sym ext = OverrideState
  { -- | Substitution for memory allocations
    _setupValueSub :: Map AllocIndex (Pointer' ext sym)

    -- | Substitution for SAW Core external constants
  , _termSub :: Map VarIndex Term

    -- | Equalities of SAW Core terms
  , _termEqs :: [(Term, ConditionMetadata, Crucible.SimError)]

    -- | Free variables available for unification
  , _osFree :: Set VarIndex

    -- | Accumulated assertions
  , _osAsserts :: [(ConditionMetadata, LabeledPred sym)]

    -- | Accumulated assumptions
  , _osAssumes :: [(ConditionMetadata, W4.Pred sym)]

    -- | Symbolic simulation state
  , _syminterface :: sym

    -- | Global variables
  , _overrideGlobals :: Crucible.SymGlobalState sym

    -- | Source location to associated with this override
  , _osLocation :: W4.ProgramLoc
  }

type OverrideState = OverrideState' Sym

makeLenses ''OverrideState'

-- | The initial override matching state starts with an empty substitution
-- and no assertions or assumptions.
initialState ::
  sym                           {- ^ simulator                      -} ->
  Crucible.SymGlobalState sym   {- ^ initial global variables       -} ->
  Map AllocIndex (Pointer' ext sym) {- ^ initial allocation substituion -} ->
  Map VarIndex Term             {- ^ initial term substituion       -} ->
  Set VarIndex                  {- ^ initial free terms             -} ->
  W4.ProgramLoc                 {- ^ location information for the override -} ->
  OverrideState' sym ext
initialState sym globals allocs terms free loc = OverrideState
  { _osAsserts       = []
  , _osAssumes       = []
  , _syminterface    = sym
  , _overrideGlobals = globals
  , _termSub         = terms
  , _termEqs         = []
  , _osFree          = free
  , _setupValueSub   = allocs
  , _osLocation      = loc
  }

--------------------------------------------------------------------------------
-- ** OverrideFailureReason

data OverrideFailureReason ext
  = AmbiguousPointsTos [MS.PointsTo ext]
  | AmbiguousVars [TypedExtCns]
  | BadTermMatch Term Term -- ^ simulated and specified terms did not match
  | BadPointerCast -- ^ Pointer required to process points-to
  | BadReturnSpecification (Some Crucible.TypeRepr)
    -- ^ type mismatch in return specification
  | NonlinearPatternNotSupported
  | BadEqualityComparison -- ^ Comparison on an undef value
  | BadPointerLoad (Either (MS.PointsTo ext) (PP.Doc Void)) (PP.Doc Void)
    -- ^ @loadRaw@ failed due to type error
  | StructuralMismatch (PP.Doc Void) (PP.Doc Void) (Maybe (ExtType ext)) (ExtType ext)
    -- ^
    -- * pretty-printed simulated value
    -- * pretty-printed specified value
    -- * type of specified value
    -- * type of simulated value

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => PP.Pretty (OverrideFailureReason ext) where
  pretty = ppOverrideFailureReason

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => Show (OverrideFailureReason ext) where
  show = show . PP.pretty

ppOverrideFailureReason ::
  ( PP.Pretty (ExtType ext)
  , PP.Pretty (MS.PointsTo ext)
  ) => OverrideFailureReason ext -> PP.Doc ann
ppOverrideFailureReason rsn = case rsn of
  AmbiguousPointsTos pts ->
    PP.vcat
    [ PP.pretty "LHS of points-to assertion(s) not reachable via points-tos from inputs/outputs:"
    , PP.indent 2 $ PP.vcat (map PP.pretty pts)
    ]
  AmbiguousVars vs ->
    PP.vcat
    [ PP.pretty "Fresh variable(s) not reachable via points-tos from function inputs/outputs:"
    , PP.indent 2 $ PP.vcat (map MS.ppTypedExtCns vs)
    ]
  BadTermMatch x y ->
    PP.vcat
    [ PP.pretty "terms do not match"
    , PP.indent 2 (PP.unAnnotate (ppTerm defaultPPOpts x))
    , PP.indent 2 (PP.unAnnotate (ppTerm defaultPPOpts y))
    ]
  BadPointerCast ->
    PP.pretty "bad pointer cast"
  BadReturnSpecification ty ->
    PP.vcat
    [ PP.pretty "Spec had no return value, but the function returns a value of type:"
    , PP.viaShow ty
    ]
  NonlinearPatternNotSupported ->
    PP.pretty "nonlinear pattern not supported"
  BadEqualityComparison ->
    PP.pretty "value containing `undef` compared for equality"
  BadPointerLoad pointsTo msg ->
    PP.vcat
    [ PP.pretty "error when loading through pointer that" PP.<+>
      PP.pretty "appeared in the override's points-to precondition(s):"
    , PP.pretty "Precondition:"
    , PP.indent 2 (either PP.pretty PP.unAnnotate pointsTo)
    , PP.pretty "Failure reason: "
    , PP.indent 2 (PP.unAnnotate msg) -- this can be long
    ]
  StructuralMismatch simVal setupVal setupValTy ty ->
    PP.vcat
    [ PP.pretty "could not match specified value with actual value:"
    , PP.vcat (map (PP.indent 2) $
              [ PP.pretty "actual (simulator) value:" PP.<+> PP.unAnnotate simVal
              , PP.pretty "specified value:         " PP.<+> PP.unAnnotate setupVal
              , PP.pretty "type of actual value:   " PP.<+> PP.pretty ty
              ] ++ let msg ty_ =
                         [PP.pretty "type of specified value:"
                          PP.<+> PP.pretty ty_]
                   in maybe [] msg setupValTy)
    ]

--------------------------------------------------------------------------------
-- ** OverrideFailure

data OverrideFailure ext = OF W4.ProgramLoc (OverrideFailureReason ext)

ppOverrideFailure :: ( PP.Pretty (ExtType ext)
                     , PP.Pretty (MS.PointsTo ext)
                     ) => OverrideFailure ext -> PP.Doc ann
ppOverrideFailure (OF loc rsn) =
  PP.vcat
  [ PP.pretty "at" PP.<+> PP.viaShow (W4.plSourceLoc loc) -- TODO: fix when what4 switches to prettyprinter
  , ppOverrideFailureReason rsn
  ]

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => PP.Pretty (OverrideFailure ext) where
  pretty = ppOverrideFailure

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => Show (OverrideFailure ext) where
  show = show . PP.pretty

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         , Typeable ext
         ) => X.Exception (OverrideFailure ext)

--------------------------------------------------------------------------------
-- ** OverrideMatcher

data RO
data RW

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher' sym ext rorw m a =
  OM (StateT (OverrideState' sym ext) (ExceptT (OverrideFailure ext) m) a)
  deriving (Applicative, Functor, Generic, Generic1, Monad, MonadIO, MonadThrow)

type OverrideMatcher ext rorw a = OverrideMatcher' Sym ext rorw IO a

instance Wrapped (OverrideMatcher' sym ext rorw m a) where

deriving instance Monad m => MonadState (OverrideState' sym ext) (OverrideMatcher' sym ext rorw m)
deriving instance Monad m => MonadError (OverrideFailure ext) (OverrideMatcher' sym ext rorw m)

instance MonadTrans (OverrideMatcher' sym ext rorw) where
    lift f = OM $ lift $ lift f

throwOverrideMatcher :: Monad m => String -> OverrideMatcher' sym ext rorw m a
throwOverrideMatcher msg = do
  loc <- use osLocation
  X.throw $ OverrideMatcherException loc msg

instance Monad m => Fail.MonadFail (OverrideMatcher' sym ext rorw m) where
  fail = throwOverrideMatcher

-- | "Run" function for OverrideMatcher. The final result and state
-- are returned. The state will contain the updated globals and substitutions
runOverrideMatcher ::
   Monad m =>
   sym                         {- ^ simulator                       -} ->
   Crucible.SymGlobalState sym {- ^ initial global variables        -} ->
   Map AllocIndex (Pointer' ext sym) {- ^ initial allocation substitution -} ->
   Map VarIndex Term           {- ^ initial term substitution       -} ->
   Set VarIndex                {- ^ initial free variables          -} ->
   W4.ProgramLoc               {- ^ override location information   -} ->
   OverrideMatcher' sym ext md m a {- ^ matching action                 -} ->
   m (Either (OverrideFailure ext) (a, OverrideState' sym ext))
runOverrideMatcher sym g a t free loc (OM m) =
  runExceptT (runStateT m (initialState sym g a t free loc))

addTermEq ::
  Term {- ^ term equality -} ->
  ConditionMetadata ->
  Crucible.SimError {- ^ reason   -} ->
  OverrideMatcher ext rorw ()
addTermEq t md r =
  OM (termEqs %= cons (t, md, r))

addAssert ::
  Monad m =>
  W4.Pred sym       {- ^ property -} ->
  ConditionMetadata ->
  Crucible.SimError {- ^ reason   -} ->
  OverrideMatcher' sym ext rorw m ()
addAssert p md r =
  OM (osAsserts %= cons (md,W4.LabeledPred p r))

addAssume ::
  Monad m =>
  W4.Pred sym       {- ^ property -} ->
  ConditionMetadata ->
  OverrideMatcher' sym ext rorw m ()
addAssume p md = OM (osAssumes %= cons (md,p))

readGlobal ::
  Monad m =>
  Crucible.GlobalVar tp ->
  OverrideMatcher' sym ext rorw m (Crucible.RegValue sym tp)
readGlobal k =
  do mb <- OM (uses overrideGlobals (Crucible.lookupGlobal k))
     case mb of
       Nothing -> throwOverrideMatcher ("No such global: " ++ show k)
       Just v  -> return v

writeGlobal ::
  Monad m =>
  Crucible.GlobalVar    tp ->
  Crucible.RegValue sym tp ->
  OverrideMatcher' sym ext RW m ()
writeGlobal k v = OM (overrideGlobals %= Crucible.insertGlobal k v)

-- | Abort the current computation by raising the given 'OverrideFailure'
-- exception.
failure ::
  Monad m =>
  W4.ProgramLoc ->
  OverrideFailureReason ext ->
  OverrideMatcher' sym ext md m a
failure loc e = OM (lift (throwE (OF loc e)))

getSymInterface :: Monad m => OverrideMatcher' sym ext md m sym
getSymInterface = OM (use syminterface)

-- | Verify that all of the fresh variables for the given
-- state spec have been "learned". If not, throws
-- 'AmbiguousVars' exception.
enforceCompleteSubstitution ::
  W4.ProgramLoc ->
  MS.StateSpec ext ->
  OverrideMatcher ext w ()
enforceCompleteSubstitution loc ss =

  do sub <- OM (use termSub)

     let -- predicate matches terms that are not covered by the computed
         -- term substitution
         isMissing tt = ecVarIndex (tecExt tt) `Map.notMember` sub

         -- list of all terms not covered by substitution
         missing = filter isMissing (view MS.csFreshVars ss)

     unless (null missing) (failure loc (AmbiguousVars missing))

-- | Allocate fresh variables for all of the "fresh" vars
-- used in this phase and add them to the term substitution.
refreshTerms ::
  SharedContext    {- ^ shared context -} ->
  MS.StateSpec ext {- ^ current phase spec -} ->
  OverrideMatcher ext w ()
refreshTerms sc ss =
  do extension <- Map.fromList <$> traverse freshenTerm (view MS.csFreshVars ss)
     OM (termSub %= Map.union extension)
  where
    freshenTerm (TypedExtCns _cty ec) =
      do ec' <- liftIO $ scFreshEC sc (toShortName (ecName ec)) (ecType ec)
         new <- liftIO $ scExtCns sc ec'
         return (ecVarIndex ec, new)

-- | An override packaged together with its preconditions, labeled with some
--   human-readable info about each condition.
data OverrideWithPreconditions ext =
  OverrideWithPreconditions
    { _owpPreconditions :: [(MS.ConditionMetadata, LabeledPred Sym)]
         -- ^ c.f. '_osAsserts'
    , _owpMethodSpec :: MS.CrucibleMethodSpecIR ext
    , owpState :: OverrideState ext
    }
  deriving (Generic)

makeLenses ''OverrideWithPreconditions

-- | Partition into three groups:
--   * Preconditions concretely succeed
--   * Preconditions concretely fail
--   * Preconditions are symbolic
partitionOWPsConcrete :: forall ext.
  Sym ->
  [OverrideWithPreconditions ext] ->
  IO ([OverrideWithPreconditions ext], [OverrideWithPreconditions ext], [OverrideWithPreconditions ext])
partitionOWPsConcrete sym =
  let trav = owpPreconditions . each . _2 . W4.labeledPred
  in W4.partitionByPredsM (Just sym) $
       foldlMOf trav (W4.andPred sym) (W4.truePred sym)

-- | Like 'W4.partitionByPreds', but partitions on solver responses, not just
--   concretized values.
partitionBySymbolicPreds ::
  (OnlineSolver solver, Foldable t) =>
  Backend solver {- ^ solver connection -} ->
  (a -> W4.Pred Sym) {- ^ how to extract predicates -} ->
  t a ->
  IO (Map Crucible.BranchResult [a])
partitionBySymbolicPreds sym getPred =
  let step mp a =
        Crucible.considerSatisfiability sym Nothing (getPred a) <&> \k ->
          Map.insertWith (++) k [a] mp
  in foldM step Map.empty

-- | Find individual preconditions that are symbolically false
--
-- We should probably be using unsat cores for this.
findFalsePreconditions ::
  OnlineSolver solver =>
  Backend solver ->
  OverrideWithPreconditions ext ->
  IO [(MS.ConditionMetadata, LabeledPred Sym)]
findFalsePreconditions bak owp =
  fromMaybe [] . Map.lookup (Crucible.NoBranch False) <$>
    partitionBySymbolicPreds bak (view (_2 . W4.labeledPred)) (owp ^. owpPreconditions)

-- | Is this group of predicates collectively unsatisfiable?
unsatPreconditions ::
  OnlineSolver solver =>
  Backend solver {- ^ solver connection -} ->
  Fold s (W4.Pred Sym) {- ^ how to extract predicates -} ->
  s {- ^ a container full of predicates -}->
  IO Bool
unsatPreconditions bak container getPreds = do
  let sym = Crucible.backendGetSym bak
  conj <- W4.andAllOf sym container getPreds
  Crucible.considerSatisfiability bak Nothing conj >>=
    \case
      Crucible.NoBranch False -> pure True
      _ -> pure False

-- | Print a message about failure of an override's preconditions
ppFailure ::
  (PP.Pretty (ExtType ext), PP.Pretty (MethodId ext)) =>
  OverrideWithPreconditions ext ->
  [LabeledPred Sym] ->
  PP.Doc ann
ppFailure owp false =
  PP.vcat
  [ MS.ppMethodSpec (owp ^. owpMethodSpec)
    -- TODO: remove viaShow when crucible switches to prettyprinter
  , bullets '*' (map (PP.viaShow . Crucible.ppSimError)
                  (false ^.. traverse . W4.labeledPredMsg))
  ]

-- | Print a message about concrete failure of an override's preconditions
--
-- Assumes that the override it's being passed does have concretely failing
-- preconditions. Otherwise, the error won't make much sense.
ppConcreteFailure ::
  (PP.Pretty (ExtType ext), PP.Pretty (MethodId ext)) =>
  OverrideWithPreconditions ext ->
  PP.Doc ann
ppConcreteFailure owp =
  let (_, false, _) =
        W4.partitionLabeledPreds (Proxy :: Proxy Sym) (map snd (owp ^. owpPreconditions))
  in ppFailure owp false

------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)
