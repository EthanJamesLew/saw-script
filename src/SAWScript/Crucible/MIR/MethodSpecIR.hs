{-# Language DataKinds #-}
{-# Language OverloadedStrings #-}
{-# Language TemplateHaskell #-}
{-# Language TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

-- | TODO RGS: Docs
module SAWScript.Crucible.MIR.MethodSpecIR
  ( -- * @MirPointsTo@
    MirPointsTo(..)

    -- * @MirAllocSpec@
  , MirAllocSpec(..)
  , maType
  , maMutbl
  , maMirType
  , maLen

    -- * @MirPointer@
  , MirPointer(..)
  , mpType
  , mpRef

    -- * @MIRMethodSpec@
  , MIRMethodSpec
  ) where

import Control.Lens (makeLenses)
import Data.Parameterized.Classes
import Data.Parameterized.Some
import Data.Text (Text)
import qualified Prettyprinter as PP

import Lang.Crucible.Types
import Mir.DefId
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as MS

type instance MS.HasSetupNull MIR = 'False
type instance MS.HasSetupGlobal MIR = 'False
type instance MS.HasSetupStruct MIR = 'True
type instance MS.HasSetupArray MIR = 'True
type instance MS.HasSetupElem MIR = 'True
type instance MS.HasSetupField MIR = 'True
type instance MS.HasSetupCast MIR = 'False
type instance MS.HasSetupUnion MIR = 'False
type instance MS.HasSetupGlobalInitializer MIR = 'False

type instance MS.HasGhostState MIR = 'False

type instance MS.TypeName MIR = Text
type instance MS.ExtType MIR = M.Ty

type instance MS.MethodId MIR = DefId
type instance MS.AllocSpec MIR = Some MirAllocSpec
type instance MS.PointsTo MIR = MirPointsTo
type instance MS.ResolvedState MIR = ()
type instance MS.CastType MIR = ()

type instance MS.Codebase MIR = CollectionState

type instance MS.CrucibleContext MIR = ()

type instance MS.Pointer' MIR sym = Some (MirPointer sym)


data MirPointsTo = MirPointsTo MS.AllocIndex [MS.SetupValue MIR]
    deriving (Show)

instance PP.Pretty MirPointsTo where
    pretty (MirPointsTo alloc sv) = PP.parens $
        PP.pretty (show alloc) PP.<+> "->" PP.<+> PP.list (map MS.ppSetupValue sv)

data MirAllocSpec tp = MirAllocSpec
    { _maType :: TypeRepr tp
    , _maMutbl :: M.Mutability
    , _maMirType :: M.Ty
    , _maLen :: Int
    }
  deriving (Show)

instance ShowF MirAllocSpec where

data MirPointer sym tp = MirPointer
    { _mpType :: TypeRepr tp
    , _mpRef :: MirReferenceMux sym tp
    }

type MIRMethodSpec = MS.CrucibleMethodSpecIR MIR

makeLenses ''MirAllocSpec
makeLenses ''MirPointer
