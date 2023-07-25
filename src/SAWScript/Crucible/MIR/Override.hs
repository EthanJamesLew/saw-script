{-# LANGUAGE GADTs #-}

-- | TODO RGS: Docs
module SAWScript.Crucible.MIR.Override
  ( decodeMIRVal
  ) where

import Data.Parameterized.Some (Some(..))
import Data.Type.Equality (TestEquality(..), (:~:)(..))

import qualified Mir.Mir as Mir

import qualified Lang.Crucible.Simulator as Crucible

import SAWScript.Crucible.Common
import SAWScript.Crucible.MIR.ResolveSetupValue
import SAWScript.Crucible.MIR.TypeShape

decodeMIRVal :: Mir.Collection -> Mir.Ty -> Crucible.AnyValue Sym -> Maybe MIRVal
decodeMIRVal col ty (Crucible.AnyValue repr rv)
  | Some shp <- tyToShape col ty
  = case testEquality repr (shapeType shp) of
      Just Refl -> Just (MIRVal shp rv)
      Nothing   -> Nothing
