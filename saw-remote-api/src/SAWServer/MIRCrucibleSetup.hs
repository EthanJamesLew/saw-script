{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | TODO RGS: Docs
module SAWServer.MIRCrucibleSetup
  ( mirLoadModule
  , mirLoadModuleDescr
  ) where

import Data.Aeson (FromJSON(..), withObject, (.:))

import Mir.Generator

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer as Server
    ( ServerName(..),
      SAWState,
      setServerVal )
import SAWServer.OK ( OK, ok )
import SAWServer.TrackFile ( trackFile )

data MIRLoadModuleParams
  = MIRLoadModuleParams ServerName FilePath

instance FromJSON MIRLoadModuleParams where
  parseJSON =
    withObject "params for \"SAW/MIR/load module\"" $ \o ->
    MIRLoadModuleParams <$> o .: "name" <*> o .: "module name"

instance Doc.DescribedMethod MIRLoadModuleParams OK where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name to refer to the loaded module by later."])
    , ("module name",
       Doc.Paragraph [Doc.Text "The file containing the MIR module (as produced by mir-json) to load."])
    ]
  resultFieldDescription = []

mirLoadModuleDescr :: Doc.Block
mirLoadModuleDescr =
  Doc.Paragraph [Doc.Text "Load the specified MIR module."]

mirLoadModule :: MIRLoadModuleParams -> Argo.Command SAWState OK
mirLoadModule (MIRLoadModuleParams serverName fileName) = do
  let mirMod :: RustModule
      -- TODO RGS: Finish me
      mirMod = undefined

  setServerVal serverName mirMod
  trackFile fileName
  ok
