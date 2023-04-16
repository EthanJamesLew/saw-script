{-# LANGUAGE ImplicitParams #-}

-- | TODO RGS: Docs
module SAWScript.Crucible.MIR.Builtins
  ( mir_load_module
  ) where

import qualified Data.ByteString.Lazy as BSL

import Mir.Generator
import Mir.ParseTranslate

import SAWScript.Options
import SAWScript.Value

-- | TODO RGS: Docs
mir_load_module :: String -> TopLevel RustModule
mir_load_module inputFile = do
   b <- io $ BSL.readFile inputFile

   opts <- getOptions
   -- TODO RGS: Hmmmmmmmmmmmmmm
   --let ?assertFalseOnError = assertFalse mirOpts
   let ?assertFalseOnError = True
   let ?debug = simVerbose opts
   -- TODO RGS: Make this configurable?
   let ?printCrucible = False

   col <- io $ parseMIR inputFile b
   halloc <- getHandleAlloc
   io $ translateMIR mempty col halloc
