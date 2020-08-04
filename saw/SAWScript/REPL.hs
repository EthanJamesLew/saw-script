{- |
Module      : SAWScript.REPL
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.REPL (run) where

import SAWScript.Options (Options(..))
import SAWScript.REPL.Logo (displayLogo)
import SAWScript.REPL.Haskeline (repl)

-- | Main function
run :: Options -> IO ()
run opts = do
  displayLogo $ useColor opts
  repl Nothing opts (return ())
