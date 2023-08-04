{-# LANGUAGE TypeOperators #-}

module Server where

import Control.Concurrent (threadDelay)
import Control.Exception (SomeException, catch)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Aeson qualified as Aeson
import Data.IORef
import Data.Text (Text)
import Data.Text qualified as Text
import Handlers (handlers)
import Language.LSP.Server
import Language.LSP.Types
import SAWT (SAWState, newSAWState)
import Server.Monad
import System.IO (hPrint, hPutStrLn, stderr)

run :: IO Int
run = runServer server -- `catch` handler
  where
    handler :: SomeException -> IO Int
    handler exn =
      do
        hPutStrLn stderr "server failed"
        hPrint stderr exn
        pure 56

server :: ServerDefinition Config
server =
  ServerDefinition
    { defaultConfig = emptyConfig,
      onConfigurationChange = onConfigurationChange',
      doInitialize = doInitialize',
      staticHandlers = handlers,
      interpretHandler = interpretHandler',
      options = options'
    }

onConfigurationChange' :: Config -> Aeson.Value -> Either Text Config
onConfigurationChange' _old v =
  do
    case Aeson.fromJSON v of
      Aeson.Error e -> Left (Text.pack e)
      Aeson.Success cfg -> Right cfg

doInitialize' ::
  LanguageContextEnv Config ->
  RequestMessage 'Initialize ->
  IO (Either ResponseError (ServerEnv, IORef SAWState))
doInitialize' env initMsg =
  do
    serverEnv <- newServerEnv env
    sawStateRef <- newSAWState >>= newIORef
    pure (Right (serverEnv, sawStateRef))

interpretHandler' :: (ServerEnv, IORef SAWState) -> (ServerM <~> IO)
interpretHandler' (serverEnv, sawStateRef) = Iso serverToIO ioToServer
  where
    serverToIO :: ServerM a -> IO a
    serverToIO action = runServerM' action serverEnv sawStateRef

    ioToServer :: IO a -> ServerM a
    ioToServer = liftIO

options' :: Options
options' = defaultOptions {textDocumentSync = Just tds}
  where
    tds =
      TextDocumentSyncOptions
        { _openClose = Just True,
          _change = Just TdSyncFull,
          _willSave = Just False,
          _willSaveWaitUntil = Just False,
          _save = Just (InR (SaveOptions {_includeText = Just True}))
        }
