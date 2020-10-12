{-# LANGUAGE FlexibleContexts #-}
module Driver.Editor.Monad where

import Control.Monad.Reader
import Control.Concurrent
import Control.Lens

import Data.HashMap.Strict (HashMap)
import qualified Data.Text as T
import Data.Sequence (Seq)
import Data.Range

import Driver.Query

import qualified Language.Haskell.LSP.Types.Lens as L
import qualified Language.Haskell.LSP.Messages as L
import qualified Language.Haskell.LSP.Types as L
import qualified Language.Haskell.LSP.Core as L
import Language.Haskell.LSP.Core (LspFuncs)

import Presyntax

import qualified Rock


data State =
  State { stateFuns             :: LspFuncs ()
        , stateErrs             :: MVar (HashMap FilePath (Seq L.Diagnostic))
        , statePendingCallbacks :: MVar (HashMap String (QttM ()))
        , stateVersions         :: MVar (HashMap L.Uri Int)
        }

type QttM = ReaderT State (Rock.Task (Query Var))

rangeToRange :: Range -> L.Range
rangeToRange r = L.Range { L._start = positionToPosition (rangeStart r), L._end = positionToPosition (rangeEnd r) } where

positionToPosition :: SourcePos -> L.Position
positionToPosition s = L.Position { L._line = unPos (sourceLine s) - 1, L._character = unPos (sourceColumn s) - 1}

rangeFromRange :: FilePath -> L.Range -> Range
rangeFromRange uri r = newRangeUnchecked (positionFromPosition uri (r ^. L.start)) (positionFromPosition uri (r ^. L.end))
  
positionFromPosition :: FilePath -> L.Position -> SourcePos
positionFromPosition uri s = SourcePos uri (mkPos (s ^. L.line + 1)) (mkPos (s ^. L.character + 1))

publishDiagnostics :: L.Uri -> [L.Diagnostic] -> QttM ()
publishDiagnostics here diagnostics = do
  logInfo $ "Publishing diagnostics: "
  _ <- traverse (logInfo . show) diagnostics
  sf <- asks (L.sendFunc . stateFuns)
  liftIO . sf $
    L.NotPublishDiagnostics $
    L.NotificationMessage (T.pack "2.0") L.TextDocumentPublishDiagnostics $
    L.PublishDiagnosticsParams here (L.List diagnostics)

sendMessage :: (MonadReader State m, MonadIO m)
            => L.RequestMessage L.ClientMethod req resp
            -> (L.ResponseMessage resp -> L.FromServerMessage) -> resp -> m ()
sendMessage msg k x = do
  fns <- asks stateFuns
  liftIO $ L.sendFunc fns $ k $ L.makeResponseMessage msg x

logInfo :: String -> QttM ()
logInfo s = do
  sf <- asks (L.sendFunc . stateFuns)
  liftIO . sf $ L.NotLogMessage $ L.fmServerLogMessageNotification L.MtInfo (T.pack s)