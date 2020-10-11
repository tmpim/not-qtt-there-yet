{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Driver.LanguageServer.Main where

import qualified Language.Haskell.LSP.Control as Ctrl
import qualified Language.Haskell.LSP.Core as L
import qualified Language.Haskell.LSP.Messages as L
import qualified Language.Haskell.LSP.Types as L
import qualified Language.Haskell.LSP.Types.Lens as L
import qualified Language.Haskell.LSP.Core as Core
import Language.Haskell.LSP.Messages
import Language.Haskell.LSP.Core

import Control.Monad.IO.Class
import Control.Concurrent.STM
import Control.Concurrent
import Control.Monad
import Control.Lens

import qualified Data.HashSet as HashSet
import qualified Data.Text as T
import Data.Default
import Data.HashSet ( HashSet )
import Data.Range
import Data.IORef
import Data.Foldable

import Driver.Rules
import Driver.Query
import Check.TypeError

import Presyntax.Lexer (ParseException(..))
import Presyntax (Var)

import Text.Megaparsec.Pos

import qualified Rock
import Qtt
import Control.Monad.Trans.Control (control)
import Control.Exception (catch)
import Text.Megaparsec.Error
import Data.Void
import Text.Megaparsec hiding (State)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.HashMap.Compat (HashMap)
import qualified Data.HashMap.Compat as HashMap
import Control.Monad.Reader
import Data.Traversable

runLSP :: IO ()
runLSP = do
  rin        <- atomically newTChan
  persistent <- newIORef =<< emptyPState
  files      <- newIORef mempty
  errorBuckets <- newMVar (mempty :: HashMap FilePath (Seq L.Diagnostic))

  let
    callbacks =
      InitializeCallbacks
        { L.onConfigurationChange = const (pure ())
        , L.onInitialConfiguration = const (pure ())
        , L.onStartup = \funs -> do
            let
              rules' = Rock.writer (addErrorsToBucket errorBuckets)
                     $ Rock.traceFetch (traceFetch funs) (\_ _ -> pure ())
                     $ rules persistent files
              rules' :: Rock.Rules (Query Var)

              state = State funs errorBuckets
            _ <- forkIO (runReaderT (messageHandler rules' rin) state)
            pure Nothing
        }
  t <- Ctrl.run callbacks (lspHandlers rin) lspOptions Nothing
  print t

data State =
  State { stateFuns :: LspFuncs ()
        , stateErrs :: MVar (HashMap FilePath (Seq L.Diagnostic))
        }

type QttM = ReaderT State (Rock.Task (Query Var))

addErrorsToBucket :: MVar (HashMap FilePath (Seq L.Diagnostic)) -> Query Var a -> HashSet (TypeError Var, [Range]) -> Rock.Task (Query Var) ()
addErrorsToBucket var (ModuleEnv path) errs = do
  liftIO . modifyMVar_ var $ \map ->
    let t = errorToDiagnostic <$> Seq.fromList (HashSet.toList errs)
        go Nothing = pure t
        go (Just s) = pure (s <> t)
     in pure (HashMap.alter go path map)
addErrorsToBucket _ _ _ = pure ()

traceFetch :: LspFuncs () -> Rock.Writer (HashSet (TypeError Var, [Range])) (Query Var) a1 -> Rock.Task (Query Var) ()
traceFetch funs (Rock.Writer q) = liftIO (sendErrorLogS (L.sendFunc funs) (T.pack (show q)))

lspHandlers :: TChan FromClientMessage -> Handlers
lspHandlers chan =
  def { L.initializedHandler = Just $ sendMessage . L.NotInitialized
      , L.hoverHandler = Just $ sendMessage . L.ReqHover

      , L.didOpenTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidOpenTextDocument
      , L.didChangeTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidChangeTextDocument
      , L.didSaveTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidSaveTextDocument
      , L.didCloseTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidCloseTextDocument
      }
  where sendMessage = atomically . writeTChan chan

lspOptions :: L.Options
lspOptions = def { Core.textDocumentSync = Just syncOptions
                 }

syncOptions :: L.TextDocumentSyncOptions
syncOptions = L.TextDocumentSyncOptions
  { L._openClose         = Just True
  , L._change            = Just L.TdSyncIncremental
  , L._willSave          = Just False
  , L._willSaveWaitUntil = Just False
  , L._save              = Just $ L.SaveOptions $ Just False
  }

errorToDiagnostic :: Show a => (a, [Range]) -> L.Diagnostic
errorToDiagnostic (e, rs) =
  let
    r =
      case (filter (\r -> unPos (sourceColumn (rangeEnd r)) - unPos (sourceColumn (rangeStart r)) > 1) rs) of
        [] -> head rs
        x:_ -> x
   in L.Diagnostic { L._range = rangeToRange r
                   , L._severity = Just L.DsError
                   , L._code = Nothing
                   , L._source = Just "qtt"
                   , L._message = T.pack (show e)
                   , L._relatedInformation = Nothing
                   , L._tags = Nothing
                   }

rangeToRange :: Range -> L.Range
rangeToRange r = L.Range { _start = p2p (rangeStart r), _end = p2p (rangeEnd r) } where
  p2p :: SourcePos -> L.Position
  p2p s = L.Position { _line = unPos (sourceLine s) - 1, _character = unPos (sourceColumn s) - 1}

messageHandler :: Rock.Rules (Query Var) -> TChan FromClientMessage -> ReaderT State IO ()
messageHandler rules chan = do
  t <- ask
  forever $ do
    msg <- liftIO $ atomically (readTChan chan)
    liftIO $ Rock.runTask rules . flip runReaderT t $ do
      liftIO . flip swapMVar mempty =<< Rock.fetch UnsolvedMetas
      handleRequest msg
      -- maybePublishUnsolvedMetas lf

unsolvedMetavariables :: QttM [L.Diagnostic]
unsolvedMetavariables = do
  t <- liftIO . readMVar =<< Rock.fetch UnsolvedMetas
  for (HashSet.toList t) $ \meta -> do
    zonked <- Rock.fetch (Zonked (metaExpected meta))

    let dropT (Binder{Qtt.var = v}:bs) (VPi _ rng) = dropT bs (rng (valueVar v))
        dropT [] t = t
        dropT _ _ = undefined

        metaT = dropT (metaTelescope meta) zonked

    let
      msg = T.unlines [ "Unsolved metavariable of type " <> T.pack (show metaT) ]

    pure $
      L.Diagnostic { L._range = rangeToRange (metaLocation meta)
                   , L._severity = Just L.DsWarning
                   , L._code = Nothing
                   , L._source = Just "qtt"
                   , L._message = msg
                   , L._relatedInformation = Nothing
                   , L._tags = Nothing
                   }

rangeUri :: Range -> L.Uri
rangeUri = L.filePathToUri . rangeFile

handleRequest :: FromClientMessage -> QttM ()
handleRequest (NotDidOpenTextDocument not)   = handleFileChange not
handleRequest (NotDidChangeTextDocument not) = handleFileChange not
handleRequest (NotDidSaveTextDocument not)   = handleFileChange not

handleRequest _ = pure ()

handleFileChange :: (L.HasUri a1 L.Uri, L.HasTextDocument a2 a1, L.HasParams s a2)
                 => s
                 -> QttM ()
handleFileChange not = do
  let uri = not ^. L.params . L.textDocument . L.uri
  fn <- asks (L.sendFunc . stateFuns)
  liftIO $ L.sendErrorLogS fn "reloading"
  case L.uriToFilePath uri of
    Just fp -> guardParseError fp () $ do
      buckets <- asks stateErrs
      liftIO . modifyMVar_ buckets $
        pure . HashMap.insert fp mempty

      _ <- Rock.fetch (ModuleEnv fp)
      errs <- liftIO . modifyMVar buckets $ \map ->
        pure (HashMap.insert fp mempty map, maybe mempty id (HashMap.lookup fp map))

      metas <- unsolvedMetavariables
      publishDiagnostics (L.filePathToUri fp) (toList errs ++ metas)

      pure ()
    Nothing -> pure ()

guardParseError :: FilePath -> a -> QttM a -> QttM a
guardParseError fp def comp =
  control $ \runInIO ->
    catch (runInIO comp) $ \(ParseError e) -> runInIO $ do
      let file = sourceName (pstateSourcePos (bundlePosState e))
      when (file == fp) $
        publishDiagnostics (L.filePathToUri file) . snd $ foldr errorBundleToDiags (bundlePosState e, []) (bundleErrors e)
      pure def

errorBundleToDiags :: ParseError T.Text Void -> (PosState T.Text, [L.Diagnostic]) -> (PosState T.Text, [L.Diagnostic])
errorBundleToDiags err (state, list) =
  let (_, state') = reachOffset (errorOffset err) state
      sp_pos = pstateSourcePos state'
      diag = L.Diagnostic { L._range = rangeToRange (newRangeUnchecked sp_pos sp_pos)
                          , L._severity = Just L.DsError
                          , L._code = Nothing
                          , L._source = Just "qtt"
                          , L._message = T.pack (parseErrorTextPretty err)
                          , L._relatedInformation = Nothing
                          , L._tags = Nothing
                          }
   in (state', diag:list)

publishDiagnostics :: L.Uri -> [L.Diagnostic] -> QttM ()
publishDiagnostics here diagnostics = do
  fn <- asks (L.sendFunc . stateFuns)
  liftIO . fn $
    L.NotPublishDiagnostics $
    L.NotificationMessage "2.0" L.TextDocumentPublishDiagnostics $
    L.PublishDiagnosticsParams here (L.List diagnostics)