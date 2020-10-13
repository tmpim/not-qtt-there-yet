{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Driver.Editor.Main where

import Check.TypeError

import Control.Monad.Trans.Control
import Control.Exception (SomeException, catch)
import Control.Concurrent.STM
import Control.Monad.Reader
import Control.Concurrent
import Control.Lens

import qualified Data.HashMap.Compat as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Sequence as Seq
import Data.HashMap.Compat (HashMap)
import qualified Data.Text.IO as T
import Data.HashSet ( HashSet )
import qualified Data.Text as T
import Data.Sequence (Seq)
import Data.Traversable
import Data.Foldable
import Data.Default
import Data.Aeson
import Data.IORef
import Data.Range
import Data.Void

import Driver.Editor.Refine
import Driver.Editor.Monad
import Driver.Query
import Driver.Rules

import qualified Language.Haskell.LSP.Control as Ctrl
import qualified Language.Haskell.LSP.Types.Lens as L
import qualified Language.Haskell.LSP.Messages as L
import qualified Language.Haskell.LSP.Core as Core
import qualified Language.Haskell.LSP.Types as L
import qualified Language.Haskell.LSP.Core as L
import qualified Language.Haskell.LSP.VFS as L
import Language.Haskell.LSP.Messages
import Language.Haskell.LSP.Core

import Presyntax.Lexer (ParseException(..))
import Presyntax (Var)

import Qtt.Pretty (prettify)
import Qtt

import qualified Rock

import Text.Megaparsec hiding (State)


runLSP :: IO ()
runLSP = do
  rin              <- atomically newTChan
  persistent       <- newIORef =<< emptyPState
  files            <- newIORef mempty
  errorBuckets     <- newMVar mempty
  pendingCallbacks <- newMVar mempty
  versions         <- newMVar mempty

  let
    callbacks =
      InitializeCallbacks
        { L.onConfigurationChange = const (pure ())
        , L.onInitialConfiguration = const (pure ())
        , L.onStartup = \funs -> do
            modifyIORef persistent $ \ps -> ps { psReport = \x -> liftIO (sendErrorLogS (L.sendFunc funs) (T.pack x)) }

            let
              reader p = L.getVirtualFileFunc funs (L.toNormalizedUri (L.filePathToUri p)) >>= \case
                Nothing -> liftIO (T.readFile p)
                Just t -> pure (L.virtualFileText t)

              rules' = Rock.writer (addErrorsToBucket errorBuckets)
                     $ Rock.traceFetch (traceFetch funs) (\_ _ -> pure ())
                     $ rules persistent files reader
              rules' :: Rock.Rules (Query Var)

              state = State funs errorBuckets pendingCallbacks versions


            let 
              start = runReaderT (messageHandler rules' rin) state
              loop =
                catch start $ \(e :: SomeException) -> do
                  -- TODO: Pop this up visibly
                  L.sendErrorLogS (L.sendFunc funs) (T.pack (show e))
                  L.sendErrorLogS (L.sendFunc funs) (T.pack "Restarting worker thread...")
                  loop
            _ <- forkIO loop
            pure Nothing
        }
  t <- Ctrl.run callbacks (lspHandlers rin) lspOptions Nothing
  print t

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
      , L.codeActionHandler = Just $ sendMessage . L.ReqCodeAction

      , L.hoverHandler = Just $ sendMessage . L.ReqHover

      , L.didOpenTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidOpenTextDocument
      , L.didChangeTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidChangeTextDocument
      , L.didSaveTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidSaveTextDocument
      , L.didCloseTextDocumentNotificationHandler = Just $ sendMessage . L.NotDidCloseTextDocument

      , L.executeCommandHandler = Just $ sendMessage . L.ReqExecuteCommand
      }
  where sendMessage = atomically . writeTChan chan

lspOptions :: L.Options
lspOptions = def { Core.textDocumentSync = Just syncOptions
                 , Core.executeCommandCommands = Just [T.pack "qtt:refresh"]
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


messageHandler :: Rock.Rules (Query Var) -> TChan FromClientMessage -> ReaderT State IO ()
messageHandler rules chan = do
  t <- ask
  forever $ do
    msg <- liftIO $ atomically (readTChan chan)
    liftIO . Rock.runTask rules . flip runReaderT t $ do
      logInfo ("Responding to: " ++ show msg)
      handleRequest msg

unsolvedMetavariables :: QttM [L.Diagnostic]
unsolvedMetavariables = do
  t <- liftIO . readMVar =<< Rock.fetch UnsolvedMetas
  for (HashSet.toList t) $ \meta -> do
    zonked <- Rock.fetch (Zonked (metaGoal meta))
    let msg = T.unlines [ "Unsolved metavariable of type " <> T.pack (show zonked) ]
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
handleRequest (NotDidOpenTextDocument not)   = handleFileChange Nothing not
handleRequest (NotDidChangeTextDocument not) = handleFileChange vers not where
  vers = not ^. L.params . L.textDocument . L.version
handleRequest (NotDidSaveTextDocument not)   = handleFileChange Nothing not

handleRequest (ReqCodeAction msg) = handleCodeActionRequest msg
handleRequest (ReqExecuteCommand msg) = do
  let params = msg ^. L.params
  case (params ^. L.command, params ^. L.arguments) of
    ("qtt:refresh", Just (L.List [fromJSON -> Success u])) -> do
      logInfo $ "Handling refresh command for " ++ show u
      let fakeNotif = L.DidSaveTextDocumentParams (L.TextDocumentIdentifier u)
      handleFileChange Nothing (L.NotificationMessage undefined undefined fakeNotif)
    _ -> error "Unknown command"

handleRequest (ReqHover msg) = do
  let
    uri = msg ^. L.params . L.textDocument . L.uri
  case L.uriToFilePath uri of
    Just fp -> do
      let pos = positionFromPosition fp (msg ^. L.params . L.position)
      t <- Rock.fetch (ModuleAnnot fp pos)
      logInfo $ "All intervals for position: " ++ show pos ++ ": " ++ show t
      case t of
        [] -> sendMessage msg L.RspHover Nothing
        _:_ -> do
          ty <- Rock.fetch (Zonked (last t))
          let markup = L.MarkupContent L.MkPlainText (T.pack (show (prettify mempty ty)))
          sendMessage msg L.RspHover (Just (L.Hover (L.HoverContents markup) Nothing))
    Nothing -> sendMessage msg L.RspHover Nothing

handleRequest _req = logInfo (show _req)

handleCodeActionRequest :: L.CodeActionRequest -> QttM ()
handleCodeActionRequest msg =
  let L.CodeActionParams{..} = msg ^. L.params in
  case L.uriToFilePath (_textDocument ^. L.uri) of
    Just fp -> do
      logInfo (show _textDocument)
      let range = rangeFromRange fp _range
      t <- liftIO . readMVar =<< Rock.fetch UnsolvedMetas
      let
        metaInRange m = includes (metaLocation m) range
        metas = toList (HashSet.filter metaInRange t)
      case metas of
        [x] -> do
          logInfo $ "Oferring refinements for " ++ show (metaGoal x)
          refinements <- offerRefinements (_textDocument ^. L.uri) (toList (_context ^. L.diagnostics)) x
          sendMessage msg L.RspCodeAction (L.List refinements)
        _ -> sendMessage msg L.RspCodeAction (L.List [])
    Nothing -> sendMessage msg L.RspCodeAction (L.List [])

handleFileChange :: (L.HasUri a1 L.Uri, L.HasTextDocument a2 a1, L.HasParams s a2)
                 => Maybe Int
                 -> s
                 -> QttM ()
handleFileChange version not = do
  let uri = not ^. L.params . L.textDocument . L.uri
  logInfo $ "Reloading " ++ show uri
  -- Invalidate unsolved metavariables:
  _ <- liftIO . flip swapMVar mempty =<< Rock.fetch UnsolvedMetas

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

      case version of
        Just x -> do
          vers <- asks stateVersions
          liftIO . modifyMVar_ vers $ pure . HashMap.insert uri x
        Nothing -> pure ()
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
