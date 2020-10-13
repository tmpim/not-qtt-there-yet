{-# LANGUAGE NamedFieldPuns, DisambiguateRecordFields, OverloadedStrings #-}
module Driver.Editor.Refine where

import Control.Monad.Reader
import Control.Concurrent

import qualified Data.HashMap.Compat as HashMap
import qualified Data.Text as T
import Data.Maybe
import Data.Range

import Driver.Editor.Monad

import qualified Language.Haskell.LSP.Types as L

import Presyntax.Context
import Presyntax

import Qtt
import Qtt.Pretty (prettify)
import Check.Data (splitPi_pure)


offerRefinements :: L.Uri -> [L.Diagnostic] -> Meta Var -> QttM [L.CAResult]
offerRefinements uri diag meta = do
  versions <- liftIO . readMVar =<< asks stateVersions
  logInfo (show versions)
  let version = fromMaybe 0 $ HashMap.lookup uri versions
      range = rangeToRange (metaLocation meta)
      metaSpan = unPos (sourceColumn (rangeEnd (metaLocation meta)))
               - unPos (sourceColumn (rangeStart (metaLocation meta)))
  case splitPi_pure (metaGoal meta) of
    (b:binders, _) -> do
      let
        spaces = metaSpan - 1
        text = showsPrec (maybe 0 contextPrecedence (metaContext meta)) lambda ""
        lambda = prettify mempty (makeLams binders)

        makeLams :: [Binder x Var] -> Value Var
        makeLams []     = VFn (var b) (\_ -> valueVar (Intro "_"))
        makeLams (x:xs) = VFn (var x) (\_ -> makeLams xs)

        label =
          if length binders >= 1
            then "Introduce " <> T.pack (show (length binders + 1)) <> " lambda abstractions"
            else "Introduce lambda abstraction"

      pure [offerText label uri diag version (T.pack text <> T.replicate spaces (T.singleton ' ')) range]

    ([], t) -> refineVars t uri diag version range meta

type Refinement = L.Uri -> [L.Diagnostic] -> Int -> L.Range -> Meta Var -> QttM [L.CAResult]

refineVars :: Value Var -> Refinement
refineVars t uri diag version range meta = do
  let
    metaSpan = unPos (sourceColumn (rangeEnd (metaLocation meta)))
             - unPos (sourceColumn (rangeStart (metaLocation meta)))
    tele = metaTelescope meta
    candidates = filter (\Binder{visibility, domain} -> visibility == Visible && domain == t) tele
    go Binder{var} =
      let name = T.pack (show var)
          spaces = metaSpan - T.length name
       in offerText ("Use variable: " <> name) uri diag version (name <> T.replicate spaces (T.singleton ' ')) range
  pure (map go candidates)

offerText :: T.Text -> L.Uri -> [L.Diagnostic] -> Int -> T.Text -> L.Range -> L.CAResult
offerText title uri diag version text range =
  let
      action = L.CodeAction
        { L._title       = title
        , L._kind        = Nothing
        , L._diagnostics = Just (L.List diag)
        , L._edit        = Just edit
        , L._command     = Nothing
        }

      edit = L.WorkspaceEdit
        { L._changes = Just $ HashMap.fromList [ (uri, L.List [textEdit]) ]
        , L._documentChanges = Just $
            L.List [L.TextDocumentEdit
                      { L._textDocument = vtdi
                      , L._edits = L.List [textEdit]
                      }
                   ]
        }

      textEdit = L.TextEdit range text
      vtdi = L.VersionedTextDocumentIdentifier uri (Just version)
  in L.CACodeAction action