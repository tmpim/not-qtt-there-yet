{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Text.Megaparsec (sourceColumn, unPos, SourcePos(sourceLine))

import Control.Monad.Reader

import Control.Concurrent.IO
import Control.Concurrent
import Control.Exception (catch)

import qualified Data.Text.IO as T
import qualified Data.Text as T
import qualified Data.HashSet as HashSet
import Data.Foldable (for_)
import Data.IORef

import Data.Range

import Qtt.Environment

import Qtt.Pretty (prettify)
import Qtt

import System.Environment

import qualified Rock

import Driver.Rules (checkFile, rules)

import Driver.Query
import Presyntax

import Check.TypeError
import Check.Monad

import Prelude hiding (putStrLn, putStr, print)
import Data.HashSet (HashSet)
import Qtt.Builtin


main :: IO ()
main =
  do
    files <- getArgs

    memoMap <- newIORef mempty
    cycles <- newIORef mempty
    persistent <- newIORef =<< emptyPState

    let rules' =
          Rock.memoiseWithCycleDetection memoMap cycles
          $ Rock.writer reportError
          $ rules persistent files

    for_ files $ \f -> forkIO $ do
      print =<< Rock.runTask rules' (checkFile f)

    Rock.runTask rules' (reportUnsolved =<< Rock.fetch UnsolvedMetas)

  `catch` \case
    Tee e -> error $ "Internal error: " ++ show e
    Teer e (r:_) -> do
      lines <- T.lines <$> T.readFile (rangeFile r)
      _ <- printRange lines r
      print (e :: TypeError Var)
    Teer e _ -> error $ "Internal error: " ++ show e

reportError :: Query Var a2 -> HashSet (TypeError Var, [Range]) -> Rock.Task (Query Var) ()
reportError _ errs = do
  for_ (HashSet.toList errs) $ \(e, r) -> do
    fail <- builtinName <$> Rock.fetch (MakeBuiltin BuiltinFail)
    case e of
      NotEqual a b | isVarAlive fail (quote a) || isVarAlive fail (quote b) -> do
        pure ()
      _ -> do
        lines <- Rock.fetch (ModuleText (rangeFile (head r)))
        liftIO $ do
          _ <- printRange lines (head r)
          print (e :: TypeError Var)

traceReq :: Query Var a1 -> IO ()
traceReq v = do
  t <- myThreadId
  putStrLn $ "[" ++ show t ++ "]: " ++ show v

reportUnsolved :: HashSet.HashSet (Meta Var) -> Rock.Task (Query Var) ()
reportUnsolved = go . HashSet.toList where
  go :: [Meta Var] -> Rock.Task (Query Var) ()
  go [] = pure ()
  go (x:xs) = do
    let f = rangeFile (metaLocation x)
    lines <- Rock.fetch (ModuleText f)
    zonked <- Rock.fetch (Zonked (metaExpected x))

    liftIO $ do
      pad <- printRange lines (metaLocation x)

      let dropT (Binder{Qtt.var = v}:bs) (VPi _ rng) = dropT bs (rng (valueVar v))
          dropT [] t = t
          dropT _ _ = undefined

          metaT = dropT (metaTelescope x) zonked

      putStrLn $ T.unpack pad ++ "Unsolved metavariable with type: " ++ show (prettify mempty metaT)
    go xs

reportWithLines :: (MonadReader (Env a) m, MonadIO m) => [T.Text] -> String -> m ()
reportWithLines file s = do
  ~(loc:_) <- asks locationStack
  liftIO $ do
    putStrLn $ "Information: "
    p <- printRange file loc
    for_ (lines s) $ \l ->
      T.putStrLn (p <> T.pack l)

printRange :: [T.Text] -> Range -> IO T.Text
printRange lines r = do
  putStrLn $ rangeFile r ++ ":" ++ show (unPos (sourceLine (rangeStart r)))
  let l = unPos $ sourceLine (rangeStart r)
      padding = T.replicate (length (show l) + 1) (T.singleton ' ')
      line = T.cons ' ' (T.pack (show l)) <> T.pack " | "
      padded = padding <> T.pack " | "
  T.putStrLn padded
  T.putStrLn (line <> (lines !! (unPos (sourceLine (rangeStart r)) - 1)))
  T.putStrLn ( padded
            <> T.replicate (unPos (sourceColumn (rangeStart r)) - 1) (T.singleton ' ')
            <> T.replicate (unPos (sourceColumn (rangeEnd r)) - unPos (sourceColumn (rangeStart r))) (T.singleton '~')
             )
  pure (padding)