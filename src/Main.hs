{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Text.Megaparsec (sourceColumn, unPos, SourcePos(sourceLine))

import Control.Monad.Reader

import qualified Data.Text.IO as T
import qualified Data.Text as T

import Data.Range


import Qtt.Environment

import Data.Foldable (for_)

import System.Environment

import qualified Rock

import Driver.Rules (checkFile, rules)
import Driver.Query
import Data.IORef
import Presyntax
import Check.Monad
import Control.Exception (catch)
import Check.TypeError (TypeError)
import Qtt.Pretty


main :: IO ()
main =
  do
    (mod:vs) <- getArgs
    let files = [mod]

    memoMap <- newIORef mempty
    cycles <- newIORef mempty
    persistent <- newIORef =<< emptyPState

    let rules' = Rock.memoiseWithCycleDetection memoMap cycles (rules persistent files)

    print =<< Rock.runTask (Rock.traceFetch (liftIO . print) (\_ _ -> pure ()) rules') (checkFile mod)
    -- TODO: repl
    for_ vs $ \v -> do
      t <- Rock.runTask rules' (Rock.fetch (VariableType mod (Intro (T.pack v))))
      case t of
        Just t -> putStrLn $ v ++ " : " ++ show (prettify mempty t)
        _ -> putStrLn $ "Not in scope: " ++ v
  `catch` \case
    Tee e -> error $ "Internal error: " ++ show e
    Teer e (r:_) -> do
      lines <- T.lines <$> T.readFile (rangeFile r)
      _ <- printRange lines r
      print (e :: TypeError Var)
    Teer e _ -> error $ "Internal error: " ++ show e

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