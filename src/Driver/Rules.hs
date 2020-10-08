{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Driver.Rules where

import Check.TypeError
import Check.Monad
import Check

import Control.Monad.Reader (ask)
import Control.Monad.IO.Class
import Control.Concurrent

import qualified Data.IntervalMap.FingerTree as IntervalMap
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Text.IO as T
import qualified Data.Text as T
import Data.HashSet (HashSet)
import Data.IORef
import Data.Range
import Data.L

import Driver.WiredIn
import Driver.Query

import Presyntax.Parser (parseFileIO)
import Presyntax

import Qtt.Evaluate (zonk)
import Qtt.Environment
import Qtt

import Rock

type Errors = HashSet (TypeError Var, [Range])

rules :: IORef (PersistentState Var)
      -> IORef [String]
      -> (FilePath -> IO T.Text)
      -> GenRules (Writer Errors (Query Var))
                  (Query Var)
rules persistent files readFile (Rock.Writer q) = case q of
  GoalFiles -> noFail . liftIO $ readIORef files
  Persistent -> noFail $ pure persistent

  ModuleText file -> noFail $ do
    contents <- liftIO $ readFile file
    pure (T.lines contents)

  ModuleCode file -> noFail $ do
    lines <- T.unlines <$> Rock.fetch (ModuleText file)
    t <- liftIO (parseFileIO file lines)
    pure t

  ModuleMap path -> noFail $ do
    code <- Rock.fetch (ModuleCode path)
    pure (foldr addDefToMM (MM mempty mempty mempty mempty mempty) code)

  ModuleEnv path -> do
    code <- Rock.fetch (ModuleCode path)
    env <- emptyEnv path
    t <- runCheckerOrFail (checkProgram code ask) env
    case t of
      (Nothing, e) -> pure (env, e)
      (Just x, e) -> pure (x, e)

  ModuleAnnot path pos -> noFail $ do
    env <- Rock.fetch (ModuleEnv path)
    x <- liftIO $ tryReadMVar (interestingIntervals env)
    case x of
      Nothing -> pure []
      Just t -> pure $ map snd (IntervalMap.search pos t)

  UnsolvedMetas -> noFail . liftIO $ do
    p <- readIORef persistent 
    pure (psUnsolved p)

  Zonked v -> do
    t <- runCheckerOrFail (zonk v) =<< emptyEnv ""
    case t of
      (Nothing, e) -> error $ "Error in zonking: " ++ show e
      (Just x, _) -> pure (x, mempty)

  MakeBuiltin b -> noFail $ makeBuiltin b

noFail :: (Monoid w, Functor f) => f a -> f (a, w)
noFail = fmap (flip (,) mempty)

checkFile :: FilePath -> Rock.Task (Query Var) ()
checkFile path = do
  _ <- Rock.fetch (ModuleEnv path)
  pure ()

foldMapM :: (Applicative f, Monoid m, Foldable t) => (a -> f m) -> t a -> f m
foldMapM k = foldr (\a b -> (<>) <$> k a <*> b) (pure mempty)

findCon :: Var -> [(Var, Value Var, Value Var)] -> Maybe (Value Var, Value Var)
findCon _ [] = Nothing
findCon c ((c',v,v'):s)
  | c == c' = pure (v, v')
  | otherwise = findCon c s

runCheckerOrFail :: TCM Var a
                 -> Env Var
                 -> Rock.Task (Query Var)
                      (Maybe a, HashSet (TypeError Var, [Range]))
runCheckerOrFail c env = do
  pvar <- Rock.fetch Persistent
  recovered <- liftIO $ newMVar mempty
  p <- liftIO $ readIORef pvar
  e <- runChecker c env{ unsolvedMetas = psUnsolved p
                       , deferredEqns = psDeferred p
                       , recoveredErrors = recovered }
  case e of
    Left (err, span) -> pure (Nothing, HashSet.singleton (err, span))
    Right x -> do
      rec <- liftIO $ takeMVar recovered
      pure (Just x, rec)

addDefToMM :: L (Decl L Var) -> ModuleMap Var -> ModuleMap Var
addDefToMM (L (TypeSig v t) _) x =
  x { moduleTySigs = HashMap.insert v t (moduleTySigs x) }
addDefToMM (L (Value v t) _) x =
  x { moduleDecls = HashMap.insert v t (moduleDecls x) }
addDefToMM (L (DataStmt t) _) x =

  x { moduleData = HashMap.insert (dataName t) t (moduleData x)
    , moduleCons = HashMap.union (HashMap.fromList cons) (moduleCons x) }
  where
    cons = map (\(L (v, _) _) -> (v, t)) (dataConstructors t)
addDefToMM (L Include{} _) x = x

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