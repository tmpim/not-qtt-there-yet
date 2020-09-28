{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Check.Monad where

import Control.Monad.Writer.Strict
import Control.Concurrent (tryReadMVar, modifyMVar_, newMVar, newEmptyMVar)
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Sequence (Seq)
import Data.Set (Set)

import Qtt.Environment
import Qtt

import Check.TypeError
import Check.Fresh

type TypeCheck var m =
  ( Fresh var, Eq var, Ord var, Show var -- var is a variable type
  , MonadReader (Env var) m
  , MonadWriter (Seq (Equation var)) m
  , MonadError (TypeError var) m
  , MonadIO m
  )

defer :: TypeCheck var m => Meta var -> [Value var] -> Value var -> m ()
defer m s r = tell (Seq.singleton (Equation m s r))

freshMeta :: (MonadReader (Env a) m, MonadIO m, Fresh a, Ord a) => m (Value a)
freshMeta = do
  id <- fresh
  vars <- asks envVariables
  meta <- liftIO $ MV id -- metavariable identifier
               <$> newEmptyMVar -- metavariable solution
               <*> newMVar mempty -- eqns blocked on this meta
  unsolved <- asks unsolvedMetas
  liftIO . modifyMVar_ unsolved $ pure . Set.insert meta
  pure (VNe (NApp (NMeta meta) (map valueVar vars)))

solveMeta :: TypeCheck a m => Meta a -> m ()
solveMeta meta = do
  unsolved <- asks unsolvedMetas
  liftIO . modifyMVar_ unsolved $ pure . Set.delete meta

newtype TCM var a = TCM { runChecker :: Env var -> IO (Either (TypeError var) (a, Seq (Equation var)))}
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (Env var)
           , MonadWriter (Seq (Equation var))
           , MonadError (TypeError var)
           , MonadIO
           )
    via (ReaderT (Env var) (WriterT (Seq (Equation var)) (ExceptT (TypeError var) IO)))

getUnsolvedMetas :: TypeCheck var m => m (Set (Meta var))
getUnsolvedMetas = do
  mv <- asks unsolvedMetas
  t <- liftIO $ tryReadMVar mv
  pure $
    case t of
      Nothing -> mempty
      Just set -> set
