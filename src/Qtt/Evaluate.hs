{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module Qtt.Evaluate where

import Control.Monad.Reader.Class (MonadReader, ask)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Concurrent

import Qtt.Environment
import Qtt
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.Reader (ReaderT(runReaderT))

doEvaluate :: (MonadReader (Env a) m, Ord a, Show a) => Term a -> m (Value a)
doEvaluate (Elim a) = doEvaluateNeutral a
doEvaluate (Lam a b) = do
  env <- ask
  pure (VFn a (\arg -> doEvaluateArrow b (insertDecl a arg env)))
doEvaluate (Pi bind b) = do
  env <- ask
  bind <- (\d -> bind { domain = d }) <$> doEvaluate (domain bind)
  pure (VPi bind (\arg -> doEvaluateArrow b (insertDecl (var bind) arg env)))
doEvaluate Set  = pure VSet
doEvaluate Prop = pure VProp

doEvaluateArrow :: (Ord a, Show a) => Term a -> Env a -> Value a
doEvaluateArrow = doEvaluate

doEvaluateNeutral :: (MonadReader (Env a) m, Ord a, Show a) => Elim a -> m (Value a)
doEvaluateNeutral (Meta mv) = pure (VNe (NMeta mv))
doEvaluateNeutral (Cut a _) = doEvaluate a
doEvaluateNeutral (Con v) = pure (VNe (NCon v))
doEvaluateNeutral (Var v) = do
  c <- lookupValue v
  case c of
    Nothing -> pure (VNe (NVar v))
    Just val -> pure val
doEvaluateNeutral (App a b) = do
  fun <- doEvaluateNeutral a
  case fun of
    VFn _ k -> k <$> doEvaluate b
    VNe n -> do
      b <- doEvaluate b
      pure (VNe n @@ b)
    _ -> error "Type error during evaluation of neutral application"

zonk :: (MonadIO m, MonadReader (Env var) m, Ord var, Show var) => Value var -> m (Value var)
zonk (VNe n) = zonkNeutral n where
  zonkNeutral (NApp mv@(NMeta MV{..}) ts) = do
    t <- liftIO $ tryReadMVar metaSlot
    case t of
      Nothing -> VNe . NApp mv <$> traverse zonk ts
      Just t -> zonk $ flip (foldl (@@)) ts t
  zonkNeutral nm@(NMeta MV{..}) = do
    t <- liftIO $ tryReadMVar metaSlot
    case t of
      Nothing -> pure (VNe nm)
      Just t -> zonk t
  zonkNeutral (NApp t ts) = do
    t <- zonkNeutral t
    ts <- traverse zonk ts
    pure (foldl (@@) t ts)
  zonkNeutral (NVar v) = pure (VNe (NVar v))
  zonkNeutral (NCon v) = pure (VNe (NCon v))
zonk (VPi b r) = do
  b <- fmap (\d -> b { domain = d }) $ zonk (domain b)
  pure $ VPi b (\arg -> unsafeZonkDomain (r arg))
zonk (VFn v r) = do
  pure $ VFn v (\arg -> unsafeZonkDomain (r arg))
zonk x = pure x

-- | What can I say but "Yikes".
unsafeZonkDomain :: (Ord var, Show var) => Value var -> Value var
unsafeZonkDomain v = unsafePerformIO (runReaderT (zonk v) =<< emptyEnv mempty)