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
import Check.Fresh
import Data.Hashable
import Control.Comonad

evaluate :: (MonadReader (Env a) m, Ord a, Show a, Fresh a) => Term a -> m (Value a)
evaluate (Elim a) = evaluateNeutral a
evaluate (Lam a b) = do
  env <- ask
  pure (VFn a (\arg -> evaluateArrow b (insertDecl a arg env)))
evaluate (Pi bind b) = do
  env <- ask
  bind <- (\d -> bind { domain = d }) <$> evaluate (domain bind)
  pure (VPi bind (\arg -> evaluateArrow b (insertDecl (var bind) arg env)))
evaluate Set  = pure VSet
evaluate Prop = pure VProp
evaluate (SpannedTerm x) = evaluate (extract x)

evaluateArrow :: (Ord a, Show a, Fresh a) => Term a -> Env a -> Value a
evaluateArrow = evaluate

evaluateNeutral :: (MonadReader (Env a) m, Ord a, Show a, Fresh a) => Elim a -> m (Value a)
evaluateNeutral (Meta mv) = pure (VNe (NMeta mv))
evaluateNeutral (Cut a _) = evaluate a
evaluateNeutral (Con v) = pure (VNe (NCon v))
evaluateNeutral (Var v) = do
  c <- lookupValue v
  case c of
    Nothing -> pure (VNe (NVar v))
    Just val -> pure val
evaluateNeutral (App a b) = do
  fun <- evaluateNeutral a
  case fun of
    VFn _ k -> k <$> evaluate b
    VNe n -> do
      b <- evaluate b
      pure (VNe n @@ b)
    _ -> error "Type error during evaluation of neutral application"

zonk :: (MonadIO m, MonadReader (Env var) m, Ord var, Show var, Hashable var) => Value var -> m (Value var)
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
unsafeZonkDomain :: (Ord var, Show var, Hashable var) => Value var -> Value var
unsafeZonkDomain v = unsafePerformIO (runReaderT (zonk v) =<< emptyEnv mempty)