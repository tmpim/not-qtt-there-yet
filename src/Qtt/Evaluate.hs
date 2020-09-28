{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module Qtt.Evaluate where

import Control.Monad.Reader.Class (MonadReader, ask)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Concurrent

import Qtt.Environment
import Qtt

evaluate :: (MonadReader (Env a) m, Ord a) => Term a -> m (Value a)
evaluate (Elim a) = evaluateNeutral a
evaluate (Lam a b) = do
  env <- ask
  pure (VFn a (\arg -> evaluateArrow b (insertDecl a arg env)))
evaluate (Pi var a b) = do
  env <- ask
  a <- evaluate a
  pure (VPi var a (\arg -> evaluateArrow b (insertDecl var arg env)))
evaluate (Set i) = pure (VSet i)

evaluateArrow :: Ord a => Term a -> Env a -> Value a
evaluateArrow = evaluate

evaluateNeutral :: (MonadReader (Env a) m, Ord a) => Elim a -> m (Value a)
evaluateNeutral (Meta mv) = pure (VNe (NMeta mv))
evaluateNeutral (Cut a _) = evaluate a
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

zonk :: (MonadIO m, MonadReader (Env var) m, Ord var) => Value var -> m (Value var)
zonk (VNe n) = zonkNeutral n where
  zonkNeutral (NApp mv@(NMeta (MV _ mvar _blocked)) ts) = do
    t <- liftIO $ tryReadMVar mvar
    case t of
      Nothing -> VNe . NApp mv <$> traverse zonk ts
      Just t -> zonk =<< evaluate t
  zonkNeutral nm@(NMeta (MV _ mvar _blocked)) = do
    t <- liftIO $ tryReadMVar mvar
    case t of
      Nothing -> pure (VNe nm)
      Just t -> zonk =<< evaluate t
  zonkNeutral (NApp t ts) = do
    t <- zonkNeutral t
    ts <- traverse zonk ts
    pure (foldl (@@) t ts)
  zonkNeutral (NVar v) = pure (VNe (NVar v))
zonk (VPi var d r) = do
  let range = r (valueVar var)
  range <- quote <$> zonk range
  env <- ask
  VPi var <$> zonk d <*> pure (\arg -> evaluateArrow range (insertDecl var arg env))
zonk x = pure x