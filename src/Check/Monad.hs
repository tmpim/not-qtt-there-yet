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

import Data.Range
import qualified Data.Map.Strict as Map

type TypeCheck var m =
  ( Fresh var, Eq var, Ord var, Show var -- var is a variable type
  , MonadReader (Env var) m
  , MonadWriter (Seq (Constraint var)) m
  , MonadError (TypeError var, [Range]) m
  , MonadIO m
  )

defer :: TypeCheck var m => Meta var -> Seq (Value var) -> Value var -> m ()
defer m s r = tell (Seq.singleton (Equation m s r))

freshMeta :: (MonadReader (Env a) m, MonadIO m, Fresh a, Ord a) => Value a -> m (Value a)
freshMeta expected = do
  id <- fresh
  top <- asks toplevel
  tele <- asks (Map.toList . flip Map.withoutKeys top . assumptions)
  loc <- asks locationStack

  let quantify ((a, b):xs) t = VPi Binder{ visibility = Visible, domain = b, var = a } (\_ -> quantify xs t)
      quantify [] t = t

      teleify = map (\(a, b) -> Binder { visibility = Visible, domain = b, var = a })

  meta <- liftIO $ MV id -- metavariable identifier
               <$> newEmptyMVar -- metavariable solution
               <*> newMVar mempty -- eqns blocked on this meta
               <*> pure (head loc)
               <*> pure (quantify tele expected)
               <*> pure (teleify tele)

  unsolved <- asks unsolvedMetas
  liftIO . modifyMVar_ unsolved $ pure . Set.insert meta
  pure (VNe (NApp (NMeta meta) (fmap valueVar (Seq.fromList (map fst tele)))))

solveMeta :: TypeCheck a m => Meta a -> m ()
solveMeta meta = do
  unsolved <- asks unsolvedMetas
  liftIO . modifyMVar_ unsolved $ pure . Set.delete meta

newtype TCM var a = TCM { runChecker :: Env var -> IO (Either (TypeError var, [Range]) (a, Seq (Constraint var)))}
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (Env var)
           , MonadWriter (Seq (Constraint var))
           , MonadError (TypeError var, [Range])
           , MonadIO
           )
    via (ReaderT (Env var) (WriterT (Seq (Constraint var)) (ExceptT (TypeError var, [Range]) IO)))

getUnsolvedMetas :: TypeCheck var m => m (Set (Meta var))
getUnsolvedMetas = do
  mv <- asks unsolvedMetas
  t <- liftIO $ tryReadMVar mv
  pure $
    case t of
      Nothing -> mempty
      Just set -> set

typeError :: TypeCheck var m => TypeError var -> m b
typeError e = do
  c <- asks locationStack
  throwError (e, c)
