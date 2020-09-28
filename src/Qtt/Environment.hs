{-# LANGUAGE FlexibleContexts #-}
module Qtt.Environment
  ( Env(..), emptyEnv
  , assume, envVariables
  , declare, insertDecl
  , lookupType
  , lookupValue
  ) where

import Control.Monad.Reader.Class (local, asks, MonadReader)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Concurrent (newMVar, MVar)

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)

import Qtt (Meta, Value)

data Env a =
  Env { assumptions   :: Map a (Value a)
      , declarations  :: Map a (Value a)
      , unsolvedMetas :: MVar (Set (Meta a))
      }

emptyEnv :: (MonadIO m, Ord a) => m (Env a)
emptyEnv = Env mempty mempty <$> liftIO (newMVar mempty)

assume :: (MonadReader (Env a) m, Ord a) => a -> Value a -> m b -> m b
assume x t = local (\env -> env { assumptions = Map.insert x t (assumptions env) })

envVariables :: Env a -> [a]
envVariables = Map.keys . assumptions

declare :: (MonadReader (Env a) m, Ord a) => a -> Value a -> Value a -> m b -> m b
declare x t val = local k where
  k env = env { assumptions = Map.insert x t (assumptions env)
              , declarations = Map.insert x val (declarations env)
              }

insertDecl :: Ord a => a -> Value a -> Env a -> Env a
insertDecl x val (Env a d metas) = Env a (Map.insert x val d) metas

lookupType :: (MonadReader (Env k) m, Ord k) => k -> m (Maybe (Value k))
lookupType var = asks (Map.lookup var . assumptions)

lookupValue :: (Ord a, MonadReader (Env a) m) => a -> m (Maybe (Value a))
lookupValue var = asks (Map.lookup var . declarations)