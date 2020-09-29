{-# LANGUAGE FlexibleContexts #-}
module Qtt.Environment
  ( Env(..), emptyEnv
  , assume, assuming, envVariables
  , declare, insertDecl
  , lookupType
  , lookupValue
  , withLocation
  ) where

import Control.Monad.Reader.Class (local, asks, MonadReader)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Concurrent (newMVar, MVar)

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Range

import Presyntax (L(..))

import Qtt

data Env a =
  Env { assumptions   :: Map a (Value a)
      , declarations  :: Map a (Value a)
      , unsolvedMetas :: MVar (Set (Meta a))
      , locationStack :: [Range]
      , unproven      :: Map a (L ())
      , toplevel      :: Set a
      }

emptyEnv :: (MonadIO m, Ord a) => m (Env a)
emptyEnv = do
  var <- liftIO (newMVar mempty)
  pure $ Env mempty mempty var mempty mempty mempty

assume :: (MonadReader (Env a) m, Ord a) => a -> Value a -> m b -> m b
assume x t = local (\env -> env { assumptions = Map.insert x t (assumptions env) })

assuming :: (MonadReader (Env a) m, Ord a) => [(a, Value a)] -> m b -> m b
assuming vars = local (\env -> env { assumptions = Map.union (assumptions env) (Map.fromList vars) })

envVariables :: Env a -> [a]
envVariables = Map.keys . assumptions

declare :: (MonadReader (Env a) m, Ord a) => a -> Value a -> Value a -> m b -> m b
declare x t val = local k where
  k env = env { assumptions = Map.insert x t (assumptions env)
              , declarations = Map.insert x val (declarations env)
              }

insertDecl :: Ord a => a -> Value a -> Env a -> Env a
insertDecl x val env = env { declarations = (Map.insert x val (declarations env)) }

lookupType :: (MonadReader (Env k) m, Ord k) => k -> m (Maybe (Value k))
lookupType var = asks (Map.lookup var . assumptions)

lookupValue :: (Ord a, MonadReader (Env a) m) => a -> m (Maybe (Value a))
lookupValue var = asks (Map.lookup var . declarations)

withLocation :: (MonadReader (Env a) m) => L x -> (x -> m b) -> m b
withLocation (L thing range) cont =
  local (\x -> x { locationStack = range:locationStack x}) (cont thing)
