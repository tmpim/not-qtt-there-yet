{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Qtt.Environment
  ( Env(..), emptyEnv, emptyEnvWithReporter
  , assume, assuming, envVariables
  , declare, insertDecl
  , addSubmodule
  , lookupType
  , lookupValue
  , withLocation
  
  , report
  ) where

import Control.Monad.Reader.Class (local, asks, MonadReader)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Concurrent (newMVar, MVar)

import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set
import Data.HashMap.Strict (HashMap)
import Data.Sequence
import Data.HashSet (HashSet)
import Data.Range

import Presyntax (L(..))

import Qtt
import Check.Fresh
import Data.Hashable

data Env a =
  Env
    { assumptions   :: HashMap a (Value a)
    , declarations  :: HashMap a (Value a)
    , modules       :: HashMap a (Env a)
    , locationStack :: [Range]
    , unproven      :: HashMap a (L ())
    , toplevel      :: HashSet a
    , constructors  :: HashSet a

    , unsolvedMetas :: MVar (HashSet (Meta a))
    , deferredEqns  :: MVar (HashMap (Meta a) (Seq (Constraint a)))

    , reporterFunction :: forall m. (MonadIO m, MonadReader (Env a) m) => String -> m ()

    , currentModule :: FilePath
    , currentlyChecking :: Maybe a
    }

emptyEnv :: (MonadIO m, Ord a, Hashable a) => FilePath -> m (Env a)
emptyEnv path = emptyEnvWithReporter path (liftIO . putStrLn)

emptyEnvWithReporter :: (MonadIO m, Ord a, Hashable a)
                     => FilePath
                     -> (forall m. (MonadIO m, MonadReader (Env a) m) => String -> m ())
                     -> m (Env a)
emptyEnvWithReporter path report = do
  unsolved <- liftIO (newMVar mempty)
  deferred <- liftIO (newMVar mempty)
  pure $ Env mempty mempty mempty mempty mempty mempty mempty unsolved deferred report path Nothing

report :: (MonadIO m, MonadReader (Env a) m) => String -> m ()
report s = ($ s) =<< asks reporterFunction

assume :: (MonadReader (Env a) m, Hashable a, Eq a) => a -> Value a -> m b -> m b
assume x t = local (\env -> env { assumptions = Map.insert x t (assumptions env), constructors = Set.delete x (constructors env) })

assuming :: (MonadReader (Env a) m, Hashable a, Eq a) => [(a, Value a)] -> m b -> m b
assuming vars = local (\env -> env { assumptions = Map.union (assumptions env) (Map.fromList vars)
                                   , constructors = Set.difference (constructors env) (Set.fromList (map fst vars))
                                   })

addSubmodule :: (MonadReader (Env a) m, Hashable a, Eq a) => a -> (Env a -> Env a) -> m b -> m b
addSubmodule name k =
  local (\env -> env { modules = Map.insert name (k env) { unsolvedMetas = unsolvedMetas env, deferredEqns = deferredEqns env } (modules env)})

envVariables :: Env a -> [a]
envVariables = Map.keys . assumptions

declare :: (MonadReader (Env a) m, Ord a, Hashable a) => a -> Value a -> Value a -> m b -> m b
declare x t val = local k where
  k env = env { assumptions = Map.insert x t (assumptions env)
              , declarations = Map.insert x val (declarations env)
              , constructors = Set.delete x (constructors env)
              }

insertDecl :: (Ord a, Hashable a) => a -> Value a -> Env a -> Env a
insertDecl x val env = env { declarations = (Map.insert x val (declarations env)) }

lookupType :: (MonadReader (Env k) m, Ord k, Hashable k) => k -> m (Maybe (Value k))
lookupType var = asks (Map.lookup var . assumptions)

lookupValue :: forall m var. (Fresh var, MonadReader (Env var) m, Ord var) => var -> m (Maybe (Value var))
lookupValue v = do
  t <- asks (Map.lookup v . declarations)
  case t of
    Just ty -> pure (Just ty)
    Nothing -> pure Nothing

withLocation :: (MonadReader (Env a) m) => L x -> (x -> m b) -> m b
withLocation (L thing range) cont =
  local (\x -> x { locationStack = range:locationStack x}) (cont thing)
