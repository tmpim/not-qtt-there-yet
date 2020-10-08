{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Qtt.Environment
  ( Env(..), emptyEnv, emptyEnvWithReporter
  , assume, assuming, envVariables
  , declare, insertDecl
  , lookupType
  , lookupValue
  , withLocation
  
  , report
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
import Data.Sequence
import qualified Data.Set as Set

data Env a =
  Env
    { assumptions   :: Map a (Value a)
    , declarations  :: Map a (Value a)
    , locationStack :: [Range]
    , unproven      :: Map a (L ())
    , toplevel      :: Set a
    , constructors  :: Set a

    , unsolvedMetas :: MVar (Set (Meta a))
    , deferredEqns  :: MVar (Map (Meta a) (Seq (Constraint a)))

    , reporterFunction :: forall m. (MonadIO m, MonadReader (Env a) m) => String -> m ()

    , currentModule :: FilePath
    , currentlyChecking :: Maybe a
    }

emptyEnv :: (MonadIO m, Ord a) => FilePath -> m (Env a)
emptyEnv path = emptyEnvWithReporter path (liftIO . putStrLn)

emptyEnvWithReporter :: (MonadIO m, Ord a)
                     => FilePath
                     -> (forall m. (MonadIO m, MonadReader (Env a) m) => String -> m ())
                     -> m (Env a)
emptyEnvWithReporter path report = do
  unsolved <- liftIO (newMVar mempty)
  deferred <- liftIO (newMVar mempty)
  pure $ Env mempty mempty mempty mempty mempty mempty unsolved deferred report path Nothing

report :: (MonadIO m, MonadReader (Env a) m) => String -> m ()
report s = ($ s) =<< asks reporterFunction

assume :: (MonadReader (Env a) m, Ord a) => a -> Value a -> m b -> m b
assume x t = local (\env -> env { assumptions = Map.insert x t (assumptions env), constructors = Set.delete x (constructors env) })

assuming :: (MonadReader (Env a) m, Ord a) => [(a, Value a)] -> m b -> m b
assuming vars = local (\env -> env { assumptions = Map.union (assumptions env) (Map.fromList vars)
                                   , constructors = Set.difference (constructors env) (Set.fromList (map fst vars))
                                   })

envVariables :: Env a -> [a]
envVariables = Map.keys . assumptions

declare :: (MonadReader (Env a) m, Ord a) => a -> Value a -> Value a -> m b -> m b
declare x t val = local k where
  k env = env { assumptions = Map.insert x t (assumptions env)
              , declarations = Map.insert x val (declarations env)
              , constructors = Set.delete x (constructors env)
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
