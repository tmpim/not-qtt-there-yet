{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
module Check.Fresh where

import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.IORef (newIORef, writeIORef, readIORef, IORef)
import System.IO.Unsafe (unsafePerformIO)
import Data.Hashable

class (Eq a, Ord a, Show a, Hashable a) => Fresh a where
  fresh :: MonadIO m => m a

  refresh :: MonadIO m => a -> m a
  refresh = const fresh

  freshWithHint :: MonadIO m => String -> m a
  freshWithHint = const fresh

  derive :: String -> a -> a
  derive _ = id

instance Fresh Int where
  {-# NOINLINE fresh #-}
  fresh = do
    x <- liftIO $ readIORef counter
    liftIO . writeIORef counter $! x + 1
    pure x

instance (a ~ Char) => Fresh [a] where
  fresh = fmap show (fresh @Int)
  refresh s = ((s ++) . show) <$> (fresh @Int)
  freshWithHint s = ((s ++) . show) <$> (fresh @Int)
  derive x n = n ++ x

{-# NOINLINE counter #-}
counter :: IORef Int
counter = unsafePerformIO $ newIORef 0