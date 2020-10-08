module Control.Concurrent.IO
  ( putStrLn
  , putStr
  , print
  ) where

import Control.Concurrent

import qualified Prelude
import Prelude hiding (putStrLn, putStr, print)
import System.IO.Unsafe (unsafePerformIO)

putStrLn :: String -> IO ()
putStrLn s = do
  modifyMVar_ stdoutLock $ \() ->
    Prelude.putStrLn s

putStr :: String -> IO ()
putStr s = do
  modifyMVar_ stdoutLock $ \() ->
    Prelude.putStrLn s

print :: Show a => a -> IO ()
print s = do
  modifyMVar_ stdoutLock $ \() ->
    Prelude.print s

{-# NOINLINE stdoutLock #-}
stdoutLock :: MVar ()
stdoutLock = unsafePerformIO (newMVar ())
