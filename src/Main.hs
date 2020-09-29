module Main where

import Text.Megaparsec (sourceColumn, unPos, SourcePos(sourceLine))

import Control.Monad.Reader

import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as T
import qualified Data.Text as T
import qualified Data.Set as Set

import Data.Range
import Data.Set (toList, Set)

import Presyntax.Parser
import Presyntax (Var(..))

import Qtt.Evaluate
import Qtt.Environment
import Qtt

import Check.Monad
import Check
import Control.Concurrent (takeMVar)
import Data.Foldable (for_)
import System.Exit (exitFailure)


main :: IO ()
main = do
  putStrLn "hello world"

  {-

  c <- asks unsolvedMetas
  set <- liftIO $ takeMVar c
  for (toList set) $ \m ->
    liftIO . putStrLn $ "Unsolved meta: " ++ show m

  t <- asks envVariables
  liftIO . putStrLn $ "Theorems: "
  for t $ \v -> do
    ~(Just t) <- lookupType v
    liftIO . putStrLn $ show v ++ " : " ++ show t
    -}

testFile :: String -> IO ()
testFile path = do
  env <- emptyEnv
  text <- T.readFile path
  prog <- parseFileIO path text
  x <- runChecker (checkProgram prog (asks id)) env
  let lines = T.lines text
  case x of
    Left (e, rs) -> do
      let r = head (filter (\r -> unPos (sourceColumn (rangeEnd r)) - unPos (sourceColumn (rangeStart r)) > 1) rs)
      print e
      printRange lines r
    Right (env, deferred) -> do
      for_ deferred print
      set <- takeMVar (unsolvedMetas env)
      for_ (toList set) $ \m -> do
        putStrLn $ "Error: Unsolved metavariable: " ++ show m
        printRange lines (metaLocation m)
        Right (ex, _) <- runChecker (zonk (metaExpected m)) env
        putStrLn $ "Note: it was expected to have type " ++ show ex
      unless (null set) exitFailure

      liftIO . putStrLn $ "Theorems: "
      for_ (Map.toList (assumptions env)) $ \(v, t) -> do
        Right (zonked, _) <- runChecker (zonk t) env
        putStrLn $ show v ++ " : " ++ show (prettify mempty zonked)

printRange :: [T.Text] -> Range -> IO ()
printRange lines r = do
  let l = unPos $ sourceLine (rangeStart r)
      padding = T.replicate (length (show l) + 1) (T.singleton ' ')
      line = T.cons ' ' (T.pack (show l)) <> T.pack " | "
      padded = padding <> T.pack " | "
  T.putStrLn padded
  T.putStrLn (line <> (lines !! (unPos (sourceLine (rangeStart r)) - 1)))
  T.putStrLn ( padded
            <> T.replicate (unPos (sourceColumn (rangeStart r)) - 1) (T.singleton ' ')
            <> T.replicate (unPos (sourceColumn (rangeEnd r)) - unPos (sourceColumn (rangeStart r))) (T.singleton '~')
             )

prettify :: Set T.Text -> Value Var -> Value Var
prettify scope (VFn arg cont) =
  case arg of
    Refresh var _ ->
      if var `Set.member` scope
        then VFn arg (prettify scope . cont)
        else VFn (Intro var) (prettify (Set.insert var scope) . cont)
    Intro var ->
      let new = findFresh var scope
       in if var `Set.member` scope
             then VFn (Intro new) (prettify (Set.insert new scope) . cont)
             else VFn (Intro var) (prettify (Set.insert var scope) . cont)
prettify scope (VPi arg vis domain range) =
  case arg of
    Refresh var _ ->
      if var `Set.member` scope
        then VPi arg         vis (prettify mempty domain) (prettify scope . range)
        else VPi (Intro var) vis (prettify mempty domain) (prettify (Set.insert var scope) . range)
    Intro var ->
      let new = findFresh var scope
       in if var `Set.member` scope
             then VPi (Intro new) vis (prettify mempty domain) (prettify (Set.insert new scope) . range)
             else VPi (Intro var) vis (prettify mempty domain) (prettify (Set.insert var scope) . range)
prettify _ x = x

findFresh :: T.Text -> Set T.Text -> T.Text
findFresh v s =
  if v `Set.member` s
    then findFresh (T.snoc v '\'') s
    else v