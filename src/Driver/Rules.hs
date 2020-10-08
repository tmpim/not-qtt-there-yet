{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Driver.Rules where

import Control.Monad.IO.Class
import Driver.Query

import qualified Rock

import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text.IO as T
import qualified Data.Text as T

import Presyntax.Parser (parseFileIO)
import Presyntax
import Check.Monad
import Qtt.Environment
import Check
import Qtt
import Control.Applicative
import Data.Range
import Presyntax.Lexer
import Data.IORef
import Control.Exception (throwIO)
import qualified Data.Map.Strict as Map
import qualified Data.HashSet as HashSet
import Control.Monad.Reader (MonadReader(local))
import Data.HashSet (HashSet)
import qualified Data.Set as Set
import Data.Foldable
import Check.TypeError


rules :: IORef (PersistentState Var) -> [String] -> Rock.Rules (Query Var)
rules persistent files = \case
  GoalFiles -> pure files
  Persistent -> pure persistent

  ModuleText file -> do
    contents <- liftIO $ T.readFile file
    pure (T.lines contents)

  ModuleCode file -> do
    lines <- T.unlines <$> Rock.fetch (ModuleText file)
    t <- liftIO (parseFileIO file lines)
    pure t

  ModuleMap path -> do
    code <- Rock.fetch (ModuleCode path)
    pure (foldr addDefToMM (MM mempty mempty mempty mempty mempty) code)

  Signature path var -> do
    mmap <- Rock.fetch (ModuleMap path)
    case var `HashMap.lookup` moduleTySigs mmap of
      Just sig -> pure (Just sig)
      Nothing -> pure Nothing

  Declaration path var -> do
    mmap <- Rock.fetch (ModuleMap path)
    case var `HashMap.lookup` moduleDecls mmap of
      Just sig -> pure sig
      Nothing -> error $ "No declaration for " ++ show var ++ " in module map"

  DataInfo path dataName -> do
    mmap <- Rock.fetch (ModuleMap path)
    case dataName `HashMap.lookup` moduleData mmap of
      Just dec -> do
        c <- runCheckerOrFail (checkDataDecl dec) =<< emptyEnv path
        let ((name, sort), cons, (elim, elimT, elimV)) = c
        liftIO $ do
          modifyIORef' persistent $ \st -> st{ psEliminators = HashMap.insert elim (elimT, elimV) (psEliminators st) }
          pure $ DI name sort cons elim elimT elimV
      Nothing -> liftIO $ throwIO (Tee (NotInScope dataName))

  VariableIdentity path var -> do
    hasSig <- Rock.fetch (Signature path var)
    -- Try, in order:
    case hasSig of
      -- A declaration with a signature...
      Just t -> fmap Just $ do
        -- if we have a signature, we also need a declaration
        dec <- Rock.fetch (Declaration path var)
        let fv = exprFreeVars (lThing dec) <> exprFreeVars (lThing t)

        values <- valueClosure path (HashSet.toList fv) mempty

        let comp = do
            local (\e -> e { declarations = Map.union (foldMap id values) (declarations e) }) $ do
              t <- checkLoc t VSet
              ty_nf <- evaluate t
              body <- checkLoc dec ty_nf
              body_nf <- evaluate body
              pure (ty_nf, body_nf)
        runCheckerOrFail comp =<< emptyEnv path
      Nothing -> do
        mmap <- Rock.fetch (ModuleMap path)
        -- Either a constructor or a data type...
        case HashMap.lookup var (moduleCons mmap) <|> HashMap.lookup var (moduleData mmap) of
          Just d -> do
            di <- Rock.fetch (DataInfo path (dataName d))
            if | var == diName di -> pure (Just (diSort di, VNe (NCon (dataName d))))
               | Just x <- findCon var (diCons di) -> pure (Just x)
               | otherwise ->
                 error $ "Impossible: " ++ show var ++ " is associated with " ++ show (dataName d) ++ " but is neither type nor constructor"
          -- or an eliminator.
          Nothing -> do
            -- TODO: HACK HACK HACK HACK HACK HACK JESUS CHRIST
            let datan = T.takeWhile (/= '.') (getVar var)
            _ <- Rock.fetch (DataInfo path (Intro datan))

            ps <- liftIO . fmap psEliminators . readIORef $ persistent
            case HashMap.lookup var ps of
              Just (v, x) -> pure (pure (v, x))
              Nothing -> pure Nothing

  VariableType p v -> fmap fst <$> Rock.fetch (VariableIdentity p v)
  VariableValue p v -> fmap snd <$> Rock.fetch (VariableIdentity p v)

  Constructors p -> do
    mmap <- Rock.fetch (ModuleMap p)
    let datacons = Set.fromList . HashSet.toList . HashMap.keysSet . moduleCons $ mmap
        typecons = Set.fromList . HashSet.toList . HashMap.keysSet . moduleData $ mmap
    pure (datacons <> typecons)

valueClosure :: FilePath -> [Var] -> HashSet Var -> Rock.Task (Query Var) (HashSet Var, Map.Map Var (Value Var))
valueClosure path fv seen =
  flip foldMapM fv $ \v -> do
    if v `HashSet.member` seen
      then pure (seen, mempty)
      else do
        t <- Rock.fetch (VariableValue path v)
        case t of
          Just val -> do
            (seen, vs) <- valueClosure path (HashSet.toList (nonLocalVars (quote val))) (HashSet.insert v seen)
            pure (seen, Map.insert v val vs)
          Nothing -> pure (seen, mempty)

checkFile :: FilePath -> Rock.Task (Query Var) ()
checkFile path = do
  mmap <- Rock.fetch (ModuleMap path)
  for_ (HashMap.toList (moduleTySigs mmap)) $ \(n, _) -> do
    Rock.fetch (VariableIdentity path n)

  for_ (HashMap.toList (moduleDecls mmap)) $ \(n, _) -> do
    Rock.fetch (VariableIdentity path n)

  for_ (HashMap.toList (moduleData mmap)) $ \(n, _) -> do
    Rock.fetch (DataInfo path n)

foldMapM :: (Applicative f, Monoid m, Foldable t) => (a -> f m) -> t a -> f m
foldMapM k = foldr (\a b -> (<>) <$> k a <*> b) (pure mempty)

findCon :: Var -> [(Var, Value Var, Value Var)] -> Maybe (Value Var, Value Var)
findCon _ [] = Nothing
findCon c ((c',v,v'):s)
  | c == c' = pure (v, v')
  | otherwise = findCon c s

runCheckerOrFail :: TCM Var a -> Env Var -> Rock.Task (Query Var) a
runCheckerOrFail c env = do
  pvar <- Rock.fetch Persistent
  cons <- Rock.fetch (Constructors (currentModule env))
  p <- liftIO $ readIORef pvar
  e <- runChecker c env{ unsolvedMetas = psUnsolved p, deferredEqns = psDeferred p, constructors = cons }
  case e of
    Left (err, span) -> liftIO $ throwIO (Teer err span)
    Right x -> do
      pure x

addDefToMM :: L (Decl L Var) -> ModuleMap Var -> ModuleMap Var
addDefToMM (L (TypeSig v t) _) x =
  x { moduleTySigs = HashMap.insert v t (moduleTySigs x) }
addDefToMM (L (Value v t) _) x =
  x { moduleDecls = HashMap.insert v t (moduleDecls x) }
addDefToMM (L (DataStmt t) _) x =
  x { moduleData = HashMap.insert (dataName t) t (moduleData x)
    , moduleCons = HashMap.union (HashMap.fromList cons) (moduleCons x) }
  where
    cons = map (\(L (v, _) _) -> (v, t)) (dataConstructors t)

printRange :: [T.Text] -> Range -> IO T.Text
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
  pure (padding)