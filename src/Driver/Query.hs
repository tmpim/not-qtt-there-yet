{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Driver.Query where

import qualified Data.Text as T
import Data.GADT.Compare
import Data.Hashable
import Data.Some

import Presyntax

import Qtt
import Type.Reflection

import Data.HashMap.Strict (HashMap)
import Control.Concurrent (newMVar, MVar)
import Data.Set (Set)
import Data.Map.Strict (Map)
import Data.Sequence (Seq)
import Data.IORef
import Data.GADT.Show

data Query var a where
  GoalFiles    :: Query var [FilePath]
  Persistent   :: Query var (IORef (PersistentState var))

  ModuleText   :: FilePath -> Query var [T.Text]
  ModuleCode   :: FilePath -> Query var [L (Decl L var)]
  ModuleMap    :: FilePath -> Query var (ModuleMap var)

  Signature    :: FilePath -> var -> Query var (Maybe (ExprL var))
  Declaration  :: FilePath -> var -> Query var (ExprL var)
  DataInfo     :: FilePath -> var -> Query var (DataInfo var)

  VariableIdentity :: FilePath -> var -> Query var (Maybe (Value var, Value var))
  VariableType     :: FilePath -> var -> Query var (Maybe (Value var))
  VariableValue    :: FilePath -> var -> Query var (Maybe (Value var))

  Constructors :: FilePath -> Query var (Set var)

instance Hashable var => Hashable (Query var a) where
  hashWithSalt salt = \case
    GoalFiles       -> hashWithSalt salt (negate 1 :: Int)
    Persistent      -> hashWithSalt salt (0 :: Int)
    ModuleText s    -> hashWithSalt (hashWithSalt salt (1 :: Int)) s
    ModuleCode s    -> hashWithSalt (hashWithSalt salt (2 :: Int)) s
    ModuleMap s     -> hashWithSalt (hashWithSalt salt (3 :: Int)) s
    Signature p s   ->
      hashWithSalt (hashWithSalt (hashWithSalt salt (4 :: Int)) s) p
    Declaration p s ->
      hashWithSalt (hashWithSalt (hashWithSalt salt (5 :: Int)) s) p
    VariableType p s ->
      hashWithSalt (hashWithSalt (hashWithSalt salt (6 :: Int)) s) p
    DataInfo p s ->
      hashWithSalt (hashWithSalt (hashWithSalt salt (7 :: Int)) s) p
    VariableValue p s ->
      hashWithSalt (hashWithSalt (hashWithSalt salt (8 :: Int)) s) p
    VariableIdentity p s ->
      hashWithSalt (hashWithSalt (hashWithSalt salt (9 :: Int)) s) p
    Constructors p -> hashWithSalt (hashWithSalt salt (10 :: Int)) p

instance Hashable var => Hashable (Some (Query var)) where
  hashWithSalt salt (Some x) = hashWithSalt salt x

-- | A module map is a mapping from Variables to pre-checked structures.
data ModuleMap var =
  MM { moduleTySigs  :: HashMap var (ExprL var)
     , moduleDecls   :: HashMap var (ExprL var)
     , moduleData    :: HashMap var (DataDecl L var)
       -- ^ Maps X → data X
     , moduleCons    :: HashMap var (DataDecl L var)
       -- ^ Maps c : ... → X => data X
     , moduleImports :: HashMap var (ModuleMap var)
     }
  deriving (Eq, Show)

data DataInfo var =
  DI { diName :: var
     , diSort :: Value var -- ^ Closed
     , diCons :: [(var, Value var, Value var)] -- ^ Closed, normalised
     , diElim :: var
     , diElimSort :: Value var -- ^ Closed
     , diElimImpl :: Value var -- ^ Meta-level
     }
  deriving (Eq, Show)

data PersistentState a =
  PS { psUnsolved    :: MVar (Set (Meta a))
     , psDeferred    :: MVar (Map (Meta a) (Seq (Constraint a)))
     , psEliminators :: HashMap a (Value a, Value a)
     }

emptyPState :: (Ord a, Hashable a) => IO (PersistentState a)
emptyPState = PS <$> newMVar mempty <*> newMVar mempty <*> pure mempty

deriving instance Show var => Show (Query var a)

instance Show var => GShow (Query var) where
  gshowsPrec = showsPrec

instance Eq var => GEq (Query var) where
  geq GoalFiles GoalFiles = Just Refl
  geq Persistent Persistent = Just Refl
  geq (ModuleText a) (ModuleText b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq (ModuleCode a) (ModuleCode b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq (ModuleMap a) (ModuleMap b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq (Signature p a) (Signature p' b)
    | p == p', a == b = Just Refl
    | otherwise = Nothing
  geq (Declaration p a) (Declaration p' b)
    | p == p', a == b = Just Refl
    | otherwise = Nothing
  geq (VariableType p a) (VariableType p' b)
    | p == p', a == b = Just Refl
    | otherwise = Nothing
  geq (VariableValue p a) (VariableValue p' b)
    | p == p', a == b = Just Refl
    | otherwise = Nothing
  geq (VariableIdentity p a) (VariableIdentity p' b)
    | p == p', a == b = Just Refl
    | otherwise = Nothing
  geq (DataInfo p a) (DataInfo p' b)
    | p == p', a == b = Just Refl
    | otherwise = Nothing
  geq (Constructors p) (Constructors p')
    | p == p' = Just Refl
    | otherwise = Nothing
  geq _ _ = Nothing