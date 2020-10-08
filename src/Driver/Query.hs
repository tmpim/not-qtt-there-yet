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
import Data.Sequence (Seq)
import Data.IORef
import Data.GADT.Show
import Qtt.Environment
import Data.HashSet (HashSet)

data Query var a where
  GoalFiles    :: Query var [FilePath]
  Persistent   :: Query var (IORef (PersistentState var))

  ModuleText   :: FilePath -> Query var [T.Text]
  ModuleCode   :: FilePath -> Query var [L (Decl L var)]
  ModuleMap    :: FilePath -> Query var (ModuleMap var)
  ModuleEnv    :: FilePath -> Query var (Env var)

  UnsolvedMetas :: Query var (HashSet (Meta var))

  Zonked        :: Value var -> Query var (Value var)

instance (Eq var, Hashable var) => Hashable (Query var a) where
  hashWithSalt salt = \case
    GoalFiles       -> hashWithSalt salt (negate 1 :: Int)
    Persistent      -> hashWithSalt salt (0 :: Int)
    ModuleText s    -> hashWithSalt (hashWithSalt salt (1 :: Int)) s
    ModuleCode s    -> hashWithSalt (hashWithSalt salt (2 :: Int)) s
    ModuleMap s     -> hashWithSalt (hashWithSalt salt (3 :: Int)) s
    ModuleEnv s     -> hashWithSalt (hashWithSalt salt (4 :: Int)) s
    UnsolvedMetas   -> hashWithSalt salt (5 :: Int)
    Zonked s        -> hashWithSalt (hashWithSalt salt (5 :: Int)) (quote s)

instance (Eq var, Hashable var) => Hashable (Some (Query var)) where
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
  PS { psUnsolved    :: MVar (HashSet (Meta a))
     , psDeferred    :: MVar (HashMap (Meta a) (Seq (Constraint a)))
     , psEliminators :: HashMap a (Value a, Value a)
     }

emptyPState :: (Ord a, Hashable a) => IO (PersistentState a)
emptyPState = PS <$> newMVar mempty <*> newMVar mempty <*> pure mempty

deriving instance (Show var, Eq var) => Show (Query var a)

instance (Show var, Eq var) => GShow (Query var) where
  gshowsPrec = showsPrec

instance Eq var => GEq (Query var) where
  geq GoalFiles GoalFiles = Just Refl
  geq Persistent Persistent = Just Refl
  geq UnsolvedMetas UnsolvedMetas = Just Refl
  geq (ModuleText a) (ModuleText b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq (ModuleCode a) (ModuleCode b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq (ModuleMap a) (ModuleMap b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq _ _ = Nothing