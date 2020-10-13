{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Driver.Query where

import Control.Concurrent (newMVar, MVar)

import Data.HashMap.Strict (HashMap)
import qualified Data.Text as T
import Data.Constraint.Extras
import Data.HashSet (HashSet)
import Data.Sequence (Seq)
import Data.GADT.Compare
import Data.Constraint
import Data.GADT.Show
import Data.Hashable
import Data.IORef
import Data.Range
import Data.Some
import Data.L

import GHC.Generics (Generic)

import Presyntax

import Qtt.Environment
import Qtt.Builtin
import Qtt

import Type.Reflection
import Control.Monad.IO.Class


data Query var a where
  GoalFiles     :: Query var [FilePath]
  Persistent    :: Query var (IORef (PersistentState var))

  ModuleText    :: FilePath -> Query var [T.Text]
  ModuleCode    :: FilePath -> Query var [L (Decl L var)]
  ModuleMap     :: FilePath -> Query var (ModuleMap var)
  ModuleEnv     :: FilePath -> Query var (Env var)

  UnsolvedMetas :: Query var (MVar (HashSet (Meta var)))

  Zonked        :: Value var -> Query var (Value var)
  MakeBuiltin   :: Builtin var kit -> Query var kit
  ModuleAnnot   :: FilePath -> SourcePos -> Query var [Value var]

instance (Eq var, Hashable var) => Hashable (Query var a) where
  hashWithSalt salt = \case
    GoalFiles       -> hashWithSalt salt (negate 1 :: Int)
    Persistent      -> hashWithSalt salt (0 :: Int)
    ModuleText s    -> hashWithSalt (hashWithSalt salt (1 :: Int)) s
    ModuleCode s    -> hashWithSalt (hashWithSalt salt (2 :: Int)) s
    ModuleMap s     -> hashWithSalt (hashWithSalt salt (3 :: Int)) s
    ModuleEnv s     -> hashWithSalt (hashWithSalt salt (4 :: Int)) s
    UnsolvedMetas   -> hashWithSalt salt (5 :: Int)
    Zonked s        -> hashWithSalt (hashWithSalt salt (6 :: Int)) (quote s)
    MakeBuiltin s   -> hashWithSalt (hashWithSalt salt (7 :: Int)) s
    ModuleAnnot s r -> hashWithSalt (hashWithSalt (hashWithSalt salt (8 :: Int)) (newRangeUnchecked r r)) s

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
  deriving (Eq, Show, Generic, Hashable)

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
     , psDeferred    :: MVar (HashMap (Meta a) (Seq (Qtt.Constraint a)))
     , psEliminators :: HashMap a (Value a, Value a)
     , psReport      :: forall m. MonadIO m => String -> m ()
     }

emptyPState :: (Ord a, Hashable a) => IO (PersistentState a)
emptyPState = do
  mv <- newMVar mempty
  mv' <- newMVar mempty
  pure (PS mv mv' mempty (\_ -> pure ()))

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
  geq (Zonked a) (Zonked b)
    | a == b    = Just Refl
    | otherwise = Nothing
  geq (MakeBuiltin a) (MakeBuiltin b)
    | Just Refl <- geq a b = Just Refl
    | otherwise = Nothing
  geq _ _ = Nothing

instance ArgDict c (Query var) where
  type ConstraintsFor (Query var) c
    = (c [FilePath],
      c (IORef (PersistentState var)),
      c [T.Text],
      c [L (Decl L var)],
      c (ModuleMap var),
      c (Env var),
      c (MVar (HashSet (Meta var))),
      c (Value var),
      c [Value var],
      c (SimpleKit var))
  argDict = \case
    GoalFiles {}     -> Dict
    Persistent {}    -> Dict
    ModuleText {}    -> Dict
    ModuleCode {}    -> Dict
    ModuleMap {}     -> Dict
    ModuleEnv {}     -> Dict
    UnsolvedMetas {} -> Dict
    Zonked {}        -> Dict
    MakeBuiltin BuiltinFail -> Dict
    ModuleAnnot {}   -> Dict

instance Hashable (IORef a) where
  hashWithSalt s _ = s

instance Hashable (MVar a) where
  hashWithSalt s _ = s