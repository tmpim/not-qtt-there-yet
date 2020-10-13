{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, QuantifiedConstraints #-}
module Presyntax where

import Check.Fresh

import Control.Comonad

import qualified Data.HashSet as HashSet
import qualified Data.Text as T
import Data.HashSet (HashSet)
import Data.Text (Text)
import Data.Hashable
import Data.L

import GHC.Generics (Generic)

import Qtt (Visibility(..))


data Expr f a
  = Var a
  | App Visibility (f (Expr f a)) (f (Expr f a))
  | Lam Visibility (f a) (f (Expr f a))
  | Pi  Visibility (f a) (f (Expr f a)) (f (Expr f a))
  | Cut (f (Expr f a)) (f (Expr f a))
  | Let a (f (Expr f a)) (f (Expr f a))
  | Set
  | Prop
  | Hole
  deriving Generic

exprFreeVars :: (Eq a, Hashable a, Foldable f, Comonad f) => Expr f a -> HashSet a
exprFreeVars (Var a) = HashSet.singleton a
exprFreeVars (App _ a b) = foldMap exprFreeVars a <> foldMap exprFreeVars b
exprFreeVars (Lam _ a b) = HashSet.delete (extract a) $ foldMap exprFreeVars b
exprFreeVars (Pi _ v a b) = foldMap exprFreeVars a <> HashSet.delete (extract v) (foldMap exprFreeVars b)
exprFreeVars (Let v a b) = foldMap exprFreeVars a <> HashSet.delete v (foldMap exprFreeVars b)
exprFreeVars (Cut a b) = foldMap exprFreeVars a <> foldMap exprFreeVars b
exprFreeVars Set = mempty
exprFreeVars Prop = mempty
exprFreeVars Hole = mempty

deriving instance (forall a. Hashable a => Hashable (f a), Hashable a) => Hashable (Expr f a)
deriving instance (forall a. Show a => Show (f a), Show a) => Show (Expr f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (Expr f a)

data Var
  = Intro Text
  | Refresh Text Int
  deriving (Eq, Ord, Generic, Hashable)

instance Fresh Var where
  fresh = Intro . T.pack <$> fresh

  refresh (Intro v) = Refresh v <$> fresh
  refresh (Refresh v x) = Refresh v . (x +) <$> fresh

  freshWithHint c = Refresh (T.pack c) <$> fresh

  derive s (Intro v) = Intro (v <> T.pack s)
  derive s (Refresh v x) = Refresh (v <> T.pack s) x

getVar :: Var -> Text
getVar (Intro x)       = x
getVar (Refresh t x)   = t <> T.singleton '$' <> T.pack (show x)

instance Show Var where
  show = T.unpack . getVar

type ExprL v = L (Expr L v)

data Decl f var
  = TypeSig var (f (Expr f var))
  | Value   var (f (Expr f var))
  | DataStmt    (DataDecl f var)

  | Include     (f Text)
  deriving (Generic)

data DataDecl f var
  = DataDecl { dataName         :: var
             , dataParams       :: [f (var, f (Expr f var))]
             , dataKind         :: f (Expr f var)
             , dataConstructors :: [f (var, f (Expr f var))]
             }
  deriving (Generic)

deriving instance (forall a. Hashable a => Hashable (f a), Hashable a) => Hashable (DataDecl f a)
deriving instance (forall a. Show a => Show (f a), Show a) => Show (DataDecl f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (DataDecl f a)

deriving instance (forall a. Hashable a => Hashable (f a), Hashable a) => Hashable (Decl f a)
deriving instance (forall a. Show a => Show (f a), Show a)             => Show (Decl f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a)                   => Eq (Decl f a)