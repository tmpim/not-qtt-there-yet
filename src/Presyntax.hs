{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, QuantifiedConstraints #-}
module Presyntax where

import Check.Fresh

import Data.Hashable
import Data.Range
import Data.Text (Text)
import qualified Data.Text as T

import Qtt (Visibility(..))
import GHC.Generics (Generic)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

data Expr f a
  = Var a
  | App Visibility (f (Expr f a)) (f (Expr f a))
  | Lam Visibility a (f (Expr f a))
  | Pi  Visibility a (f (Expr f a)) (f (Expr f a))
  | Cut (f (Expr f a)) (f (Expr f a))
  | Let a (f (Expr f a)) (f (Expr f a))
  | Set
  | Prop
  | Hole

exprFreeVars :: (Eq a, Hashable a, Foldable f) => Expr f a -> HashSet a
exprFreeVars (Var a) = HashSet.singleton a
exprFreeVars (App _ a b) = foldMap exprFreeVars a <> foldMap exprFreeVars b
exprFreeVars (Lam _ a b) = HashSet.delete a $ foldMap exprFreeVars b
exprFreeVars (Pi _ v a b) = foldMap exprFreeVars a <> HashSet.delete v (foldMap exprFreeVars b)
exprFreeVars (Let v a b) = foldMap exprFreeVars a <> HashSet.delete v (foldMap exprFreeVars b)
exprFreeVars (Cut a b) = foldMap exprFreeVars a <> foldMap exprFreeVars b
exprFreeVars Set = mempty
exprFreeVars Prop = mempty
exprFreeVars Hole = mempty

deriving instance (forall a. Show a => Show (f a), Show a) => Show (Expr f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (Expr f a)

data L a
  = L { lThing :: a
      , lRange :: Range }
  deriving (Eq, Ord, Functor, Foldable)

instance Show a => Show (L a) where
  show = show . lThing

data Var
  = Intro Text
  | Refresh Text Int
  | Qualified Var Var
  deriving (Eq, Ord, Generic, Hashable)

instance Fresh Var where
  fresh = Intro . T.pack <$> fresh

  refresh (Intro v) = Refresh v <$> fresh
  refresh (Refresh v x) = Refresh v . (x +) <$> fresh
  refresh (Qualified x y) = Qualified x <$> refresh y

  freshWithHint c = Refresh (T.pack c) <$> fresh

  derive s (Intro v) = Intro (v <> T.pack s)
  derive s (Refresh v x) = Refresh (v <> T.pack s) x
  derive s (Qualified x y) = Qualified x (derive s y)

getVar :: Var -> Text
getVar (Intro x)       = x
getVar (Refresh t x)   = t <> T.singleton '$' <> T.pack (show x)
getVar (Qualified x y) = getVar x <> T.singleton '.' <> getVar y

instance Show Var where
  show = T.unpack . getVar

type ExprL v = L (Expr L v)

data Decl f var
  = TypeSig var (f (Expr f var))
  | Value   var (f (Expr f var))
  | DataStmt    (DataDecl f var)

  | Include     (f Text)

data DataDecl f var
  = DataDecl { dataName         :: var
             , dataParams       :: [f (var, f (Expr f var))]
             , dataKind         :: f (Expr f var)
             , dataConstructors :: [f (var, f (Expr f var))]
             }

deriving instance (forall a. Show a => Show (f a), Show a) => Show (DataDecl f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (DataDecl f a)

deriving instance (forall a. Show a => Show (f a), Show a) => Show (Decl f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (Decl f a)