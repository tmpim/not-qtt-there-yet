{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, QuantifiedConstraints #-}
module Presyntax where

import Check.Fresh

import Data.Range
import Data.Text (Text)
import qualified Data.Text as T

import Qtt (Visibility(..))

data Expr f a
  = Var a
  | App Visibility (f (Expr f a)) (f (Expr f a))
  | Lam Visibility a (f (Expr f a))
  | Pi  Visibility a (f (Expr f a)) (f (Expr f a))
  | Cut (f (Expr f a)) (f (Expr f a))
  | Let a (f (Expr f a)) (f (Expr f a))
  | Set Int
  | Prop
  | Hole

deriving instance (forall a. Show a => Show (f a), Show a) => Show (Expr f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (Expr f a)

data L a
  = L { lThing :: a
      , lRange :: Range }
  deriving (Eq, Ord)

instance Show a => Show (L a) where
  show = show . lThing

data Var = Intro Text | Refresh Text Int
  deriving (Eq, Ord)

instance Fresh Var where
  fresh = Intro . T.pack <$> fresh

  refresh (Intro v) = Refresh v <$> fresh
  refresh (Refresh v x) = Refresh v . (x +) <$> fresh

  freshWithHint c = Refresh (T.pack c) <$> fresh

  derive s (Intro v) = Intro (v <> T.pack s)
  derive s (Refresh v x) = Refresh (v <> T.pack s) x

getVar :: Var -> Text
getVar (Intro x) = x
getVar (Refresh t x) = t <> T.singleton '$' <> T.pack (show x)

instance Show Var where
  show = T.unpack . getVar

type ExprL v = L (Expr L v)

data Decl f var
  = TypeSig var (f (Expr f var))
  | Value   var (f (Expr f var))
  | DataDecl { dataName         :: var
             , dataParams       :: [f (var, f (Expr f var))]
             , dataKind         :: f (Expr f var)
             , dataConstructors :: [f (var, f (Expr f var))]
             }

deriving instance (forall a. Show a => Show (f a), Show a) => Show (Decl f a)
deriving instance (forall a. Eq a => Eq (f a), Eq a) => Eq (Decl f a)