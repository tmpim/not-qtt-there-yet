{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Presyntax where

import Check.Fresh

data Expr a
  = Var a
  | App (Expr a) (Expr a)
  | Lam a (Expr a)
  | Cut (Expr a) (Expr a)
  | Pi a (Expr a) (Expr a)
  | Set
  | Hole
  deriving (Eq, Show, Ord)

newtype Var = MkVar { getVar :: String }
  deriving (Eq, Ord)

instance Fresh Var where
  fresh = MkVar <$> fresh
  refresh = fmap MkVar . refresh . getVar
  freshWithHint = fmap MkVar . freshWithHint

instance Show Var where
  show = getVar

identity :: Expr Var
identity = Lam (MkVar "A") (Lam (MkVar "a") (Var (MkVar "a")))