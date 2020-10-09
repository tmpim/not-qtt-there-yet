{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Data.L where

import Data.Hashable
import Data.Range

import GHC.Generics (Generic)
import Control.Comonad

data L a
  = L { lThing :: a
      , lRange :: Range }
  deriving (Eq, Ord, Functor, Foldable, Traversable, Hashable, Generic)

instance Comonad L where
  extract = lThing
  duplicate (L x y) = L (L x y) y

instance Show a => Show (L a) where
  show = show . lThing