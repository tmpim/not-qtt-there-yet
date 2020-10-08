{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
module Qtt.Builtin where

import Data.GADT.Compare ( GEq(..) )
import Data.Dependent.HashMap
import Data.Hashable

import GHC.Generics (Generic)

import Qtt

import Type.Reflection ( (:~:)(Refl) )


data Builtin var kit where
  BuiltinFail :: Builtin var (SimpleKit var)

instance Show (Builtin var kit) where
  show BuiltinFail = "fail"

instance GEq (Builtin var) where
  geq BuiltinFail BuiltinFail = Just Refl

instance Hashable (Builtin var kit) where
  hashWithSalt s BuiltinFail = hashWithSalt s (1 :: Int)

instance Hashable (Some (Builtin var)) where
  hashWithSalt s (Some x) = hashWithSalt s x

data SimpleKit var
  = SimpleKit { builtinName  :: var 
              , builtinType  :: Value var
              , builtinValue :: Value var
              }
  deriving (Generic, Hashable)