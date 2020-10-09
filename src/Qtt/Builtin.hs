{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
module Qtt.Builtin where

import Data.GADT.Compare ( GEq(..) )
import Type.Reflection ( (:~:)(Refl) )

import Qtt
import Data.Hashable
import Data.Dependent.HashMap

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