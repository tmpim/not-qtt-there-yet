{-# LANGUAGE GADTs #-}
module Driver.WiredIn where

import Check.Fresh

import Driver.Query

import Qtt.Builtin
import Qtt

import Rock


makeBuiltin :: Fresh var => Builtin var a -> Task (Query var) a
makeBuiltin BuiltinFail = do
  name <- freshWithHint "fail"
  let builtinTy  = VPi (Binder name Visible VSet) id
  let builtinVal = valueVar name
  pure (SimpleKit name builtinTy builtinVal)