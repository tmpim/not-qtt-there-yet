{-# LANGUAGE GADTs #-}
module Driver.WiredIn where

import Driver.Query

import Rock

import Qtt.Builtin
import Check.Fresh
import Qtt

makeBuiltin :: Fresh var => Builtin var a -> Task (Query var) a
makeBuiltin BuiltinFail = do
  name <- freshWithHint "fail"
  let builtinTy  = VPi (Binder name Visible VSet) id
  let builtinVal = valueVar name
  pure (SimpleKit name builtinTy builtinVal)