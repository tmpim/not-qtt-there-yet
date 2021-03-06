{-# LANGUAGE NamedFieldPuns #-}
module Qtt.Pretty where

import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Set

import Presyntax (Var(..))

import Qtt


prettify :: Set T.Text -> Value Var -> Value Var
prettify scope (VFn Binder{var=arg,visibility,domain} cont) =
  case cont (valueVar arg) of
    VNe (NApp f spine) | Just s <- etaReduceMaybe f spine arg -> VNe s
    _ -> VFn (Binder arg' visibility (prettify scope domain)) (prettify scope' . cont)
  where
    (scope', var) = refreshFromScope scope (varText arg)
    arg' = Intro var
prettify scope (VPi (Binder arg vis domain) range) =
  let (scope', var) = refreshFromScope scope (varText arg)
   in VPi (Binder (Intro var) vis (prettify scope domain)) (prettify scope' . range)
prettify scope val@(VNe n) =
  case n of
    NApp f sp -> VNe $ NApp f (prettify scope <$> sp)
    _ -> val
prettify _ x = x

refreshFromScope :: Set T.Text -> T.Text -> (Set T.Text, T.Text)
refreshFromScope s t = (Set.insert t s, findFresh t s)

findFresh :: T.Text -> Set T.Text -> T.Text
findFresh v s =
  if v `Set.member` s
    then findFresh (T.snoc v '\'') s
    else v

varText :: Var -> T.Text
varText (Intro v) = v
varText (Refresh v _) = v