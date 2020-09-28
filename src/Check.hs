{-# LANGUAGE FlexibleContexts #-}
module Check where

import Control.Monad.IO.Class
import Control.Monad.Reader (MonadReader)
import Control.Monad.Except (throwError, MonadError)

import qualified Presyntax as P

import Qtt.Environment
import Qtt.Evaluate
import Qtt

import Check.TypeError ( TypeError(..) )
import Check.Subsumes ( subsumes )
import Check.Monad
import Check.Fresh
import Debug.Trace (traceShow)

check :: TypeCheck a m => P.Expr a -> Value a -> m (Term a)
check ex t | traceShow (ex, "checks", t) False = undefined
check P.Set value = do
  i <- isSet value
  pure (Set i)

check (P.Lam var body) term = do
  (dom, range) <- isPiType (Just var) term
  term <-
    assume var dom $
      check body (range (valueVar var))
  pure (Lam var term)

check (P.Pi var domain range) i = do
  i <- isSet i
  term <- check domain (VSet i)
  domain <- evaluate term
  assume var domain $ do
    range <- check range (VSet i)
    pure (Pi var term range)

check exp expected = do
  (term, ty) <- infer exp
  traceShow (ty, expected) $
    subsumes ty expected
  pure (Elim term)

infer :: TypeCheck a m
      => P.Expr a -> m (Elim a, Value a)
infer ex | traceShow (ex, "infers") False = undefined
infer (P.Var a) = do
  t <- lookupType a
  case t of
    Just ty ->
      traceShow ("inferred", Var a, ty)
      pure (Var a, ty)
    Nothing -> throwError (NotInScope a)
infer (P.App a b) = do
  (elimA, tyA) <- infer a
  (dom, range) <- isPiType Nothing tyA
  (termB) <- check b dom
  nfB <- evaluate termB
  pure (elimA `App` termB, range nfB)
infer (P.Cut a b) = do
  tyB <- check b (VSet 0)
  nfB <- evaluate tyB
  tA <- check a nfB
  pure (Cut tA tyB, nfB)
infer P.Hole = do
  ~(VNe tm) <- freshMeta
  t <- freshMeta
  pure (quoteNeutral tm, t)
infer e = do
  x <- freshMeta
  term <- check e x
  x <- zonk x
  pure (Cut term (quote x), x)

isPiType :: TypeCheck a m
         => Maybe a -> Value a -> m (Value a, Value a -> Value a)
isPiType _ (VPi _ a b) = pure (a, b)
isPiType hint t = do
  name <- case hint of
    Just t -> pure t
    Nothing -> fresh
  domain <- freshMeta
  assume name domain $ do
    range <- freshMeta
    subsumes t (VPi name domain (const range))
    pure (domain, const range)

isSet :: (Fresh a, MonadError (TypeError a) m, MonadIO m, MonadReader (Env a) m, Ord a, Show a)
      => Value a -> m Int
isSet (VSet i) = pure i
isSet t = throwError (NotSet t)
