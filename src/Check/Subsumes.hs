{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
module Check.Subsumes where

import Control.Monad.IO.Class

import qualified Data.Set as Set
import Data.Set (Set)

import Check.TypeError
import Check.Monad

import Qtt.Environment
import Qtt.Evaluate
import Qtt

import Control.Concurrent
import qualified Data.Sequence as Seq
import Data.Foldable (for_)

import Check.Fresh
import Control.Monad (zipWithM_)
import Control.Monad.Except (throwError, MonadError(catchError))
import Control.Monad.Reader (asks)

import Data.Sequence (Seq)
import Data.Foldable (Foldable(toList))

subsumes :: TypeCheck a m => Value a -> Value a -> m ()
-- subsumes a b | trace (show a ++ " ≤? " ++ show b) False = undefined
subsumes (VNe (NApp (NMeta m) spine)) term = solve m spine term
subsumes term (VNe (NApp (NMeta m) spine)) = solve m spine term
subsumes (VNe a) (VNe b) = subsumesNe a b
subsumes (VPi _ vis domain range) (VPi _ vis' domain' range') | vis == vis' = do
  v <- freshWithHint "$pi"
  subsumes domain' domain
  subsumes (range (valueVar v)) (range' (valueVar v))
subsumes (VFn a b) t = subsumes (b (valueVar a)) (t @@ valueVar a)
subsumes t (VFn a b) = subsumes (t @@ valueVar a) (b (valueVar a))
subsumes (VSet i) (VSet j)
  | i <= j = pure ()
subsumes a b = do
  a <- zonk a
  b <- zonk b
  typeError (NotEqual a b)

subsumesNe :: TypeCheck a m => Neutral a -> Neutral a -> m ()
subsumesNe (NVar a) (NVar b)
  | a == b = pure ()
  | otherwise = typeError (NotEqual (valueVar a) (valueVar b))
subsumesNe (NApp (NVar h) b) (NApp (NVar h') b') | h == h' = do
  zipWithM_ subsumes (toList b) (toList b')

subsumesNe (NApp (NMeta m) spine) term = solve m spine (VNe term)

subsumesNe (NMeta m) term = solve m mempty (VNe term)

subsumesNe term (NApp (NMeta m) spine) = solve m spine (VNe term)

subsumesNe term (NMeta m) = solve m mempty (VNe term)

subsumesNe a b = do
  a <- zonk (VNe a)
  b <- zonk (VNe b)
  typeError (NotEqual a b)

solve :: TypeCheck a m => Meta a -> Seq (Value a) -> Value a -> m ()
solve meta@MV{..} spine val
  | Just MV{..} <- metaHeaded val = do
      liftIO . modifyMVar_ metaBlockedEqns $ \queue ->
        pure (queue Seq.:|> Equation meta spine val)
  | Just vars <- isPattern spine =
      do
        val <- quote <$> zonk val
        top <- asks toplevel
        checkScope (top <> vars) val
        fakeLam <- evaluate $ foldr (\(VNe (NVar v)) b -> Lam v b) val spine
        x <- liftIO $ tryReadMVar metaSlot
        case x of
          Nothing -> do
            solveMeta meta
            liftIO . putStrLn $ "Solving " ++ show meta ++ " := " ++ show (fakeLam)
            liftIO $ putMVar metaSlot (quote fakeLam)
            t <- liftIO $ swapMVar metaBlockedEqns mempty
            for_ t $ \(Equation meta spine val) -> do
              solve meta spine val
          Just t -> do
            tv <- evaluate t
            subsumes (foldl (@@) tv spine) =<< evaluate (quote (foldl (@@) fakeLam spine))
      `catchError` \(_, r) -> do
        m <- zonk (VNe (NMeta meta))
        throwError ((NotEqual m val), r)
  | otherwise = defer meta spine val

metaHeaded :: Value a -> Maybe (Meta a)
metaHeaded (VNe (NApp (NMeta m) _)) = Just m
metaHeaded (VNe (NMeta m)) = Just m
metaHeaded _ = Nothing

checkScope :: TypeCheck a m => Set a -> Term a -> m ()
checkScope set (Elim a) = go a where
  go (Var v)
    | v `Set.member` set = pure ()
    | otherwise = typeError (NotInScope v)
  go (App a b) = do
    go a
    checkScope set b
  go (Cut a b) = do
    checkScope set a
    checkScope set b
  go Meta{} = pure ()
checkScope set (Pi var _vis domain range) = do
  checkScope set domain
  checkScope (Set.insert var set) range
checkScope set (Lam var body) = checkScope (Set.insert var set) body
checkScope _ Set{} = pure ()

isPattern :: Ord a => Seq (Value a) -> Maybe (Set a)
isPattern = go mempty where
  go x (VNe (NVar v) Seq.:<| rest)
    | v `Set.member` x = Nothing
    | otherwise = go (Set.insert v x) rest
  go _ (_ Seq.:<| _) = Nothing
  go x Seq.Empty = Just x
